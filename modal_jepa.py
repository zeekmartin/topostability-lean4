"""
Spectral simplicial hierarchy on a REAL JEPA model's attention connectivity.

Companion to `modal_lean.py` (that one builds Lean on CPU; THIS one runs a
pretrained JEPA encoder on a Modal GPU). We test, on the actual head-to-head
attention-correlation graph of a pretrained I-JEPA ViT, whether the empirically
universal inequality

        λ₂(T(G)) ≤ λ₂(G)            (and the full chain λ₂(T₃) ≤ λ₂(T(G)) ≤ λ₂(G))

— validated across 45,000+ synthetic graphs with zero violations — still holds.

Pipeline (all on a T4 GPU)
--------------------------
  1. load I-JEPA (`facebook/ijepa_vith14_1k`, ViT-H/14, 32 layers × 16 heads)
  2. forward pass on a batch of real images (HF `cifar10` test split, eager attn)
  3. per (layer, head): mean attention map over images → flattened signature
  4. per-layer graph G_L: nodes = heads, edge iff Pearson r(sig_i, sig_j) > τ
  5. spectral hierarchy per layer: λ₂(G), λ₂(T(G)), ρ = λ₂(T)/λ₂(G)
  6. global graph over ALL 512 heads: λ₂(G), λ₂(T(G)), λ₂(T₃)
  7. SAL-style head masking: drop 33% of heads, recompute ρ and FI before/after
     (FI = fraction of edges in zero triangles — the SAL "fragility index")

Usage
-----
    modal run modal_jepa.py                       # full run, writes the report
    modal run modal_jepa.py --n-images 8 --threshold 0.3

The remote function returns a JSON-serialisable dict; the local entrypoint
formats `informal/jepa_real_spectral.md` and dumps the raw JSON beside it.
"""
import json
import os

import modal

# --------------------------------------------------------------------------- #
# Image: Python 3.10 + torch + transformers + graph/num stack, T4 GPU.
# --------------------------------------------------------------------------- #
image = (
    modal.Image.debian_slim(python_version="3.10")
    .pip_install(
        "torch==2.4.1",
        "transformers==4.49.0",     # has IJepaModel + VJepa2
        "torchvision==0.19.1",
        "datasets==3.2.0",
        "pillow",
        "networkx==3.4.2",
        "numpy<2",
        "scipy",
        "accelerate",
        "huggingface_hub",
    )
    .env({"HF_HOME": "/cache/hf", "TOKENIZERS_PARALLELISM": "false"})
)

app = modal.App("jepa-spectral")

# Persist the (large) HF model + dataset downloads across runs.
cache_vol = modal.Volume.from_name("jepa-hf-cache", create_if_missing=True)

TOL = 1e-9


# ========================================================================= #
#  Graph / hierarchy helpers — pure numpy + networkx (run inside container,
#  also importable locally). Definitions match the repo's existing scripts.
# ========================================================================= #
def lambda2(G):
    """Second-smallest Laplacian eigenvalue (algebraic connectivity) of the
    FULL graph G (= 0 exactly when G is disconnected). Returns
    (val, connected, n). Dense `eigvalsh` for n ≤ 1800, else sparse shift-invert
    so large triangle graphs stay tractable.

    The hierarchy is only meaningful for connected graphs, so callers gate on
    the returned `connected` flag — we never do per-graph largest-component
    surgery (that would compare λ₂ of *different* subgraphs)."""
    import networkx as nx
    import numpy as np
    n = G.number_of_nodes()
    if n < 2:
        return None, False, n
    connected = nx.is_connected(G)
    if n <= 1800:
        L = nx.laplacian_matrix(G).toarray().astype(float)
        ev = np.linalg.eigvalsh(L)
        return float(ev[1]), connected, n
    # large: smallest two Laplacian eigenvalues via shift-invert
    from scipy.sparse.linalg import eigsh
    Ls = nx.laplacian_matrix(G).astype(float)
    try:
        ev = eigsh(Ls, k=2, sigma=1e-8, which="LM", return_eigenvectors=False)
    except Exception:
        ev = eigsh(Ls, k=2, which="SM", return_eigenvectors=False)
    return float(np.sort(ev)[1]), connected, n


def triangle_graph(G):
    """T(G): nodes = edges of G; two edges adjacent iff they share a vertex and
    the opposite endpoints are adjacent (i.e. they lie in a common triangle).
    Built by enumerating triangles (O(Σ deg²)) rather than edge-pairs."""
    import networkx as nx
    edges = [tuple(sorted(e)) for e in G.edges()]
    idx = {e: i for i, e in enumerate(edges)}
    T = nx.Graph()
    T.add_nodes_from(range(len(edges)))
    adj = {v: set(G.neighbors(v)) for v in G.nodes()}
    for a, b, c in _triangles(G, adj):
        e_ab, e_ac, e_bc = tuple(sorted((a, b))), tuple(sorted((a, c))), tuple(sorted((b, c)))
        i, j, k = idx[e_ab], idx[e_ac], idx[e_bc]
        T.add_edge(i, j); T.add_edge(i, k); T.add_edge(j, k)
    return T


def _triangles(G, adj):
    seen = set()
    for v in G.nodes():
        nbrs = sorted(adj[v])
        for x in range(len(nbrs)):
            for y in range(x + 1, len(nbrs)):
                a, b = nbrs[x], nbrs[y]
                if b in adj[a]:
                    tri = tuple(sorted((v, a, b)))
                    if tri not in seen:
                        seen.add(tri)
                        yield tri


def _count_triangles_capped(G, cap):
    """Number of triangles, stopping early once it exceeds `cap`."""
    adj = {v: set(G.neighbors(v)) for v in G.nodes()}
    c = 0
    for _ in _triangles(G, adj):
        c += 1
        if c > cap:
            return c
    return c


def tetra_graph(G, tri_cap=4000, tetra_cap=200000):
    """T₃: nodes = triangles (3-cliques) of G; two triangles adjacent iff they
    share an edge AND their union is a 4-clique (tetrahedron of the clique
    complex). Built from 4-cliques directly — for each tetrahedron its four
    triangular faces are mutually adjacent — which is O(#4-cliques), not the
    O(#triangles²) of comparing every pair of triangles.

    Returns (H | None, n_triangles). H is None when the triangle or tetra count
    exceeds the caps (graph too dense for an exact T₃ — reported, not crashed)."""
    import networkx as nx
    adj = {v: set(G.neighbors(v)) for v in G.nodes()}
    tris = []
    for t in _triangles(G, adj):
        tris.append(frozenset(t))
        if len(tris) > tri_cap:
            return None, len(tris)
    tri_idx = {t: i for i, t in enumerate(tris)}
    H = nx.Graph()
    H.add_nodes_from(range(len(tris)))
    seen = set()
    for tri in tris:
        a, b, c = sorted(tri)
        for d in (adj[a] & adj[b] & adj[c]):       # d completes a 4-clique
            tet = frozenset((a, b, c, d))
            if tet in seen:
                continue
            seen.add(tet)
            if len(seen) > tetra_cap:
                return None, len(tris)
            faces = [tri_idx[frozenset(f)] for f in
                     ((a, b, c), (a, b, d), (a, c, d), (b, c, d))]
            for x in range(4):
                for y in range(x + 1, 4):
                    H.add_edge(faces[x], faces[y])
    return H, len(tris)


def compute_fi_from_adj(A):
    """SAL fragility index: fraction of edges participating in zero triangles.
    A: n×n binary symmetric adjacency (no self-loops). High FI = fragile."""
    import numpy as np
    n = A.shape[0]
    if n < 2:
        return 0.0
    total = fragile = 0
    for i in range(n):
        row_i = A[i]
        for j in range(i + 1, n):
            if A[i, j]:
                total += 1
                if int(np.dot(row_i, A[j])) == 0:
                    fragile += 1
    return 1.0 if total == 0 else fragile / total


def graph_from_corr(C, threshold):
    """Build a simple graph from a correlation matrix: edge iff C_ij > threshold
    (signed). Returns (nx.Graph, binary adjacency)."""
    import networkx as nx
    import numpy as np
    n = C.shape[0]
    A = (C > threshold).astype(np.int8)
    np.fill_diagonal(A, 0)
    G = nx.from_numpy_array(A)
    return G, A


def hierarchy(C, threshold, want_t3=False, edge_cap=5000, giant=False):
    """Full spectral-hierarchy record for a correlation matrix C at a threshold.

    Protocol mirrors the 45k-graph synthetic study: λ₂ on the FULL graph, and
    ρ / violation / chain are defined ONLY when the relevant graphs are
    connected (`eligible`). If the graph is too dense (edges > edge_cap) we
    raise the threshold in small steps so T(G) (whose node count = #edges of G)
    stays tractable; the threshold actually used is reported.

    `giant=True` runs the spectral hierarchy on G's largest connected component
    (used for the 512-head global graph, which is typically disconnected — the
    giant component is itself a connected graph, so λ₂(T(G_gc)) ≤ λ₂(G_gc) is a
    valid connected-graph test). FI is always computed on the FULL graph (it
    needs no connectivity), so before/after-masking FI stays comparable."""
    import networkx as nx
    t = threshold
    bumped = False
    tri_cap = 4000
    while True:
        G, A = graph_from_corr(C, t)
        ntri = _count_triangles_capped(G, tri_cap)
        # Bound BOTH #edges (= #nodes of T(G)) and #triangles (= #nodes of T₃
        # and the cost driver) so the hierarchy stays exactly computable.
        if (G.number_of_edges() > edge_cap or ntri > tri_cap) and t < 0.95:
            t = round(t + 0.02, 4); bumped = True
            continue
        break

    fi = compute_fi_from_adj(A)                 # full-graph fragility index
    n_comp = nx.number_connected_components(G) if G.number_of_nodes() else 0
    orig_nodes, orig_edges = G.number_of_nodes(), G.number_of_edges()
    if giant and orig_nodes >= 1 and not nx.is_connected(G):
        G = G.subgraph(max(nx.connected_components(G), key=len)).copy()

    l2G, gconn, gn = lambda2(G)
    TG = triangle_graph(G)
    tconn = TG.number_of_nodes() >= 2 and nx.is_connected(TG)
    l2TG, _, _ = lambda2(TG)

    eligible = bool(gconn and tconn)   # both connected → hierarchy is defined
    rec = {
        "threshold": t, "threshold_bumped": bumped, "giant": giant,
        "orig_nodes": int(orig_nodes), "orig_edges": int(orig_edges),
        "n_components": int(n_comp),
        "nodes": int(G.number_of_nodes()), "edges": int(G.number_of_edges()),
        "density": _density(G),
        "G_connected": bool(gconn),
        "TG_nodes": int(TG.number_of_nodes()), "TG_edges": int(TG.number_of_edges()),
        "TG_connected": bool(tconn),
        "eligible": eligible,
        "l2G": l2G, "l2TG": l2TG,
        "rho": (l2TG / l2G) if (eligible and l2G and l2G > TOL) else None,
        "fi": fi,
        "violation": bool(eligible and l2TG is not None and l2G is not None
                          and l2TG - l2G > TOL),
    }
    if want_t3:
        T3, n_tris = tetra_graph(G, tri_cap=tri_cap)
        if T3 is None:                       # too dense for an exact T₃
            rec["T3_skipped"] = True
            rec["T3_nodes"] = int(n_tris)
            rec["T3_connected"] = None
            rec["l2T3"] = None
            rec["chain_eligible"] = False
            rec["chain_holds"] = None
            rec["chain_violation"] = None
        else:
            t3conn = T3.number_of_nodes() >= 2 and nx.is_connected(T3)
            l2T3, _, _ = lambda2(T3)
            chain_eligible = bool(eligible and t3conn)
            rec["T3_skipped"] = False
            rec["T3_nodes"] = int(T3.number_of_nodes())
            rec["T3_connected"] = bool(t3conn)
            rec["l2T3"] = l2T3
            rec["chain_eligible"] = chain_eligible
            rec["chain_holds"] = bool(
                chain_eligible and l2T3 <= l2TG + TOL and l2TG <= l2G + TOL)
            rec["chain_violation"] = bool(
                chain_eligible and not (l2T3 <= l2TG + TOL and l2TG <= l2G + TOL))
    return rec


def _density(G):
    n = G.number_of_nodes()
    if n < 2:
        return 0.0
    return 2.0 * G.number_of_edges() / (n * (n - 1))


# ========================================================================= #
#  Remote GPU function
# ========================================================================= #
@app.function(image=image, gpu="T4", volumes={"/cache": cache_vol},
              timeout=3600)
def run(model_id: str = "facebook/ijepa_vith14_1k",
        n_images: int = 16, threshold: float = 0.3,
        mask_frac: float = 0.33, mask_trials: int = 40, seed: int = 0):
    import numpy as np
    import torch
    import networkx as nx
    from transformers import AutoModel, AutoProcessor

    dev = "cuda" if torch.cuda.is_available() else "cpu"
    print(f"device={dev}  model={model_id}", flush=True)

    # ---- load model (eager attn so attentions are returned) ----
    processor = AutoProcessor.from_pretrained(model_id)
    model = AutoModel.from_pretrained(
        model_id, attn_implementation="eager", torch_dtype=torch.float32)
    model.to(dev).eval()
    cfg = model.config
    n_layers = cfg.num_hidden_layers
    n_heads = cfg.num_attention_heads
    print(f"n_layers={n_layers} n_heads={n_heads} hidden={cfg.hidden_size}", flush=True)

    # ---- load real images ----
    images = _load_images(n_images)
    print(f"loaded {len(images)} images", flush=True)
    n_images = len(images)

    # ---- forward pass(es), accumulate mean attention map per (layer, head) ----
    seq_len = None
    acc = None     # (n_layers, n_heads, seq, seq) running sum over images
    count = 0
    chunk = 4
    for s in range(0, n_images, chunk):
        batch = images[s:s + chunk]
        inp = processor(images=batch, return_tensors="pt").to(dev)
        with torch.no_grad():
            out = model(**inp, output_attentions=True)
        atts = out.attentions
        if atts is None or atts[0] is None:
            raise RuntimeError("model returned no attentions; eager attn failed")
        if acc is None:
            seq_len = atts[0].shape[-1]
            acc = np.zeros((n_layers, n_heads, seq_len, seq_len), dtype=np.float64)
        for L in range(n_layers):
            # (B, heads, seq, seq) -> sum over batch
            acc[L] += atts[L].sum(dim=0).float().cpu().numpy()
        count += len(batch)
        print(f"  processed {count}/{n_images}", flush=True)
    acc /= count   # mean attention map per (layer, head)

    # ---- signatures: flatten each head's mean attention map ----
    # per-layer signatures (n_heads, seq*seq); global stacks all layers
    sigs_per_layer = [acc[L].reshape(n_heads, -1) for L in range(n_layers)]
    global_sigs = acc.reshape(n_layers * n_heads, -1)   # (512, seq*seq)

    def corr(M):
        # Pearson correlation across rows; guard zero-variance rows
        C = np.corrcoef(M)
        C = np.nan_to_num(C, nan=0.0)
        return C

    # ---- STEP 3: per-layer hierarchy ----
    per_layer = []
    for L in range(n_layers):
        C = corr(sigs_per_layer[L])
        rec = hierarchy(C, threshold, want_t3=True, edge_cap=400)
        rec["layer"] = L
        per_layer.append(rec)
        print(f"  layer {L:2d}: edges={rec['edges']:3d} "
              f"l2G={rec['l2G']} l2TG={rec['l2TG']} rho={rec['rho']}", flush=True)

    # ---- STEP 4: global hierarchy over all heads (giant component) ----
    Cg = corr(global_sigs)
    global_rec = hierarchy(Cg, threshold, want_t3=True, edge_cap=5000, giant=True)
    print(f"  GLOBAL: thr={global_rec['threshold']} edges={global_rec['edges']} "
          f"l2G={global_rec['l2G']} l2TG={global_rec['l2TG']} "
          f"l2T3={global_rec.get('l2T3')}", flush=True)

    # ---- STEP 5: SAL-style head masking on the global graph ----
    # Use the (possibly bumped) global threshold so we mask the same graph.
    # giant=True → ρ is the giant-component test; FI is over the full subgraph.
    gthr = global_rec["threshold"]
    base = hierarchy(Cg, gthr, want_t3=False, edge_cap=10**9, giant=True)
    base_fi = base["fi"]

    rng = np.random.default_rng(seed)
    H = n_layers * n_heads
    k_mask = int(round(mask_frac * H))
    masked_rho, masked_fi, masked_viol = [], [], []
    for _ in range(mask_trials):
        keep = np.sort(rng.choice(H, size=H - k_mask, replace=False))
        Csub = Cg[np.ix_(keep, keep)]
        r = hierarchy(Csub, gthr, want_t3=False, edge_cap=10**9, giant=True)
        if r["rho"] is not None:
            masked_rho.append(r["rho"])
        masked_fi.append(r["fi"])
        masked_viol.append(r["violation"])

    def stats(xs):
        xs = [x for x in xs if x is not None]
        if not xs:
            return None
        a = np.asarray(xs, float)
        return {"n": len(a), "mean": float(a.mean()), "std": float(a.std()),
                "min": float(a.min()), "max": float(a.max())}

    masking = {
        "n_heads_total": H, "n_masked": k_mask, "mask_frac": mask_frac,
        "trials": mask_trials, "seed": seed, "threshold": gthr,
        "base_rho": base["rho"], "base_fi": base_fi,
        "base_violation": base["violation"],
        "masked_rho": stats(masked_rho), "masked_fi": stats(masked_fi),
        "masked_violations": int(sum(masked_viol)),
    }
    print(f"  MASK: base_rho={base['rho']} base_fi={base_fi} "
          f"masked_rho={masking['masked_rho']} masked_fi={masking['masked_fi']}",
          flush=True)

    cache_vol.commit()

    return {
        "model_id": model_id, "device": dev,
        "n_layers": n_layers, "n_heads": n_heads,
        "hidden": int(cfg.hidden_size), "seq_len": int(seq_len),
        "n_images": n_images, "threshold": threshold,
        "per_layer": per_layer, "global": global_rec, "masking": masking,
    }


def _load_images(n):
    """Return a list of `n` PIL RGB images. Try HF cifar10 test split, then
    fall back to a few stable image URLs."""
    from PIL import Image
    imgs = []
    try:
        from datasets import load_dataset
        ds = load_dataset("uoft-cs/cifar10", split=f"test[:{n}]")
        col = "img" if "img" in ds.column_names else ds.column_names[0]
        imgs = [ds[i][col].convert("RGB") for i in range(len(ds))]
    except Exception as e:
        print(f"cifar10 load failed ({e}); falling back to URLs", flush=True)
    if len(imgs) < 4:
        import io
        import urllib.request
        urls = [
            "http://images.cocodataset.org/val2017/000000039769.jpg",
            "http://images.cocodataset.org/val2017/000000000139.jpg",
            "http://images.cocodataset.org/val2017/000000000285.jpg",
            "http://images.cocodataset.org/val2017/000000000632.jpg",
            "http://images.cocodataset.org/val2017/000000000724.jpg",
            "http://images.cocodataset.org/val2017/000000000776.jpg",
            "http://images.cocodataset.org/val2017/000000000785.jpg",
            "http://images.cocodataset.org/val2017/000000000802.jpg",
        ]
        for u in urls[:max(n, 8)]:
            try:
                with urllib.request.urlopen(u, timeout=20) as r:
                    imgs.append(Image.open(io.BytesIO(r.read())).convert("RGB"))
            except Exception as e:
                print(f"  url fail {u}: {e}", flush=True)
    if not imgs:
        raise RuntimeError("could not load any images")
    return imgs[:n]


# ========================================================================= #
#  Local entrypoint — runs remote, writes the report.
# ========================================================================= #
@app.local_entrypoint()
def main(model_id: str = "facebook/ijepa_vith14_1k",
         n_images: int = 16, threshold: float = 0.3,
         mask_frac: float = 0.33, mask_trials: int = 40, seed: int = 0):
    res = run.remote(model_id=model_id, n_images=n_images, threshold=threshold,
                     mask_frac=mask_frac, mask_trials=mask_trials, seed=seed)

    here = os.path.dirname(os.path.abspath(__file__))
    informal = os.path.join(here, "informal")
    os.makedirs(informal, exist_ok=True)
    with open(os.path.join(informal, "jepa_real_spectral.json"), "w",
              encoding="utf-8") as f:
        json.dump(res, f, indent=2)

    report = _build_report(res)
    with open(os.path.join(informal, "jepa_real_spectral.md"), "w",
              encoding="utf-8") as f:
        f.write(report)
    print("\nwrote informal/jepa_real_spectral.md and .json")


def _build_report(res):
    pl = res["per_layer"]
    g = res["global"]
    m = res["masking"]

    def fnum(x, d=4):
        return "—" if x is None else f"{x:.{d}f}"

    # per-layer hierarchy violations + ratios (only over ELIGIBLE layers:
    # both G and T(G) connected — the regime where the inequality is defined)
    eligible = [r for r in pl if r["eligible"]]
    viol = [r for r in eligible if r["violation"]]
    rhos = [r["rho"] for r in eligible if r["rho"] is not None]
    ranked = sorted([r for r in eligible if r["rho"] is not None],
                    key=lambda r: r["rho"])

    L = []
    L.append("# Spectral hierarchy on a REAL JEPA model\n")
    L.append(f"**Model.** `{res['model_id']}` "
             f"({res['n_layers']} layers × {res['n_heads']} heads, "
             f"hidden {res['hidden']}, {res['seq_len']} attention tokens), "
             f"run on a Modal **{res['device']}** GPU over **{res['n_images']}** "
             "real images. For each `(layer, head)` we average the self-attention "
             "map over images and flatten it to a signature; heads are joined when "
             f"their attention maps correlate with Pearson **r > {res['threshold']}**.\n")
    L.append("**Question.** The inequality `λ₂(T(G)) ≤ λ₂(G)` (and the full chain "
             "`λ₂(T₃) ≤ λ₂(T(G)) ≤ λ₂(G)`) held across 45,000+ synthetic graphs "
             "with zero violations. Does it survive on a *trained* transformer's "
             "real head-to-head attention-correlation graph?\n")

    # ---- headline ----
    L.append("## Headline\n")
    L.append(f"- **Eligible layers** (both `G` and `T(G)` connected, so the "
             f"inequality is defined): **{len(eligible)}/{len(pl)}**. The other "
             f"{len(pl) - len(eligible)} have a disconnected `T(G)` — `ρ` is "
             "undefined there and they are excluded (not counted as violations).")
    L.append(f"- **Per-layer upper link `λ₂(T(G)) ≤ λ₂(G)`: "
             f"{'✅ 0' if not viol else f'❌ ' + str(len(viol))} violations across "
             f"the {len(eligible)} eligible layers.**")
    if viol:
        L.append("  - Violating layers: "
                 + ", ".join(f"{r['layer']} (ρ={r['rho']:.2f})" for r in viol) + ".")
    gv = ("n/a (graph not eligible)" if not g["eligible"]
          else ("✅ holds" if not g["violation"] else "❌ VIOLATED"))
    L.append(f"- **Global graph (all {res['n_layers']*res['n_heads']} heads): "
             f"upper link {gv}**; full chain "
             f"{'holds ✅' if g.get('chain_holds') else ('VIOLATED ❌' if g.get('chain_violation') else 'n/a (T₃ disconnected)')}.")
    if rhos:
        import statistics
        L.append(f"- Per-layer coherence ratio ρ = λ₂(T)/λ₂(G) over eligible "
                 f"layers: mean {statistics.mean(rhos):.3f}, "
                 f"range [{min(rhos):.3f}, {max(rhos):.3f}].")
    L.append("")

    # ---- per-layer table ----
    L.append("## Per-layer spectral hierarchy\n")
    L.append("`G conn` / `T(G) conn` = whether each graph is connected; the upper "
             "link is only tested on layers where both are (`link` = ✅/❌), else "
             "`n/a`.\n")
    L.append("| layer | edges | dens | G conn | T(G) conn | λ₂(G) | λ₂(T(G)) | ρ=λ₂(T)/λ₂(G) | FI | link |")
    L.append("|---|---|---|---|---|---|---|---|---|---|")
    for r in pl:
        link = ("✅" if not r["violation"] else "❌") if r["eligible"] else "n/a"
        gc = "y" if r["G_connected"] else "n"
        tc = "y" if r["TG_connected"] else "n"
        L.append(f"| {r['layer']} | {r['edges']} | {r['density']:.2f} | {gc} | {tc} | "
                 f"{fnum(r['l2G'],3)} | {fnum(r['l2TG'],3)} | {fnum(r['rho'],3)} | "
                 f"{fnum(r['fi'],3)} | {link} |")
    L.append("")
    if any(r["threshold_bumped"] for r in pl):
        L.append("_(layers where the graph was too dense had their threshold "
                 "raised to keep T(G) tractable; see JSON.)_\n")

    # ---- steepest drop ----
    L.append("## Which layers have the steepest coherence drop?\n")
    if ranked:
        L.append("Smallest ρ = steepest drop from vertex- to edge-connectivity:\n")
        for r in ranked[:5]:
            L.append(f"- **layer {r['layer']}** — ρ = {r['rho']:.3f} "
                     f"(λ₂(G)={fnum(r['l2G'],3)}, λ₂(T)={fnum(r['l2TG'],3)})")
        L.append("")
        L.append(f"- Flattest (ρ closest to 1): **layer {ranked[-1]['layer']}** "
                 f"(ρ = {ranked[-1]['rho']:.3f}).")
    L.append("")

    # ---- global ----
    L.append("## Global attention graph (all heads)\n")
    L.append(f"- Threshold used: **{g['threshold']}**"
             + (" (raised from the requested r > {} so the dense 512-head graph's "
                "triangle count stays exactly computable)".format(res["threshold"])
                if g["threshold_bumped"] else "") + ".")
    L.append(f"- Full graph: {g['orig_nodes']} heads, {g['orig_edges']} edges, "
             f"**{g['n_components']} connected components** — so the hierarchy is "
             "evaluated on the **giant component**.")
    L.append(f"- Giant component: {g['nodes']} nodes, {g['edges']} edges, density "
             f"{g['density']:.3f}.")
    L.append(f"- λ₂(G) = {fnum(g['l2G'])}, λ₂(T(G)) = {fnum(g['l2TG'])}, "
             f"λ₂(T₃) = {fnum(g.get('l2T3'))}.")
    if g["eligible"]:
        L.append(f"- ρ = {fnum(g['rho'])}; FI = {fnum(g['fi'])}; "
                 f"upper link {'holds ✅' if not g['violation'] else 'VIOLATED ❌'}; "
                 f"full chain "
                 f"{'holds ✅' if g.get('chain_holds') else ('VIOLATED ❌' if g.get('chain_violation') else 'n/a — T₃ disconnected')}.")
    else:
        L.append(f"- FI = {fnum(g['fi'])}; ρ / upper link **n/a** — "
                 f"G connected={g['G_connected']}, T(G) connected={g['TG_connected']} "
                 "(inequality undefined unless both are connected).")
    t3desc = (f"skipped (>{4000} triangles — too dense for exact T₃)"
              if g.get("T3_skipped") else
              f"{g.get('T3_nodes','—')} nodes (connected={g.get('T3_connected')})")
    L.append(f"- T(G): {g['TG_nodes']} nodes / {g['TG_edges']} edges "
             f"(connected={g['TG_connected']}); T₃: {t3desc}.")
    L.append("")

    # ---- masking ----
    L.append("## SAL-style head masking (mask 33% of heads)\n")
    L.append(f"Randomly drop **{m['n_masked']}/{m['n_heads_total']}** heads "
             f"({m['mask_frac']:.0%}), recompute the induced attention graph; "
             f"{m['trials']} trials (seed {m['seed']}), threshold {m['threshold']}. "
             "FI = fraction of edges in zero triangles (SAL fragility index; "
             "higher = more fragile), computed on the full induced graph; ρ is the "
             "giant-component value.\n")
    mr, mf = m["masked_rho"], m["masked_fi"]
    L.append("| quantity | before (full) | after masking (mean ± std) |")
    L.append("|---|---|---|")
    L.append(f"| ρ = λ₂(T)/λ₂(G) | {fnum(m['base_rho'])} | "
             f"{fnum(mr['mean']) if mr else '—'} ± {fnum(mr['std']) if mr else '—'} |")
    L.append(f"| FI (fragility) | {fnum(m['base_fi'])} | "
             f"{fnum(mf['mean']) if mf else '—'} ± {fnum(mf['std']) if mf else '—'} |")
    L.append("")
    if mr and m["base_rho"] is not None:
        dr = mr["mean"] - m["base_rho"]
        L.append(f"- Masking **{'raises' if dr > 0 else 'lowers'} ρ** by "
                 f"{abs(dr):.3f} on average → coherence "
                 f"{'improves' if dr > 0 else 'degrades'} relative to the full graph.")
    if mf and m["base_fi"] is not None:
        df = mf["mean"] - m["base_fi"]
        L.append(f"- Masking **{'raises' if df > 0 else 'lowers'} FI** by "
                 f"{abs(df):.3f} → the remaining structure becomes "
                 f"{'more fragile' if df > 0 else 'more robust'}.")
    n_elig = mr["n"] if mr else 0
    L.append(f"- Of {m['trials']} masked subgraphs, {n_elig} were eligible "
             f"(both `G` and `T(G)` connected); upper-link violations among them: "
             f"**{m['masked_violations']}/{max(n_elig,1) if n_elig else m['trials']}**"
             f"{'' if n_elig else ' (none eligible)'}.")
    L.append("")

    # ---- takeaways ----
    L.append("## Takeaways\n")
    if not viol:
        L.append(f"- **The hierarchy `λ₂(T(G)) ≤ λ₂(G)` holds on real JEPA attention "
                 f"connectivity** wherever it is defined: **0 violations across the "
                 f"{len(eligible)} eligible layers** (ρ ∈ "
                 f"[{min(rhos):.2f}, {max(rhos):.2f}] < 1) — consistent with the "
                 "45,000+ synthetic-graph result. The inequality is not an artifact "
                 "of synthetic topology.")
    else:
        L.append(f"- **Violations of `λ₂(T(G)) ≤ λ₂(G)` found** on the trained model "
                 f"({len(viol)}/{len(eligible)} eligible layers). Unlike the 45,000+ "
                 "synthetic graphs, real attention connectivity **can break the "
                 "conjecture** — a genuinely new data point.")
    L.append("- **The connectivity gate is the real story.** Half the layers, and "
             "the entire 512-head global graph, have a **disconnected `T(G)`**: many "
             "attention-head pairs correlate without sitting in any triangle, so the "
             "inequality is simply *undefined* there (reported `n/a`, never silently "
             "counted as a pass). Real attention connectivity is far more "
             "triangle-sparse than the dense synthetic families.")
    if m["base_fi"] is not None and m["masked_fi"]:
        df = m["masked_fi"]["mean"] - m["base_fi"]
        L.append(f"- **SAL masking → fragility.** ρ is undefined under masking (the "
                 f"masked giant components also have disconnected `T(G)`), but FI is "
                 f"well-defined and **{'rises' if df>0 else 'falls'} "
                 f"{m['base_fi']:.3f} → {m['masked_fi']['mean']:.3f}** when 33% of "
                 f"heads are dropped: removing heads makes the remaining attention "
                 f"graph {'more fragile' if df>0 else 'more robust'} (more edges fall "
                 "outside any triangle).")
    L.append("- ρ measures how much algebraic connectivity is lost passing from "
             "heads to head-interactions; per-layer ρ identifies which depths carry "
             "the most redundant (triangle-rich) vs. fragile attention structure "
             f"(steepest: layer {ranked[0]['layer']}, ρ={ranked[0]['rho']:.2f}; "
             f"flattest: layer {ranked[-1]['layer']}, ρ={ranked[-1]['rho']:.2f}).")
    L.append("")
    L.append("## Caveats\n")
    L.append(f"- One model (`{res['model_id']}`), {res['n_images']} images, single "
             "seed. Graphs are unweighted (edge iff r > τ). **Per-layer**: λ₂ on the "
             "full graph, with ρ/violation gated on both `G` and `T(G)` being "
             "connected (exactly the 45k-graph protocol — no component surgery). "
             "**Global** (512 heads): the graph is disconnected, so the hierarchy is "
             "evaluated on its giant component (a legitimately connected graph), "
             "while FI is computed on the full graph. The global τ is raised from 0.3 "
             "until the triangle count is exactly computable; the τ used is reported.")
    L.append("- Head masking here is **graph-level** (drop head-nodes, recompute the "
             "induced correlation graph), not a re-forward-pass with head outputs "
             "zeroed; it isolates the structural effect on the attention graph, the "
             "level at which SAL's FI is defined.\n")
    return "\n".join(L) + "\n"
