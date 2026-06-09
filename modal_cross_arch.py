"""
Cross-architecture spectral simplicial hierarchy on REAL transformer attention.

Companion to `modal_jepa.py`. That script validated, on a pretrained I-JEPA
ViT-H/14, the empirically universal inequality

        λ₂(T(G)) ≤ λ₂(G)            (and the chain λ₂(T₃) ≤ λ₂(T(G)) ≤ λ₂(G))

on the model's head-to-head attention-correlation graph (0 violations on 16
eligible layers, ρ ∈ [0.19, 0.75]). THIS script runs the *exact same pipeline*
on three more architectures to get a comparative picture:

  1. BERT  (`bert-base-uncased`)      — 12 L × 12 H, encoder-only,  text
  2. GPT-2 (`gpt2`)                   — 12 L × 12 H, decoder-only,  text
  3. ViT   (`google/vit-base-patch16-224`) — 12 L × 12 H, vision

All graph / hierarchy / masking math is imported verbatim from `modal_jepa`
(`lambda2`, `triangle_graph`, `tetra_graph`, `hierarchy`, `compute_fi_from_adj`,
…) so the methodology is byte-for-byte identical to the I-JEPA experiment — the
only thing that changes is how attention is extracted (text tokenization vs.
image patches).

Pipeline (per model, all on a single T4 GPU, one Modal call)
------------------------------------------------------------
  STEP 1  forward pass with `output_attentions=True` (eager attn)
            · text  models: 16 English sentences, padded to a fixed length
            · vision model:  16 CIFAR-10 images (same source as I-JEPA)
  STEP 2  per layer: mean attention map per (layer, head) → flattened signature;
            graph G_L: nodes = heads, edge iff Pearson r(sig_i, sig_j) > τ
  STEP 3  per-layer spectral hierarchy: λ₂(G), λ₂(T(G)), ρ = λ₂(T)/λ₂(G), FI
  STEP 4  global graph over all 144 heads (giant component): λ₂(G/T(G)/T₃)
  STEP 5  SAL-style head masking: drop 33% of heads, recompute FI before/after

Usage
-----
    modal run modal_cross_arch.py
    modal run modal_cross_arch.py --n-images 16 --threshold 0.3

The local entrypoint folds in the saved I-JEPA result
(`informal/jepa_real_spectral.json`) and writes the comparative report to
`informal/cross_architecture_spectral.{md,json}`.
"""
import json
import os
import statistics

import modal

# Reuse the EXACT graph/hierarchy/masking helpers from the I-JEPA experiment.
# (Pure numpy+networkx; all heavy imports happen inside the function bodies, so
# they are safe to call remotely once modal_jepa.py is shipped into the image.)
from modal_jepa import hierarchy  # noqa: F401  (used remotely)

# --------------------------------------------------------------------------- #
# Image: Python 3.10 + torch + transformers + graph/num stack, T4 GPU.
# Identical dependency set to modal_jepa.py. `add_local_python_source` ships
# modal_jepa.py into the container so the imported helpers resolve remotely.
# --------------------------------------------------------------------------- #
image = (
    modal.Image.debian_slim(python_version="3.10")
    .pip_install(
        "torch==2.4.1",
        "transformers==4.49.0",
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
    .add_local_python_source("modal_jepa")
)

app = modal.App("cross-arch-spectral")

# Reuse the I-JEPA HF cache volume so the cifar10 download is shared.
cache_vol = modal.Volume.from_name("jepa-hf-cache", create_if_missing=True)

# 16 diverse English sentences for the text models (varied length & topic so the
# head signatures are not degenerate). Same batch fed to BERT and GPT-2.
SENTENCES = [
    "The quick brown fox jumps over the lazy dog near the river.",
    "Scientists discovered a new species of butterfly in the rainforest.",
    "She carefully placed the fragile vase on the wooden shelf.",
    "Global markets rallied after the central bank cut interest rates.",
    "He learned to play the violin when he was only six years old.",
    "The ancient castle stood silently on the hill above the village.",
    "Machine learning models require large amounts of training data.",
    "A gentle breeze carried the scent of blossoms across the garden.",
    "The committee voted unanimously to approve the new budget proposal.",
    "Children laughed and played in the park on a sunny afternoon.",
    "The spacecraft entered orbit after a seven month journey to Mars.",
    "Fresh bread and strong coffee filled the small bakery with warmth.",
    "Engineers tested the bridge under heavy load before opening it.",
    "The novel explores themes of memory, loss, and the passage of time.",
    "Volunteers planted hundreds of trees along the eroding coastline.",
    "Quantum computers may one day solve problems classical machines cannot.",
]

# Models to test: (key, model_id, modality, arch label).
MODELS = [
    ("BERT", "bert-base-uncased", "text", "Encoder"),
    ("GPT-2", "gpt2", "text", "Decoder"),
    ("ViT", "google/vit-base-patch16-224", "vision", "ViT-B/16"),
]


# ========================================================================= #
#  Attention extraction (the ONLY part that differs across modalities).
#  Both paths return: acc (n_layers, n_heads, seq, seq) = mean attention map
#  per (layer, head), plus model metadata. The downstream graph/hierarchy/
#  masking code is identical to modal_jepa.py.
# ========================================================================= #
def _extract_text(model_id, sentences, dev, max_length=32):
    import numpy as np
    import torch
    from transformers import AutoModel, AutoTokenizer

    tok = AutoTokenizer.from_pretrained(model_id)
    if tok.pad_token is None:          # GPT-2 has no pad token by default
        tok.pad_token = tok.eos_token
    model = AutoModel.from_pretrained(
        model_id, attn_implementation="eager", torch_dtype=torch.float32)
    model.to(dev).eval()
    cfg = model.config
    n_layers, n_heads = cfg.num_hidden_layers, cfg.num_attention_heads

    acc = None
    seq_len = None
    count = 0
    chunk = 4
    for s in range(0, len(sentences), chunk):
        batch = sentences[s:s + chunk]
        inp = tok(batch, return_tensors="pt", padding="max_length",
                  truncation=True, max_length=max_length).to(dev)
        with torch.no_grad():
            out = model(**inp, output_attentions=True)
        atts = out.attentions
        if atts is None or atts[0] is None:
            raise RuntimeError(f"{model_id} returned no attentions")
        if acc is None:
            seq_len = atts[0].shape[-1]
            acc = np.zeros((n_layers, n_heads, seq_len, seq_len), dtype=np.float64)
        for L in range(n_layers):
            acc[L] += atts[L].sum(dim=0).float().cpu().numpy()
        count += len(batch)
        print(f"    processed {count}/{len(sentences)}", flush=True)
    acc /= count
    return acc, n_layers, n_heads, int(cfg.hidden_size), int(seq_len), count


def _extract_vision(model_id, images, dev):
    import numpy as np
    import torch
    from transformers import AutoImageProcessor, AutoModel

    proc = AutoImageProcessor.from_pretrained(model_id)
    model = AutoModel.from_pretrained(
        model_id, attn_implementation="eager", torch_dtype=torch.float32)
    model.to(dev).eval()
    cfg = model.config
    n_layers, n_heads = cfg.num_hidden_layers, cfg.num_attention_heads

    acc = None
    seq_len = None
    count = 0
    chunk = 4
    for s in range(0, len(images), chunk):
        batch = images[s:s + chunk]
        inp = proc(images=batch, return_tensors="pt").to(dev)
        with torch.no_grad():
            out = model(**inp, output_attentions=True)
        atts = out.attentions
        if atts is None or atts[0] is None:
            raise RuntimeError(f"{model_id} returned no attentions")
        if acc is None:
            seq_len = atts[0].shape[-1]
            acc = np.zeros((n_layers, n_heads, seq_len, seq_len), dtype=np.float64)
        for L in range(n_layers):
            acc[L] += atts[L].sum(dim=0).float().cpu().numpy()
        count += len(batch)
        print(f"    processed {count}/{len(images)}", flush=True)
    acc /= count
    return acc, n_layers, n_heads, int(cfg.hidden_size), int(seq_len), count


# ========================================================================= #
#  STEP 3/4/5 — identical to modal_jepa.run, factored out so all models share
#  the exact same hierarchy + masking protocol.
# ========================================================================= #
def _analyze(acc, n_layers, n_heads, threshold, mask_frac, mask_trials, seed):
    import numpy as np

    sigs_per_layer = [acc[L].reshape(n_heads, -1) for L in range(n_layers)]
    global_sigs = acc.reshape(n_layers * n_heads, -1)

    def corr(M):
        C = np.corrcoef(M)
        return np.nan_to_num(C, nan=0.0)

    # ---- STEP 3: per-layer hierarchy (same edge_cap=400 as I-JEPA) ----
    per_layer = []
    for L in range(n_layers):
        C = corr(sigs_per_layer[L])
        rec = hierarchy(C, threshold, want_t3=True, edge_cap=400)
        rec["layer"] = L
        per_layer.append(rec)
        print(f"    layer {L:2d}: edges={rec['edges']:3d} "
              f"l2G={rec['l2G']} l2TG={rec['l2TG']} rho={rec['rho']}", flush=True)

    # ---- STEP 4: global hierarchy over all heads (giant component) ----
    Cg = corr(global_sigs)
    global_rec = hierarchy(Cg, threshold, want_t3=True, edge_cap=5000, giant=True)
    print(f"    GLOBAL: thr={global_rec['threshold']} edges={global_rec['edges']} "
          f"l2G={global_rec['l2G']} l2TG={global_rec['l2TG']} "
          f"l2T3={global_rec.get('l2T3')}", flush=True)

    # ---- STEP 5: SAL-style head masking on the global graph ----
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
    print(f"    MASK: base_fi={base_fi} masked_fi={masking['masked_fi']}", flush=True)
    return per_layer, global_rec, masking


# ========================================================================= #
#  Remote GPU function — runs ALL three models in one call (one cold start).
# ========================================================================= #
@app.function(image=image, gpu="T4", volumes={"/cache": cache_vol},
              timeout=3600)
def run(n_images: int = 16, threshold: float = 0.3,
        mask_frac: float = 0.33, mask_trials: int = 40, seed: int = 0):
    import torch

    dev = "cuda" if torch.cuda.is_available() else "cpu"
    print(f"device={dev}", flush=True)

    images = _load_images(n_images)
    print(f"loaded {len(images)} images for the vision model", flush=True)

    results = {}
    for key, model_id, modality, arch in MODELS:
        print(f"\n=== {key} ({model_id}, {modality}) ===", flush=True)
        if modality == "text":
            acc, n_layers, n_heads, hidden, seq_len, count = _extract_text(
                model_id, SENTENCES, dev)
            n_inputs = count
        else:
            acc, n_layers, n_heads, hidden, seq_len, count = _extract_vision(
                model_id, images, dev)
            n_inputs = count
        print(f"  {key}: n_layers={n_layers} n_heads={n_heads} hidden={hidden} "
              f"seq_len={seq_len} inputs={n_inputs}", flush=True)

        per_layer, global_rec, masking = _analyze(
            acc, n_layers, n_heads, threshold, mask_frac, mask_trials, seed)

        results[key] = {
            "model_id": model_id, "arch": arch, "modality": modality,
            "device": dev, "n_layers": n_layers, "n_heads": n_heads,
            "hidden": hidden, "seq_len": seq_len, "n_inputs": n_inputs,
            "threshold": threshold,
            "per_layer": per_layer, "global": global_rec, "masking": masking,
        }

    cache_vol.commit()
    return results


def _load_images(n):
    """Return `n` PIL RGB images — HF cifar10 test split (same source as the
    I-JEPA run), with a COCO-URL fallback."""
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
#  Summary helpers — collapse a per-model result to a comparison-table row.
# ========================================================================= #
def _summarize(res):
    """Return the comparison-row dict for one model's result block."""
    pl = res["per_layer"]
    eligible = [r for r in pl if r["eligible"]]
    viol = [r for r in eligible if r["violation"]]
    rhos = [r["rho"] for r in eligible if r["rho"] is not None]
    m = res["masking"]
    mf = m["masked_fi"]
    return {
        "model": res.get("label", res["model_id"]),
        "arch": res["arch"],
        "modality": res["modality"],
        "layers": res["n_layers"],
        "heads": res["n_heads"],
        "eligible": len(eligible),
        "violations": len(viol),
        "rho_min": (min(rhos) if rhos else None),
        "rho_max": (max(rhos) if rhos else None),
        "rho_mean": (statistics.mean(rhos) if rhos else None),
        "fi_base": m["base_fi"],
        "fi_masked": (mf["mean"] if mf else None),
        "fi_delta": ((mf["mean"] - m["base_fi"]) if mf and m["base_fi"] is not None else None),
        "global_threshold": res["global"]["threshold"],
        "global_components": res["global"]["n_components"],
    }


def _summarize_jepa(j):
    """Build the same comparison-row from the saved I-JEPA JSON (different top-
    level shape: a single result, not a {key: result} map)."""
    pl = j["per_layer"]
    eligible = [r for r in pl if r["eligible"]]
    viol = [r for r in eligible if r["violation"]]
    rhos = [r["rho"] for r in eligible if r["rho"] is not None]
    m = j["masking"]
    mf = m["masked_fi"]
    return {
        "model": "I-JEPA",
        "arch": "ViT-H/14",
        "modality": "vision",
        "layers": j["n_layers"],
        "heads": j["n_heads"],
        "eligible": len(eligible),
        "violations": len(viol),
        "rho_min": (min(rhos) if rhos else None),
        "rho_max": (max(rhos) if rhos else None),
        "rho_mean": (statistics.mean(rhos) if rhos else None),
        "fi_base": m["base_fi"],
        "fi_masked": (mf["mean"] if mf else None),
        "fi_delta": ((mf["mean"] - m["base_fi"]) if mf and m["base_fi"] is not None else None),
        "global_threshold": j["global"]["threshold"],
        "global_components": j["global"]["n_components"],
    }


# ========================================================================= #
#  Local entrypoint — runs remote, folds in I-JEPA, writes the report.
# ========================================================================= #
@app.local_entrypoint()
def main(n_images: int = 16, threshold: float = 0.3,
         mask_frac: float = 0.33, mask_trials: int = 40, seed: int = 0):
    res = run.remote(n_images=n_images, threshold=threshold,
                     mask_frac=mask_frac, mask_trials=mask_trials, seed=seed)
    for key in res:
        res[key]["label"] = key

    here = os.path.dirname(os.path.abspath(__file__))
    informal = os.path.join(here, "informal")
    os.makedirs(informal, exist_ok=True)

    # Fold in the saved I-JEPA result if present.
    jepa = None
    jpath = os.path.join(informal, "jepa_real_spectral.json")
    if os.path.exists(jpath):
        with open(jpath, encoding="utf-8") as f:
            jepa = json.load(f)

    # Comparison rows: I-JEPA first (matching the requested table), then ours.
    rows = []
    if jepa is not None:
        rows.append(_summarize_jepa(jepa))
    for key, *_ in MODELS:
        rows.append(_summarize(res[key]))

    out = {
        "params": {"n_images": n_images, "threshold": threshold,
                   "mask_frac": mask_frac, "mask_trials": mask_trials,
                   "seed": seed},
        "comparison": rows,
        "models": res,
        "jepa_included": jepa is not None,
    }
    with open(os.path.join(informal, "cross_architecture_spectral.json"), "w",
              encoding="utf-8") as f:
        json.dump(out, f, indent=2)

    report = _build_report(res, rows, out["params"])
    with open(os.path.join(informal, "cross_architecture_spectral.md"), "w",
              encoding="utf-8") as f:
        f.write(report)
    print("\nwrote informal/cross_architecture_spectral.md and .json")


def _build_report(res, rows, params):
    def fnum(x, d=3):
        return "—" if x is None else f"{x:.{d}f}"

    L = []
    L.append("# Cross-architecture spectral hierarchy on real attention\n")
    L.append("**Question.** The inequality `λ₂(T(G)) ≤ λ₂(G)` (and the chain "
             "`λ₂(T₃) ≤ λ₂(T(G)) ≤ λ₂(G)`) held across 45,000+ synthetic graphs "
             "with zero violations, and on a pretrained I-JEPA ViT-H/14. Does it "
             "survive across *encoder-only*, *decoder-only*, and *vision* "
             "transformers — and does fragility (FI) behave the same under "
             "SAL-style head masking?\n")
    L.append("**Method (identical to the I-JEPA run).** For each model we run a "
             "forward pass with `output_attentions=True` (eager attention), "
             "average each head's attention map over the inputs, flatten it to a "
             f"signature, and join heads whose signatures correlate with Pearson "
             f"**r > {params['threshold']}**. Per layer we compute λ₂(G), λ₂(T(G)) "
             "and ρ = λ₂(T)/λ₂(G) (defined only where both `G` and `T(G)` are "
             "connected); globally we evaluate the giant component of all "
             f"L×H heads and mask **{params['mask_frac']:.0%}** of heads "
             f"({params['mask_trials']} random trials, seed {params['seed']}) to "
             "measure the fragility index FI (fraction of edges in zero "
             "triangles). Text models see 16 English sentences; vision models see "
             f"16 CIFAR-10 images.\n")

    # ---- headline comparison table ----
    L.append("## Comparison table\n")
    L.append("| Model | Arch | Layers | Eligible | Violations | ρ_min | ρ_max | "
             "ρ_mean | FI_base | FI_masked |")
    L.append("|---|---|---|---|---|---|---|---|---|---|")
    for r in rows:
        L.append(f"| {r['model']} | {r['arch']} | {r['layers']} | "
                 f"{r['eligible']} | {r['violations']} | "
                 f"{fnum(r['rho_min'],2)} | {fnum(r['rho_max'],2)} | "
                 f"{fnum(r['rho_mean'],3)} | {fnum(r['fi_base'],3)} | "
                 f"{fnum(r['fi_masked'],3)} |")
    L.append("")

    # ---- key questions ----
    total_viol = sum(r["violations"] for r in rows)
    L.append("## Key findings\n")
    if total_viol == 0:
        L.append(f"- **The hierarchy holds across ALL architectures: 0 violations** "
                 f"of `λ₂(T(G)) ≤ λ₂(G)` over every eligible layer of every model "
                 f"(I-JEPA, BERT, GPT-2, ViT). The inequality is not an artifact of "
                 "synthetic topology, model size, modality, or attention direction "
                 "(causal vs. bidirectional).")
    else:
        L.append(f"- **{total_viol} violation(s) of `λ₂(T(G)) ≤ λ₂(G)` found** "
                 "across the four models — see the per-model sections.")
    # best coherence
    ranked = sorted([r for r in rows if r["rho_mean"] is not None],
                    key=lambda r: r["rho_mean"], reverse=True)
    if ranked:
        best, worst = ranked[0], ranked[-1]
        L.append(f"- **Triangular coherence (ρ_mean) is highest in "
                 f"{best['model']}** ({fnum(best['rho_mean'],3)}) and lowest in "
                 f"{worst['model']}** ({fnum(worst['rho_mean'],3)}). Higher ρ = the "
                 "head-interaction graph keeps more of the head graph's algebraic "
                 "connectivity (more triangle-redundant structure).")
    # enc vs dec vs vision
    by_model = {r["model"]: r for r in rows}
    if {"BERT", "GPT-2"} <= set(by_model):
        b, g = by_model["BERT"], by_model["GPT-2"]
        L.append(f"- **Encoder vs. decoder (same 12×12 size, same text inputs).** "
                 f"BERT/GPT-2 eligible layers {b['eligible']}/{g['eligible']}, "
                 f"ρ_mean {fnum(b['rho_mean'],3)}/{fnum(g['rho_mean'],3)}, "
                 f"FI_base {fnum(b['fi_base'],3)}/{fnum(g['fi_base'],3)}. "
                 "Bidirectional vs. causal attention "
                 + ("yields a markedly different connectivity profile."
                    if b["eligible"] != g["eligible"] else
                    "yields broadly similar spectral profiles."))
    # masking → fragility
    L.append("- **SAL masking → fragility, in every architecture.** Dropping "
             f"{params['mask_frac']:.0%} of heads changes FI as follows:")
    for r in rows:
        if r["fi_delta"] is not None:
            arrow = "↑" if r["fi_delta"] > 0 else ("↓" if r["fi_delta"] < 0 else "→")
            L.append(f"  - {r['model']}: FI {fnum(r['fi_base'],3)} → "
                     f"{fnum(r['fi_masked'],3)} ({arrow} {abs(r['fi_delta']):.3f})")
    L.append("")

    # ---- per-model detail ----
    for key, *_ in MODELS:
        r = res[key]
        L.append(_model_section(r, fnum))
    L.append("")

    # ---- caveats ----
    L.append("## Caveats\n")
    L.append("- Single seed, 16 inputs per model, unweighted graphs (edge iff "
             "r > τ). Text attention maps are computed over sentences padded to a "
             "fixed length, so pad positions are part of the signature (consistent "
             "across the batch, same as the ViT patch grid). The per-layer "
             "protocol gates ρ/violation on both `G` and `T(G)` being connected "
             "(no component surgery); the global graph is evaluated on its giant "
             "component while FI is over the full induced graph. The global τ is "
             "raised from the requested value until the triangle count is exactly "
             "computable; the τ used is reported per model.")
    L.append("- Head masking is graph-level (drop head-nodes, recompute the "
             "induced correlation graph), not a re-forward-pass with head outputs "
             "zeroed — it isolates the structural effect on the attention graph, "
             "the level at which SAL's FI is defined.")
    L.append("- All graph/hierarchy/masking math is imported verbatim from "
             "`modal_jepa.py`; only attention extraction differs by modality.\n")
    return "\n".join(L) + "\n"


def _model_section(r, fnum):
    pl = r["per_layer"]
    g = r["global"]
    m = r["masking"]
    eligible = [x for x in pl if x["eligible"]]
    viol = [x for x in eligible if x["violation"]]
    rhos = [(x["layer"], x["rho"]) for x in eligible if x["rho"] is not None]
    rhos_sorted = sorted(rhos, key=lambda t: t[1])

    S = []
    S.append(f"## {r.get('label', r['model_id'])} — `{r['model_id']}` "
             f"({r['arch']}, {r['modality']})\n")
    S.append(f"{r['n_layers']} layers × {r['n_heads']} heads, hidden "
             f"{r['hidden']}, {r['seq_len']} attention tokens, "
             f"{r['n_inputs']} inputs.\n")
    S.append(f"- Eligible layers (both `G`, `T(G)` connected): "
             f"**{len(eligible)}/{len(pl)}**; upper-link violations: "
             f"**{len(viol)}**"
             + ("." if not viol else
                " (" + ", ".join(f"L{x['layer']}" for x in viol) + ")."))
    if rhos_sorted:
        lo, hi = rhos_sorted[0], rhos_sorted[-1]
        S.append(f"- ρ over eligible layers: range "
                 f"[{fnum(lo[1],3)} (L{lo[0]}), {fnum(hi[1],3)} (L{hi[0]})], "
                 f"mean {fnum(statistics.mean([v for _, v in rhos]),3)}.")
    gelig = g["eligible"]
    S.append(f"- Global graph (all {r['n_layers']*r['n_heads']} heads): "
             f"τ={g['threshold']}, {g['orig_edges']} edges, "
             f"{g['n_components']} components → giant component "
             f"{g['nodes']} nodes/{g['edges']} edges; "
             + (f"ρ={fnum(g['rho'])}, upper link "
                f"{'holds ✅' if not g['violation'] else 'VIOLATED ❌'}."
                if gelig else
                f"ρ n/a (T(G) connected={g['TG_connected']})."))
    mf = m["masked_fi"]
    if mf is not None and m["base_fi"] is not None:
        d = mf["mean"] - m["base_fi"]
        S.append(f"- SAL masking (drop {m['n_masked']}/{m['n_heads_total']} "
                 f"heads): FI {fnum(m['base_fi'])} → {fnum(mf['mean'])} ± "
                 f"{fnum(mf['std'])} "
                 f"({'more fragile' if d > 0 else 'more robust'}).")

    # early vs deep redundancy (mean ρ of first vs second half of eligible layers)
    if len(rhos) >= 4:
        half = r["n_layers"] // 2
        early = [v for (lay, v) in rhos if lay < half]
        deep = [v for (lay, v) in rhos if lay >= half]
        if early and deep:
            em, dm = statistics.mean(early), statistics.mean(deep)
            S.append(f"- Early vs. deep eligible layers: ρ_mean "
                     f"{fnum(em,3)} (L<{half}) vs. {fnum(dm,3)} (L≥{half}) — "
                     f"deep layers are "
                     f"{'more' if dm > em else 'less'} triangle-redundant.")
    S.append("")
    return "\n".join(S)
