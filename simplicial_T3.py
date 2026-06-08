"""
Simplicial hierarchy experiment — extend the triangle graph T(G) to tetrahedra.

Dimensional ladder of "shared-facet, common-cofacet" graphs:
  G          : vertices joined by EDGES                         -> lambda2(G)
  T(G)       : EDGES joined when they share a vertex and lie in a common TRIANGLE
               (= the existing triangle graph)                  -> lambda2(T(G))
  T3(K)      : TRIANGLES joined when they share an edge and lie in a common
               TETRAHEDRON                                      -> lambda2(T3(K))

Conjectured simplicial hierarchy:
        lambda2(T3(K))  <=  lambda2(T(G))  <=  lambda2(G)

T(G) uses the *existing* repo definition (adjacency via 3-cliques of the
1-skeleton). T3(K) needs a genuine 3-complex (tetrahedra), so we work with
clique complexes of K_n, random 3-complexes, and triangulated 3-spheres.

Pure exploration (networkx + numpy). Run:  python simplicial_T3.py
"""
import os
from itertools import combinations, product

import numpy as np
import networkx as nx

import counterexample_search as ce

TOL = 1e-9


# --------------------------------------------------------------------------- #
# abstract simplicial complex (dims 0..3)
# --------------------------------------------------------------------------- #
class SC:
    def __init__(self):
        self.tetra = set()   # frozensets of size 4
        self.tri = set()     # size 3
        self.edges = set()   # size 2
        self.verts = set()

    def add_edge(self, e):
        e = frozenset(e)
        if len(e) == 2:
            self.edges.add(e); self.verts |= e

    def add_tri(self, t):
        t = frozenset(t)
        if len(t) == 3:
            self.tri.add(t)
            for e in combinations(sorted(t), 2):
                self.add_edge(e)

    def add_tetra(self, t):
        t = frozenset(t)
        if len(t) == 4:
            self.tetra.add(t)
            for tr in combinations(sorted(t), 3):
                self.add_tri(tr)

    def rebuild_from_tetra(self):
        """For a PURE 3-complex (every face is in a tetra): derive tri/edges."""
        self.tri = set(); self.edges = set(); self.verts = set()
        for t in self.tetra:
            self.add_tetra(t)

    def skeleton(self):
        G = nx.Graph()
        G.add_nodes_from(sorted(self.verts))
        G.add_edges_from(tuple(sorted(e)) for e in self.edges)
        return G

    def tetra_graph(self):
        """T3(K): nodes = triangles; adjacent iff they share an edge (|∩|=2) and
        their union (4 verts) is a tetrahedron of K."""
        tris = [frozenset(t) for t in self.tri]
        H = nx.Graph()
        H.add_nodes_from(range(len(tris)))
        for i in range(len(tris)):
            ti = tris[i]
            for j in range(i + 1, len(tris)):
                tj = tris[j]
                if len(ti & tj) == 2 and (ti | tj) in self.tetra:
                    H.add_edge(i, j)
        return H

    # ---- constructors ----
    @classmethod
    def clique_complex(cls, G):
        """All 3-cliques become triangles, all 4-cliques become tetrahedra."""
        K = cls()
        for e in G.edges():
            K.add_edge(e)
        for clq in nx.enumerate_all_cliques(G):
            if len(clq) == 3:
                K.add_tri(clq)
            elif len(clq) == 4:
                K.add_tetra(clq)
        return K


def lam2(H):
    """Second-smallest Laplacian eigenvalue, or None if < 2 nodes."""
    if H.number_of_nodes() < 2:
        return None
    return ce.lambda2(H)


# --------------------------------------------------------------------------- #
# generators
# --------------------------------------------------------------------------- #
def gen_complete_clique(ns=(5, 6, 7, 8)):
    out = []
    for n in ns:
        K = SC.clique_complex(nx.complete_graph(n))
        out.append(("K_n clique", f"K{n}", K))
    return out


def gen_random_complexes(rng, count=1000):
    out = []
    n_choices = [6, 7, 8, 9, 10]
    for _ in range(count):
        n = int(rng.choice(n_choices))
        p = float(rng.uniform(0.6, 0.97))      # denser => T3 more often connected
        q = float(rng.uniform(0.5, 1.0))
        G = nx.gnp_random_graph(n, p, seed=int(rng.integers(0, 2**31)))
        K = SC()
        for e in G.edges():
            K.add_edge(e)
        cliques = list(nx.enumerate_all_cliques(G))
        for clq in cliques:
            if len(clq) == 3:
                K.add_tri(clq)
        for clq in cliques:
            if len(clq) == 4 and rng.random() < q:
                K.add_tetra(clq)
        out.append(("random 3-complex", f"rand-n{n}-p{p:.2f}-q{q:.2f}", K))
    return out


def boundary_4simplex():
    K = SC()
    for t in combinations(range(5), 4):
        K.add_tetra(t)
    return K


def cross_polytope_16cell():
    pairs = [(0, 1), (2, 3), (4, 5), (6, 7)]
    K = SC()
    for choice in product(*pairs):
        K.add_tetra(choice)
    return K


def stacked_sphere(k, rng):
    """Start from the boundary of the 4-simplex (a 3-sphere) and apply k random
    stellar subdivisions of facets (each replaces one tetra by four)."""
    K = boundary_4simplex()
    next_v = 5
    for _ in range(k):
        tet = list(K.tetra)[int(rng.integers(0, len(K.tetra)))]
        a, b, c, d = sorted(tet)
        v = next_v; next_v += 1
        K.tetra.discard(tet)
        for face in combinations((a, b, c, d), 3):
            K.tetra.add(frozenset(face + (v,)))
    K.rebuild_from_tetra()
    return K


def gen_spheres(rng):
    out = [("3-sphere", "boundary-4simplex", boundary_4simplex()),
           ("3-sphere", "cross-polytope-16cell", cross_polytope_16cell())]
    for k in (1, 2, 3, 4, 5, 6, 8, 10):
        for r in range(4):
            out.append(("stacked 3-sphere",
                        f"stacked-k{k}-{r}", stacked_sphere(k, rng)))
    return out


# --------------------------------------------------------------------------- #
# analysis
# --------------------------------------------------------------------------- #
def analyse(K):
    G = K.skeleton()
    TG = ce.triangle_graph(G)
    T3 = K.tetra_graph()
    rec = {
        "nV": G.number_of_nodes(), "nE": G.number_of_edges(),
        "nTri": len(K.tri), "nTet": len(K.tetra),
        "Gc": G.number_of_nodes() >= 2 and nx.is_connected(G),
        "TGc": TG.number_of_nodes() >= 2 and nx.is_connected(TG),
        "T3c": T3.number_of_nodes() >= 2 and nx.is_connected(T3),
        "TGn": TG.number_of_nodes(), "T3n": T3.number_of_nodes(),
    }
    rec["l2G"] = lam2(G) if rec["Gc"] else None
    rec["l2TG"] = lam2(TG) if rec["TGc"] else None
    rec["l2T3"] = lam2(T3) if rec["T3c"] else None
    rec["full"] = rec["Gc"] and rec["TGc"] and rec["T3c"]
    return rec


def _pearson(x, y):
    x = np.asarray(x, float); y = np.asarray(y, float)
    if len(x) < 2 or np.std(x) == 0 or np.std(y) == 0:
        return float("nan")
    return float(np.corrcoef(x, y)[0, 1])


def main():
    rng = np.random.default_rng(20260608)
    families = (gen_complete_clique() + gen_spheres(rng)
                + gen_random_complexes(rng, 1000))

    rows = []
    for fam, name, K in families:
        r = analyse(K); r["family"] = fam; r["name"] = name
        rows.append(r)

    full = [r for r in rows if r["full"]]                 # all three connected

    # ---- hierarchy checks over fully-connected complexes ----
    link_lower = []   # λ₂(T3) ≤ λ₂(T(G))
    link_upper = []   # λ₂(T(G)) ≤ λ₂(G)
    viol_lower, viol_upper = [], []
    for r in full:
        sL = r["l2TG"] - r["l2T3"]
        sU = r["l2G"] - r["l2TG"]
        link_lower.append(sL); link_upper.append(sU)
        if sL < -TOL:
            viol_lower.append(r)
        if sU < -TOL:
            viol_upper.append(r)
    chain_hold = sum(1 for r in full
                     if r["l2T3"] <= r["l2TG"] + TOL and r["l2TG"] <= r["l2G"] + TOL)

    # tightest ratios (closest to 1) among nontrivial
    def tightest(num_key, den_key):
        best = None
        for r in full:
            num, den = r[num_key], r[den_key]
            if den > TOL and num > TOL:
                ratio = num / den
                if best is None or ratio > best[0]:
                    best = (ratio, r)
        return best

    tl = tightest("l2T3", "l2TG")
    tu = tightest("l2TG", "l2G")

    # ---- correlations among the three λ₂ ----
    xs = [r["l2G"] for r in full]
    ys = [r["l2TG"] for r in full]
    zs = [r["l2T3"] for r in full]
    cor = {
        ("λ₂(G)", "λ₂(T(G))"): _pearson(xs, ys),
        ("λ₂(G)", "λ₂(T3(K))"): _pearson(xs, zs),
        ("λ₂(T(G))", "λ₂(T3(K))"): _pearson(ys, zs),
    }

    # ---- family-level summary ----
    fams = {}
    for r in rows:
        fams.setdefault(r["family"], []).append(r)

    # =============================== report ===============================
    L = []
    L.append("# Simplicial hierarchy: extending T(G) to tetrahedra — `T₃(K)`\n")
    L.append("**Definition.** For a 3-dimensional simplicial complex `K`, the *tetrahedral "
             "graph* `T₃(K)` has the **triangles (2-faces) of `K`** as vertices; two triangles "
             "are adjacent iff they **share an edge and both lie in a common tetrahedron** of "
             "`K`. This is the exact dimension-shifted analogue of the triangle graph `T(G)` "
             "(whose vertices are edges, adjacent when they share a vertex and lie in a common "
             "triangle).\n")
    L.append("**Dimensional ladder of algebraic connectivities:**\n")
    L.append("| level | graph | vertices are | adjacency via | λ₂ |")
    L.append("|---|---|---|---|---|")
    L.append("| 0→1 | `G` (1-skeleton) | vertices | edges | `λ₂(G)` |")
    L.append("| 1→2 | `T(G)` | edges | triangles | `λ₂(T(G))` |")
    L.append("| 2→3 | `T₃(K)` | triangles | tetrahedra | `λ₂(T₃(K))` |")
    L.append("")
    L.append("**Conjectured simplicial hierarchy:**  `λ₂(T₃(K)) ≤ λ₂(T(G)) ≤ λ₂(G)`.\n")

    L.append("## Test complexes\n")
    L.append(f"- Total generated: **{len(rows)}**; with all three graphs connected "
             f"(eligible for the chain): **{len(full)}**.")
    for fam in ["K_n clique", "3-sphere", "stacked 3-sphere", "random 3-complex"]:
        rs = fams.get(fam, [])
        nf = sum(1 for r in rs if r["full"])
        L.append(f"  - **{fam}**: {len(rs)} generated, {nf} fully connected.")
    L.append("")

    L.append("## Hierarchy results\n")
    L.append(f"- **Full chain `λ₂(T₃) ≤ λ₂(T(G)) ≤ λ₂(G)` holds on "
             f"{chain_hold}/{len(full)} ({100.0*chain_hold/max(1,len(full)):.2f}%).**")
    L.append(f"- **Lower link `λ₂(T₃(K)) ≤ λ₂(T(G))`** (new): "
             f"{'✅ 0 violations' if not viol_lower else f'❌ {len(viol_lower)} violations'}.")
    if tl:
        r = tl[1]
        L.append(f"  - Tightest ratio λ₂(T₃)/λ₂(T(G)) = {tl[0]:.4f} "
                 f"(`{r['name']}`, λ₂(T₃)={r['l2T3']:.4f}, λ₂(T(G))={r['l2TG']:.4f}).")
    L.append(f"- **Upper link `λ₂(T(G)) ≤ λ₂(G)`** (= Conjecture B): "
             f"{'✅ 0 violations' if not viol_upper else f'❌ {len(viol_upper)} violations'}.")
    if tu:
        r = tu[1]
        L.append(f"  - Tightest ratio λ₂(T(G))/λ₂(G) = {tu[0]:.4f} "
                 f"(`{r['name']}`, λ₂(T(G))={r['l2TG']:.4f}, λ₂(G)={r['l2G']:.4f}).")
    L.append("")

    if viol_lower or viol_upper:
        L.append("### Violations\n")
        for r in viol_lower[:20]:
            L.append(f"- **lower-link** `{r['name']}` ({r['family']}): "
                     f"λ₂(T₃)={r['l2T3']:.4f} > λ₂(T(G))={r['l2TG']:.4f} "
                     f"(λ₂(G)={r['l2G']:.4f}); V={r['nV']} E={r['nE']} "
                     f"Tri={r['nTri']} Tet={r['nTet']}.")
        for r in viol_upper[:20]:
            L.append(f"- **upper-link** `{r['name']}` ({r['family']}): "
                     f"λ₂(T(G))={r['l2TG']:.4f} > λ₂(G)={r['l2G']:.4f}.")
        L.append("")

    L.append("## Correlations (Pearson) among the three λ₂\n")
    L.append("| pair | r |")
    L.append("|---|---|")
    for (a, b), v in cor.items():
        L.append(f"| {a} vs {b} | {v:.4f} |")
    L.append("")

    # ---- worked examples ----
    L.append("## Worked examples\n")
    L.append("### Complete clique complexes `K_n` (T(G)=J(n,2), T₃(K)=J(n,3))\n")
    L.append("| complex | V | E | Tri | Tet | λ₂(G) | λ₂(T(G)) | λ₂(T₃(K)) | chain |")
    L.append("|---|---|---|---|---|---|---|---|---|")
    for r in fams.get("K_n clique", []):
        ch = "✅" if (r["full"] and r["l2T3"] <= r["l2TG"] + TOL
                     and r["l2TG"] <= r["l2G"] + TOL) else "—"
        L.append(f"| {r['name']} | {r['nV']} | {r['nE']} | {r['nTri']} | {r['nTet']} | "
                 f"{r['l2G']:.3f} | {r['l2TG']:.3f} | {r['l2T3']:.3f} | {ch} |")
    L.append("")
    L.append("Johnson graphs satisfy `λ₂(J(n,k)) = n` for every `k`, so the clique complex of "
             "`K_n` gives **equality throughout**: `λ₂(T₃)=λ₂(T(G))=λ₂(G)=n`. The hierarchy is "
             "tight (ratio 1) on the densest complexes.\n")

    L.append("### Triangulated 3-spheres\n")
    L.append("| complex | V | E | Tri | Tet | λ₂(G) | λ₂(T(G)) | λ₂(T₃(K)) | chain |")
    L.append("|---|---|---|---|---|---|---|---|---|")
    for r in fams.get("3-sphere", []) + fams.get("stacked 3-sphere", [])[:8]:
        if not r["full"]:
            continue
        ch = "✅" if (r["l2T3"] <= r["l2TG"] + TOL
                     and r["l2TG"] <= r["l2G"] + TOL) else "❌"
        L.append(f"| {r['name']} | {r['nV']} | {r['nE']} | {r['nTri']} | {r['nTet']} | "
                 f"{r['l2G']:.3f} | {r['l2TG']:.3f} | {r['l2T3']:.3f} | {ch} |")
    L.append("")

    L.append("## Conclusion\n")
    if not viol_lower and not viol_upper:
        L.append("- **The simplicial hierarchy `λ₂(T₃(K)) ≤ λ₂(T(G)) ≤ λ₂(G)` holds on every "
                 f"one of the {len(full)} fully-connected test complexes** — clique complexes, "
                 "random 3-complexes, and triangulated 3-spheres alike.")
        L.append("- The new **lower link `λ₂(T₃(K)) ≤ λ₂(T(G))`** is the dimensional successor "
                 "of Conjecture B; empirically it behaves the same way (no counterexample), "
                 "suggesting a general *spectral monotonicity up the simplicial ladder*: "
                 "algebraic connectivity does not increase as you pass from `k`-faces to "
                 "`(k+1)`-faces via shared-facet/common-cofacet adjacency.")
    else:
        L.append(f"- The hierarchy **fails** on some complexes "
                 f"(lower-link viol={len(viol_lower)}, upper-link viol={len(viol_upper)}); "
                 "see the Violations section.")
    L.append("- Equality is attained by the densest complexes (complete clique complexes, "
             "Johnson graphs, λ₂ = n at every level).")
    L.append("")
    L.append("## Caveats\n")
    L.append("- Exploration only — clique complexes (n=5..8), ~600 random 3-complexes, and a "
             "family of triangulated 3-spheres (boundary of the 4-simplex, the 16-cell, and "
             "stacked spheres). Not a census; no proofs.")
    L.append("- `T(G)` uses the existing graph definition (3-cliques of the 1-skeleton); "
             "`T₃(K)` uses `K`'s actual 2-faces and tetrahedra. Both coincide with the "
             "simplicial faces for clique complexes. `λ₂` numerical (`eigvalsh`), tol 1e-9.\n")

    report = "\n".join(L) + "\n"
    out = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                       "informal", "simplicial_hierarchy_T3.md")
    with open(out, "w", encoding="utf-8") as f:
        f.write(report)

    # ---- console summary ----
    print(f"Generated {len(rows)} complexes; {len(full)} fully connected.")
    print(f"Chain lambda2(T3)<=lambda2(T(G))<=lambda2(G): "
          f"{chain_hold}/{len(full)} hold")
    print(f"  lower-link viol (T3<=TG): {len(viol_lower)}; "
          f"upper-link viol (TG<=G): {len(viol_upper)}")
    if tl:
        print(f"  tightest lower ratio lambda2(T3)/lambda2(TG) = {tl[0]:.4f} at {tl[1]['name']}")
    ascii_cor = {"l2G|l2TG": cor[("λ₂(G)", "λ₂(T(G))")],
                 "l2G|l2T3": cor[("λ₂(G)", "λ₂(T3(K))")],
                 "l2TG|l2T3": cor[("λ₂(T(G))", "λ₂(T3(K))")]}
    print("  correlations:", {k: round(v, 3) for k, v in ascii_cor.items()})
    print("  K_n clique (should be equal = n):")
    for r in fams.get("K_n clique", []):
        print(f"    {r['name']}: l2G={r['l2G']:.3f} l2TG={r['l2TG']:.3f} l2T3={r['l2T3']:.3f}")
    print(f"report written to: {out}")


if __name__ == "__main__":
    main()
