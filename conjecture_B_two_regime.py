"""
Conjecture B — two-regime proof strategy.  A := fᵀDf - λ₂ (unit Fiedler f).
Identity: fᵀ(D+A)f = λ₂ + 2A. So B ⟺ fᵀL_t f ≤ λ₂(λ₂+2A)  (exact target).

Candidate upper bounds on fᵀL_t f = Σ_{ab∈E} t_ab (f_a-f_b)²  (t_ab=|N(a)∩N(b)|):
  B1 crude  : (Δ-1)·λ₂            [t_ab ≤ Δ-1];  closes B iff Δ-1 ≤ λ₂+2A
  B2 min-1  : Σ(min(d_a,d_b)-1)(f_a-f_b)²;  closes B iff ≤ λ₂(λ₂+2A)
  B3 dmax   : Δ·λ₂;               closes B iff Δ ≤ λ₂+2A
  B4 maxgrad: λ₂·Σt_ab = 3λ₂·#tri; closes iff 3#tri ≤ λ₂+2A  (expected too lossy)

Run:  python conjecture_B_two_regime.py
"""
import numpy as np
import networkx as nx
from itertools import combinations
import counterexample_search as ce

TOL = 1e-9


def quant(G, f=None):
    nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}
    edges = list(G.edges()); n, m = len(nodes), len(edges)
    L = nx.laplacian_matrix(G, nodelist=nodes).toarray().astype(float)
    d = L.diagonal().copy(); A = np.diag(d) - L
    ev, V = np.linalg.eigh(L); l2 = float(ev[1])
    if f is None:
        f = V[:, 1] / np.linalg.norm(V[:, 1])
    fDf = float((d * f * f).sum()); Aexc = fDf - l2
    fQf = float(f @ (np.diag(d) + A) @ f)            # = λ₂ + 2A
    Delta_disc = l2 * fQf                            # B-RHS = λ₂(λ₂+2A)
    fLtf = 0.0; W1 = 0.0; ntri = 0
    for u, v in edges:
        i, j = idx[u], idx[v]; g = (f[i] - f[j]) ** 2
        t = len(set(G[u]) & set(G[v]))
        fLtf += t * g; W1 += (min(d[i], d[j]) - 1) * g
    # count triangles
    for c in combinations(nodes, 3):
        if G.has_edge(c[0], c[1]) and G.has_edge(c[0], c[2]) and G.has_edge(c[1], c[2]):
            ntri += 1
    dmax = float(d.max()); dmin = float(d.min())
    return dict(n=n, m=m, l2=l2, A=Aexc, fQf=fQf, fLtf=fLtf, W1=W1,
                BRHS=l2 * fQf, ntri=ntri, dmax=dmax, dmin=dmin,
                Delta=l2 * fQf - fLtf,           # discriminant Δ = B-RHS - LHS
                ratio=fLtf / (l2 * fQf) if fQf > 0 else 0.0)


def corpus(maxn=9):
    seen = {}
    for tag, exh, G in ce._gen_graphs_hier(maxn):
        if G.number_of_nodes() < 3 or not nx.is_connected(G):
            continue
        T = ce.triangle_graph(G)
        if T.number_of_nodes() < 2 or not nx.is_connected(T):
            continue
        key = (G.number_of_nodes(), G.number_of_edges(),
               nx.weisfeiler_lehman_graph_hash(G, iterations=3))
        if key not in seen:
            seen[key] = G.copy()
    return list(seen.values())


def main():
    graphs = corpus(9)
    rows = [quant(G) for G in graphs]
    rows = [r for r in rows if r["l2"] > 1e-6]
    N = len(rows)
    Avals = np.array([r["A"] for r in rows])
    print(f"distinct corpus graphs: {N}")
    print(f"\n=== PHASE 1.1: distribution of A = fᵀDf - λ₂ ===")
    print(f"  A: min={Avals.min():.3f} median={np.median(Avals):.3f} max={Avals.max():.3f}")
    for thr in (0.5, 1.0, 1.5, 2.0, 3.0):
        print(f"   #graphs A≥{thr}: {int(np.sum(Avals>=thr))}  |  A<{thr}: {int(np.sum(Avals<thr))}")
    # gap near A=1.5? histogram
    hist, edges = np.histogram(Avals, bins=[0,0.5,1,1.25,1.5,1.75,2,3,5,1e9])
    print("  A histogram:", dict(zip([f"[{edges[i]:.2f},{edges[i+1]:.2f})" for i in range(len(hist))], hist.tolist())))

    # B always holds (it's true); confirm
    nB = sum(1 for r in rows if r["fLtf"] <= r["BRHS"] + 1e-7)
    print(f"\n  [check] B (fᵀL_t f ≤ λ₂(λ₂+2A)) holds: {nB}/{N}")

    def regime(cond):
        return [r for r in rows if cond(r)]

    for label, cond in [("A ≥ 1.5", lambda r: r["A"] >= 1.5),
                        ("A < 1.5", lambda r: r["A"] < 1.5)]:
        rs = regime(cond); n = len(rs)
        if n == 0:
            continue
        print(f"\n=== REGIME {label}: {n} graphs ===")
        # candidate bound closure rates
        b1 = sum(1 for r in rs if (r["dmax"] - 1) * r["l2"] <= r["BRHS"] + 1e-7)
        b2 = sum(1 for r in rs if r["W1"] <= r["BRHS"] + 1e-7)
        b3 = sum(1 for r in rs if r["dmax"] * r["l2"] <= r["BRHS"] + 1e-7)
        b4 = sum(1 for r in rs if 3 * r["ntri"] <= r["fQf"] + 1e-7)
        print(f"  B1 (Δ-1)λ₂ ≤ B-RHS  [⟺ d_max-1≤λ₂+2A]: {b1}/{n} ({100*b1/n:.1f}%)")
        print(f"  B2 min-1 form ≤ B-RHS                  : {b2}/{n} ({100*b2/n:.1f}%)")
        print(f"  B3 d_max·λ₂ ≤ B-RHS [⟺ d_max≤λ₂+2A]   : {b3}/{n} ({100*b3/n:.1f}%)")
        print(f"  B4 3·#tri ≤ λ₂+2A (maxgrad)            : {b4}/{n} ({100*b4/n:.1f}%)")
        # tightest LHS/RHS and the W1 relaxation ratio
        rr = np.array([r["ratio"] for r in rs])
        w1r = np.array([r["W1"] / r["BRHS"] for r in rs])
        print(f"  tightest fᵀL_t f / B-RHS: max={rr.max():.4f}  (B margin)")
        print(f"  W1 / B-RHS: max={w1r.max():.4f}  ({'min-1 relaxation CLOSES B' if w1r.max()<=1+1e-6 else 'min-1 OVERSHOOTS'})")

    # PHASE 1.3: characterize small-A (A<1.5)
    sm = regime(lambda r: r["A"] < 1.5)
    print(f"\n=== PHASE 1.3: small-A (A<1.5) structure, {len(sm)} graphs ===")
    miss = np.array([r["n"]*(r["n"]-1)//2 - r["m"] for r in sm])
    spread = np.array([r["dmax"] - r["dmin"] for r in sm])
    l2_vs_dmax = np.array([r["l2"] / (r["dmax"] - 1) for r in sm if r["dmax"] > 1])
    print(f"  complement |H|: min={miss.min()} median={int(np.median(miss))} max={miss.max()}")
    print(f"  degree spread Δ-δ: min={spread.min()} median={int(np.median(spread))} max={spread.max()} "
          f"(near-regular ≤2: {100*np.mean(spread<=2):.0f}%)")
    print(f"  λ₂/(d_max-1): min={l2_vs_dmax.min():.3f} median={np.median(l2_vs_dmax):.3f} max={l2_vs_dmax.max():.3f}")

    # PHASE 3: threshold for B1 / B3 (the clean crude bounds)
    print(f"\n=== PHASE 3: threshold analysis ===")
    # B1 closes iff A ≥ (d_max-1-λ₂)/2 =: A1*.  Report distribution of A1*.
    A1star = np.array([(r["dmax"] - 1 - r["l2"]) / 2 for r in rows])
    A3star = np.array([(r["dmax"] - r["l2"]) / 2 for r in rows])
    print(f"  B1 needs A ≥ A1*=(d_max-1-λ₂)/2: A1* median={np.median(A1star):.3f} max={A1star.max():.3f}")
    print(f"     (a uniform c works for B1 only if A ≥ max A1* = {A1star.max():.3f} on its regime — graph-dependent!)")
    # the actual A where B1 first holds: among graphs, is there c s.t. A≥c ⇒ B1?
    # find max A among B1-FAILURES (if c>that, B1 holds for A≥c)
    b1fail_A = [r["A"] for r in rows if (r["dmax"]-1)*r["l2"] > r["BRHS"]+1e-7]
    b2fail_A = [r["A"] for r in rows if r["W1"] > r["BRHS"]+1e-7]
    print(f"  B1 fails on {len(b1fail_A)} graphs; their A: "
          f"max={max(b1fail_A) if b1fail_A else float('nan'):.3f} "
          f"⇒ B1 holds for A > {max(b1fail_A) if b1fail_A else 0:.3f}")
    print(f"  B2 fails on {len(b2fail_A)} graphs; their A: "
          f"max={max(b2fail_A) if b2fail_A else float('nan'):.3f} "
          f"⇒ B2 (min-1) holds for A > {max(b2fail_A) if b2fail_A else 0:.3f}")

    # named families: A, B-RHS, LHS, which bounds close
    print(f"\n=== named graphs ===")
    for name, G in [("K_8", nx.complete_graph(8)),
                    ("K_8-e", _rm(nx.complete_graph(8), [(0,1)])),
                    ("K_8-△", _rm(nx.complete_graph(8), [(0,1),(0,2),(1,2)])),
                    ("Petersen", nx.petersen_graph()),
                    ("C5", nx.cycle_graph(5))]:
        if not nx.is_connected(G): continue
        r = quant(G)
        print(f"  {name:9s}: A={r['A']:.3f} λ₂={r['l2']:.3f} d_max={int(r['dmax'])} "
              f"LHS={r['fLtf']:.3f} B-RHS={r['BRHS']:.3f} Δ={r['Delta']:.3f} "
              f"B1ok={((r['dmax']-1)*r['l2']<=r['BRHS']+1e-7)} B2ok={(r['W1']<=r['BRHS']+1e-7)}")

    main.rows = rows


def _rm(G, es):
    G.remove_edges_from(es); return G


if __name__ == "__main__":
    main()
