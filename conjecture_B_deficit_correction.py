"""
Strengthened triangle-Poincare deficit vs the required correction.
T = fᵀL_t f (real triangles).  B  ⟺  Deficit ≥ Required, where
  Deficit  = λ₂ fᵀDf − T            (aggregate-Poincare surplus, ≥0)
  Required = λ₂(λ₂ + S²/m − fᵀDf)    (= λ₂(S²/m − fᵀAf),  fᵀAf = fᵀDf − λ₂)
Identity: Deficit − Required = RHS − T  (the actual-triangle slack), so
  ratio = Deficit/Required = 1 + (RHS−T)/Required.
Per-apex: Deficit = Σ_c (λ₂·mass_c − energy_c),  mass_c=Σ_{v∈N(c)}f_v², energy_c=E_{G[N(c)]}.
Run:  python conjecture_B_deficit_correction.py
"""
import numpy as np
import networkx as nx
import counterexample_search as ce


def deg2dense(n, q, seed):
    rng = np.random.default_rng(seed)
    G = nx.gnp_random_graph(n - 1, q, seed=int(rng.integers(0, 2**31)))
    G = nx.relabel_nodes(G, {i: i + 1 for i in range(n - 1)}); G.add_node(0)
    for b in rng.choice(range(1, n), size=2, replace=False):
        G.add_edge(0, int(b))
    return G


def quant(G):
    nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}; n = len(nodes)
    L = nx.laplacian_matrix(G, nodelist=nodes).toarray().astype(float)
    d = L.diagonal().copy(); A = np.diag(d) - L; m = int(G.number_of_edges())
    ev, V = np.linalg.eigh(L); l2 = float(ev[1]); f = V[:, 1] / np.linalg.norm(V[:, 1])
    fDf = float((d * f * f).sum()); S = float(d @ f)
    A2 = A @ A; W = A * A2; Lt = np.diag(W @ np.ones(n)) - W
    T = float(f @ Lt @ f)
    RHS = l2 * (2 * fDf - l2 - S * S / m)
    Deficit = l2 * fDf - T
    Required = l2 * (l2 + S * S / m - fDf)
    return dict(n=n, m=m, l2=l2, fDf=fDf, S=S, T=T, RHS=RHS,
                Deficit=Deficit, Required=Required, fAf=fDf - l2, S2m=S * S / m,
                idx=idx, d=d, A=A, f=f, nodes=nodes)


def corpus(maxn=9):
    seen = {}
    for tag, exh, G in ce._gen_graphs_hier(maxn):
        if G.number_of_nodes() < 3 or not nx.is_connected(G):
            continue
        Tg = ce.triangle_graph(G)
        if Tg.number_of_nodes() < 2 or not nx.is_connected(Tg):
            continue
        key = (G.number_of_nodes(), G.number_of_edges(),
               nx.weisfeiler_lehman_graph_hash(G, iterations=3))
        if key not in seen:
            seen[key] = G.copy()
    return list(seen.values())


def per_apex(r):
    """return arrays of (mass_c, energy_c, d_c) over apexes c."""
    G = nx.from_numpy_array(r["A"]); f = r["f"]; d = r["d"]; n = r["n"]
    mass = np.zeros(n); energy = np.zeros(n)
    for c in range(n):
        Nc = list(G.neighbors(c))
        mass[c] = sum(f[v] ** 2 for v in Nc)
        e = 0.0
        for x in range(len(Nc)):
            for y in range(x + 1, len(Nc)):
                if r["A"][Nc[x], Nc[y]] > 0.5:
                    e += (f[Nc[x]] - f[Nc[y]]) ** 2
        energy[c] = e
    return mass, energy, d


def main():
    print("===== TASK 1: Deficit vs Required at scale (ratio must be ≥1) =====")
    rows = [quant(G) for G in corpus(9)]
    rows = [r for r in rows if r["l2"] > 1e-6]
    # corpus: where Required>0 (the nontrivial case)
    pos = [r for r in rows if r["Required"] > 1e-9]
    print(f"  corpus n≤9: {len(rows)} graphs; Required>0 on {len(pos)} (else B trivial)")
    if pos:
        rr = np.array([r["Deficit"] / r["Required"] for r in pos])
        print(f"    ratio Deficit/Required: min={rr.min():.4f} median={np.median(rr):.3f} "
              f"(≥1 on {int(np.sum(rr>=1-1e-9))}/{len(pos)})")
    print("  deg2+dense (the binding family):")
    print("     n   | Deficit | Required | ratio | margin (Def-Req)/Def | RHS-T")
    for n in (50, 100, 200, 500, 1000):
        best = None
        for s in range(5 if n <= 200 else 2):
            G = deg2dense(n, 0.65, seed=300 + n + s)
            if not nx.is_connected(G):
                continue
            r = quant(G)
            if r["Required"] > 1e-9:
                ratio = r["Deficit"] / r["Required"]
                if best is None or ratio < best[0]:
                    best = (ratio, r)
        if best:
            ratio, r = best
            print(f"    {n:5d} | {r['Deficit']:7.3f} | {r['Required']:8.3f} | {ratio:5.3f} | "
                  f"{(r['Deficit']-r['Required'])/r['Deficit']:8.4f} | {r['RHS']-r['T']:.4f}")

    print("\n===== TASK 3: Required_correction structure on deg2+dense =====")
    print("     n   | fᵀAf=fDf-λ₂ | S²/m | S²/m - fᵀAf | λ₂ | Required=λ₂(S²/m-fᵀAf)")
    for n in (50, 100, 200, 500, 1000):
        G = deg2dense(n, 0.65, seed=300 + n)
        if not nx.is_connected(G):
            continue
        r = quant(G)
        print(f"    {n:5d} | {r['fAf']:11.4f} | {r['S2m']:.4f} | {r['S2m']-r['fAf']:11.4f} | "
              f"{r['l2']:.3f} | {r['Required']:.4f}")

    print("\n===== TASK 2: per-apex decomposition (surplus λ₂·mass_c − energy_c) =====")
    for n in (50, 100, 200):
        G = deg2dense(n, 0.65, seed=300 + n)
        if not nx.is_connected(G):
            continue
        r = quant(G)
        mass, energy, d = per_apex(r); l2 = r["l2"]
        surplus = l2 * mass - energy
        med = np.median(d)
        fail = surplus < -1e-12                 # local Poincare fails here
        tot_surplus = float(surplus[surplus > 0].sum())
        tot_overshoot = float(-surplus[fail].sum())
        print(f"  n={n}: local Poincare fails on {int(fail.sum())}/{n} apexes "
              f"({100*fail.mean():.0f}%); Σsurplus⁺={tot_surplus:.3f} Σovershoot={tot_overshoot:.3f} "
              f"net Deficit={surplus.sum():.3f}")
        dense = d > med; low = ~dense
        print(f"     dense apexes (d>med): Σsurplus={surplus[dense].sum():.3f} "
              f"(fails {int((fail&dense).sum())}); low apexes: Σsurplus={surplus[low].sum():.3f} "
              f"(fails {int((fail&low).sum())})")
        # which apex carries the most overshoot / where is Required produced
        worst = int(np.argmin(surplus))
        print(f"     most-overshooting apex: degree {int(d[worst])} (min deg={int(d.min())}), "
              f"surplus={surplus[worst]:.3f}")

    print("\n===== TASK 4: decisive — does ratio stay bounded away from 1? =====")
    print("  deg2+dense ratio Deficit/Required by n (min over samples):")
    trend = []
    for n in (50, 100, 200, 400, 700, 1000):
        rs = []
        for s in range(6 if n <= 200 else 3):
            G = deg2dense(n, 0.65, seed=500 + n + 11 * s)
            if not nx.is_connected(G):
                continue
            r = quant(G)
            if r["Required"] > 1e-9:
                rs.append(r["Deficit"] / r["Required"])
        if rs:
            trend.append((n, min(rs), np.mean(rs)))
            print(f"    n={n:5d}: min ratio={min(rs):.4f}  mean={np.mean(rs):.4f}")
    if len(trend) >= 2:
        verdict = ("→ 1 (asymptotically exact; needs minimality)"
                   if trend[-1][1] < 1.15 and trend[-1][1] < trend[0][1]
                   else "bounded away from 1 (Poincare surplus suffices)")
        print(f"  VERDICT: ratio {verdict}")


if __name__ == "__main__":
    main()
