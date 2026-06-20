"""
TYPE A asymptotic proof attempt: test the proposed argument honestly.

Proposed (user): for min(d_a,d_b) >= D0,  f_a ~ x/d_a -> 0,  C_attach -> 0,  gap -> R'' > 0.
We verify each claim. Key decisive test: FIX attachment degree low while n -> inf (does gap/eff stay
low = persistent minimizer, or rise = finite-size?).
Run: python conjecture_B_typeA_asymptotic_proof.py
"""
import numpy as np
import networkx as nx


def analyze(H, a, b):
    H = nx.convert_node_labels_to_integers(H); N = H.number_of_nodes()
    if not nx.is_connected(H) or a == b: return None
    G = nx.Graph(H); G.add_node(N); G.add_edge(N, a); G.add_edge(N, b)
    nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}
    A = nx.to_numpy_array(G, nodelist=nodes); d = A.sum(1); L = np.diag(d) - A
    ev, U = np.linalg.eigh(L); lam = ev[1]; f = U[:, 1]; f = f / np.linalg.norm(f)
    v0 = idx[N]
    if f[v0] < 0: f = -f
    m = G.number_of_edges(); S = float(d @ f); fDf = float(d @ (f * f))
    x = float(f[v0]); fa = float(f[idx[a]]); fb = float(f[idx[b]])
    Gsum = sum((f[idx[u]] + f[idx[v]]) ** 2 for u, v in G.edges())
    B2 = sum((min(d[idx[u]], d[idx[v]]) - 1) * (f[idx[u]] - f[idx[v]]) ** 2 for u, v in G.edges())
    gap = lam * (Gsum - S ** 2 / m) - B2
    da, db = float(d[idx[a]]), float(d[idx[b]])
    Catt = (da - 2) * fa * (fa - x) + (db - 2) * fb * (fb - x)
    Rpp = lam * (fDf - lam + 1 - S ** 2 / m)
    LH = nx.laplacian_matrix(H, nodelist=list(range(N))).toarray().astype(float)
    mu, phi = np.linalg.eigh(LH); gamma = float(mu[1])
    if gamma - lam <= 1e-9: return None
    inv = 1.0 / (mu[1:] - lam); R = (phi[:, 1:] * inv) @ phi[:, 1:].T
    eff = float(R[a, a] + R[b, b] - 2 * R[a, b])
    return dict(N=N, n=N + 1, m=m, lam=lam, gamma=gamma, x=x, fa=fa, fb=fb,
                da_core=int(LH[a, a]), db_core=int(LH[b, b]), Catt=Catt, Rpp=Rpp, gap=gap,
                eff=eff, goe=gap / eff, fv0sq=x ** 2)


def fix_degree(H, a, deg, rng):
    """Reduce vertex a's degree to `deg` by removing random incident edges (keep connected)."""
    H = H.copy()
    nb = list(H.neighbors(a))
    rng.shuffle(nb)
    while H.degree(a) > deg and nb:
        u = nb.pop()
        H.remove_edge(a, u)
        if not nx.is_connected(H):
            H.add_edge(a, u)
    return H


def main():
    print("=" * 96)
    print("TASK 1a — does C_attach -> 0 ?  (claim) vs  C_attach = O(1) ?  (dense gnp, q fixed, n grows)")
    print("=" * 96)
    print(f"  {'n':>5} {'q':>5} {'lam':>6} {'gamma':>7} {'fa':>9} {'x/gamma':>9} {'fa*da':>8} "
          f"{'C_attach':>9} {'Rpp':>8} {'gap':>9} {'goe':>7}")
    for q in [0.5]:
        for n in [40, 70, 120, 200, 320]:
            r = analyze(nx.gnp_random_graph(n, q, seed=7), 0, 1)
            if r:
                print(f"  {n:5d} {q:5.2f} {r['lam']:6.3f} {r['gamma']:7.2f} {r['fa']:9.5f} "
                      f"{r['x']/r['gamma']:9.5f} {r['fa']*r['da_core']:8.4f} {r['Catt']:9.4f} "
                      f"{r['Rpp']:8.4f} {r['gap']:9.5f} {r['goe']:7.3f}")
    print("  => f_a ~ x/gamma (NOT x/d_a^2); C_attach ~ O(1) (NOT ->0); gap ->0 (R'' & C_att cancel);")
    print("     but gap/eff -> c(q) = O(1) bounded. The proposed 'C_attach->0, gap->R''' is FALSE.")

    print("\n" + "=" * 96)
    print("TASK 1b — CORRECT object: gap/eff -> c(q). Does it stabilize >0 as n grows? (per q)")
    print("=" * 96)
    print(f"  {'q':>5} " + " ".join(f"n={n}" for n in [40, 80, 160, 320]))
    for q in [0.3, 0.5, 0.7, 0.9]:
        row = []
        for n in [40, 80, 160, 320]:
            r = analyze(nx.gnp_random_graph(n, q, seed=11), 0, 1)
            row.append(f"{r['goe']:.2f}" if r else " - ")
        print(f"  {q:5.2f} " + "   ".join(row))

    print("\n" + "=" * 96)
    print("TASK 1c — DECISIVE: FIX attachment degree low (deg=3,5) on a growing dense gnp(.5) core")
    print("=" * 96)
    rng = np.random.default_rng(3)
    for deg in [3, 5, 8]:
        print(f"  fixed attachment degree = {deg}:")
        for n in [40, 80, 160, 300]:
            H = nx.gnp_random_graph(n, 0.5, seed=5)
            if not nx.is_connected(H): continue
            H = fix_degree(H, 0, deg, rng); H = fix_degree(H, 1, deg, rng)
            r = analyze(H, 0, 1)
            if r:
                print(f"    n={n:4d}: da={r['da_core']} db={r['db_core']} lam={r['lam']:.3f} "
                      f"gamma={r['gamma']:.2f} gap={r['gap']:.5f} eff={r['eff']:.3f} goe={r['goe']:.3f}")
    print("  (if goe stays low for FIXED low degree as n grows => persistent minimizer family;")
    print("   if goe rises => the low-degree-attachment minima are finite-size only.)")

    print("\n" + "=" * 96)
    print("TASK 2 — finite verification: TYPE A graphs with gap/eff < 5, by n")
    print("=" * 96)
    rng = np.random.default_rng(0); below = []
    maxn_below = 0
    for n in range(8, 41):
        for q in [0.25, 0.35, 0.5, 0.65, 0.8]:
            for s in range(2):
                H = nx.gnp_random_graph(n, q, seed=int(rng.integers(1e9)))
                Hc = nx.convert_node_labels_to_integers(H)
                if not nx.is_connected(Hc): continue
                deg = dict(Hc.degree()); lo = sorted(deg, key=lambda u: deg[u])
                for a, b in [(0, 1), (lo[0], lo[1]), (lo[0], sorted(deg, key=lambda u:-deg[u])[0])]:
                    r = analyze(Hc, a, b)
                    if r and r['fv0sq'] > 0.3 and r['goe'] < 5.0:
                        below.append((n, round(r['goe'], 3), round(r['lam'], 2),
                                      r['da_core'], r['db_core']))
                        maxn_below = max(maxn_below, n)
    below.sort()
    print(f"  TYPE A graphs found with gap/eff < 5: {len(below)}; largest n with gap/eff<5: {maxn_below}")
    print(f"  smallest gap/eff: {min(b[1] for b in below) if below else 'n/a'}")
    # distribution of n for the <5 cases
    from collections import Counter
    cn = Counter(b[0] for b in below)
    print(f"  count by n (gap/eff<5): {dict(sorted(cn.items()))}")
    print(f"  fraction of <5 cases with low attach degree min(da,db)<=4: "
          f"{sum(1 for b in below if min(b[3],b[4])<=4)}/{len(below)}")

    print("\n" + "=" * 96)
    print("SUMMARY")
    print("=" * 96)
    print("  Honest verdict on the proposed asymptotic argument and the finite-verification bound.")


if __name__ == "__main__":
    main()
