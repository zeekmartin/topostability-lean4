"""
TYPE A extremal family: v0 attached to two LOW-degree ports a,b into a dense/complete bulk.

Core H = K_N (complete bulk) + a + b, where a,b each attach to exactly d bulk vertices
(overlap s = |common bulk neighbours|, optionally a~b). G = H + v0, v0~{a,b}.
Take N -> inf; compute gap, eff, gap/eff. Compare to random dense-core values
(d=2 -> 0.68, d=3 -> 1.20, d=4 -> 1.63).
Run: python conjecture_B_typeA_low_degree_ports.py
"""
import numpy as np
import networkx as nx


def build_model(N, d, s, ab=False):
    """K_N bulk + ports a,b (degree d each, overlap s) + v0~{a,b}."""
    if 2 * d - s > N: return None
    H = nx.complete_graph(N)
    a, b, v0 = N, N + 1, N + 2
    H.add_node(a); H.add_node(b)
    common = list(range(s)); aonly = list(range(s, d)); bonly = list(range(d, 2 * d - s))
    for u in common + aonly: H.add_edge(a, u)
    for u in common + bonly: H.add_edge(b, u)
    if ab: H.add_edge(a, b)
    G = nx.Graph(H); G.add_node(v0); G.add_edge(v0, a); G.add_edge(v0, b)
    return G, H, a, b, v0


def metrics(N, d, s, ab=False):
    res = build_model(N, d, s, ab)
    if res is None: return None
    G, H, a, b, v0 = res
    nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}
    A = nx.to_numpy_array(G, nodelist=nodes); dg = A.sum(1); L = np.diag(dg) - A
    ev, U = np.linalg.eigh(L); lam = ev[1]; f = U[:, 1]; f = f / np.linalg.norm(f)
    iv = idx[v0]
    if f[iv] < 0: f = -f
    m = G.number_of_edges(); S = float(dg @ f)
    Gsum = sum((f[idx[u]] + f[idx[v]]) ** 2 for u, v in G.edges())
    B2 = sum((min(dg[idx[u]], dg[idx[v]]) - 1) * (f[idx[u]] - f[idx[v]]) ** 2 for u, v in G.edges())
    gap = lam * (Gsum - S ** 2 / m) - B2
    Hn = list(H.nodes()); Hidx = {u: i for i, u in enumerate(Hn)}
    LH = nx.laplacian_matrix(H, nodelist=Hn).toarray().astype(float)
    mu, phi = np.linalg.eigh(LH); gamma = float(mu[1])
    if gamma - lam <= 1e-9: return None
    inv = 1.0 / (mu[1:] - lam); R = (phi[:, 1:] * inv) @ phi[:, 1:].T
    ia, ib = Hidx[a], Hidx[b]
    eff = float(R[ia, ia] + R[ib, ib] - 2 * R[ia, ib])
    return dict(N=N, d=d, s=s, ab=ab, lam=lam, gamma=gamma, gap=gap, eff=eff,
                goe=gap / eff, fv0=float(f[iv]) ** 2)


def main():
    print("=" * 92)
    print("TASK 1/3/4 — complete-bulk low-degree ports: gap/eff as N->inf, vs random (0.68/1.20/1.63)")
    print("=" * 92)
    rand = {2: 0.68, 3: 1.20, 4: 1.63}
    for d in [1, 2, 3, 4, 5]:
        for s in [0, min(1, d), d]:
            if s > d: continue
            row = []
            for N in [30, 60, 120, 240, 480]:
                r = metrics(N, d, s, ab=False)
                row.append(r['goe'] if r else None)
            lim = row[-1]
            tag = f"  (random d={d}: {rand[d]})" if (s == 0 and d in rand) else ""
            vals = " ".join(f"{g:6.3f}" if g else "  --  " for g in row)
            print(f"  d={d} s={s} ab=F: N=30..480 goe = {vals}  -> {lim}{tag}")

    print("\n" + "=" * 92)
    print("TASK 1b — effect of a~b (adjacent ports) and overlap s, at N=480")
    print("=" * 92)
    print(f"  {'d':>3} {'s':>3} {'ab':>5} {'lam':>7} {'gamma':>8} {'gap':>9} {'eff':>9} {'goe':>8} {'fv0^2':>7}")
    for d in [2, 3, 4]:
        for s in range(0, d + 1):
            for ab in [False, True]:
                r = metrics(480, d, s, ab=ab)
                if r:
                    print(f"  {d:3d} {s:3d} {str(ab):>5} {r['lam']:7.4f} {r['gamma']:8.3f} "
                          f"{r['gap']:9.5f} {r['eff']:9.4f} {r['goe']:8.4f} {r['fv0']:7.3f}")

    print("\n" + "=" * 92)
    print("TASK 3 — minimum g_{d,s} = lim gap/eff (N=480), and the minimizing (d,s,ab)")
    print("=" * 92)
    best = None
    for d in [1, 2, 3, 4, 5, 6]:
        for s in range(0, d + 1):
            for ab in [False, True]:
                r = metrics(480, d, s, ab=ab)
                if r and r['fv0'] > 0.3:
                    if best is None or r['goe'] < best['goe']:
                        best = r
    if best:
        print(f"  min gap/eff over (d,s,ab) at N=480: {best['goe']:.4f} at "
              f"d={best['d']} s={best['s']} ab={best['ab']} (lam={best['lam']:.3f} gamma={best['gamma']:.2f})")
    # scan g_d for d=2..6 (s=0, the disjoint-port case)
    print("  g_d (disjoint ports s=0, ab=F, N=480):")
    for d in [1, 2, 3, 4, 5, 6, 8, 12]:
        r = metrics(480, d, 0, ab=False)
        if r: print(f"    d={d:2d}: gap/eff={r['goe']:.4f}  gap={r['gap']:.4f}  eff={r['eff']:.4f}")

    print("\n" + "=" * 92)
    print("TASK 4 — does complete-bulk model match random gnp(.5) fixed-degree values?")
    print("=" * 92)
    print("  random gnp(.5) fixed-degree (from prior round): d=2->0.68, d=3->1.20, d=4->1.63")
    for d in [2, 3, 4]:
        r0 = metrics(480, d, 0); r1 = metrics(480, d, 1) if d >= 1 else None
        print(f"  d={d}: complete-bulk s=0 -> {r0['goe']:.3f}; s=1 -> "
              f"{r1['goe'] if r1 else '--':.3f}; random -> {rand[d]}")


if __name__ == "__main__":
    main()
