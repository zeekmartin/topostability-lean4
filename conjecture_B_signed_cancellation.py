"""
Signed cancellation for C >= -lam. C = Sum_e(d_h-d_l)f_h(f_h-f_l); C/lam = d_eff - E_mu[min].
TASK 1: C+lam = Sum_e(f_h-f_l)[(d_h-d_l)f_h+(f_h-f_l)]; complete-square = CS (fails) -> need global.
TASK 2: bad edges f_h(f_h-f_l)<0; mass vs Dirichlet.
TASK 3: vertex split P/N (d_v^2 vs s_v); negative mass vs I.
TASK 4: sharp constant inf C/lam, extremal family.
Also: is C>=-lam spectral? (test arbitrary f).
Run: python conjecture_B_signed_cancellation.py
"""
import numpy as np
import networkx as nx


def pieces(G, f=None):
    G = nx.convert_node_labels_to_integers(G); n = G.number_of_nodes()
    if not nx.is_connected(G): return None
    Am = nx.to_numpy_array(G); d = Am.sum(1); L = np.diag(d) - Am
    ev, U = np.linalg.eigh(L); lam2 = ev[1]
    if f is None: f = U[:, 1]
    f = f / np.linalg.norm(f)
    edges = [(i, j) for i in range(n) for j in range(i + 1, n) if Am[i, j] > 0]
    lam = sum((f[a] - f[b]) ** 2 for a, b in edges)
    C = 0.0; bad_mass = 0.0; I = 0.0
    for a, b in edges:
        h, l = (a, b) if d[a] >= d[b] else (b, a)
        delta = d[h] - d[l]; g = f[h] - f[l]
        C += delta * f[h] * g
        I += delta * g ** 2
        if f[h] * (f[h] - f[l]) < 0: bad_mass += g ** 2     # Dirichlet on bad edges
    s = Am @ d
    A = float(((d ** 2 - s) * f ** 2).sum())
    negmass = float(((d ** 2 - s) * f ** 2)[(d ** 2 - s) < 0].sum())   # negative vertex mass (N)
    return dict(n=n, lam=lam, C=C, A=A, I=I, negmass=negmass, bad_mass=bad_mass,
                C_over_lam=C / lam if lam > 0 else 0.0,
                d_eff=float(d @ (f * f)))


def main():
    rng = np.random.default_rng(0)

    print("=" * 92)
    print("Is C>=-lam SPECTRAL? (test C>=-Sum g^2 for ARBITRARY f, not eigenvector)")
    print("=" * 92)
    fail = 0; tot = 0; worst = 1e9
    for nn in [20, 30, 40]:
        for q in [0.3, 0.5, 0.7]:
            G = nx.gnp_random_graph(nn, q, seed=int(rng.integers(1e9)))
            if not nx.is_connected(G): continue
            for _ in range(60):
                p = pieces(G, f=rng.standard_normal(nn)); tot += 1
                if p['C_over_lam'] < -1 - 1e-7: fail += 1; worst = min(worst, p['C_over_lam'])
    print(f"  arbitrary f: C>=-lam holds {tot-fail}/{tot}; worst C/lam = {worst:.3f}")
    print(f"  => {'SPECTRAL (fails for arbitrary f; eigenvector essential).' if fail else 'holds for all f (NOT spectral!)'}")

    def d2(nn, q, s):
        H = nx.gnp_random_graph(nn - 1, q, seed=s); H.add_node(nn - 1); H.add_edge(nn - 1, 0); H.add_edge(nn - 1, 1); return H
    def deg_k_into_dense(nn, q, k, s):  # one degree-k vertex into dense core
        H = nx.gnp_random_graph(nn - 1, q, seed=s); H.add_node(nn - 1)
        for w in range(k): H.add_edge(nn - 1, w)
        return H

    print("\n" + "=" * 92)
    print("TASK 4 — sharp constant: scan inf C/lam (extremal family search)")
    print("=" * 92)
    best = (0.0, "")
    rows = []
    for nn in [40, 80, 120, 160]:
        for q in [0.1, 0.2, 0.3, 0.4, 0.5]:
            G = d2(nn, q, 7)
            if not nx.is_connected(G): continue
            p = pieces(G)
            rows.append((f"deg2d{nn}_{q}", p['C_over_lam']))
            if p['C_over_lam'] < best[0]: best = (p['C_over_lam'], f"deg2d{nn}_{q}")
    for nn in [60, 100]:
        for k in [2, 3, 4]:
            for q in [0.2, 0.4]:
                G = deg_k_into_dense(nn, q, k, 7)
                if not nx.is_connected(G): continue
                p = pieces(G)
                rows.append((f"deg{k}into{nn}_{q}", p['C_over_lam']))
                if p['C_over_lam'] < best[0]: best = (p['C_over_lam'], f"deg{k}into{nn}_{q}")
    for nm, r in sorted(rows, key=lambda x: x[1])[:14]:
        print(f"  {nm:18s} C/lam = {r:.4f}")
    print(f"  EMPIRICAL inf C/lam = {best[0]:.4f} at {best[1]}  (leaf needs >= -1)")

    print("\n" + "=" * 92)
    print("TASK 4b — does inf approach a limit as N grows? (fixed family)")
    print("=" * 92)
    for q in [0.2, 0.3]:
        seq = []
        for nn in [40, 80, 120, 160, 220]:
            G = d2(nn, q, 7)
            if nx.is_connected(G): seq.append((nn, pieces(G)['C_over_lam']))
        print(f"  deg2dense q={q}: " + "  ".join(f"N={nn}:{r:.3f}" for nn, r in seq))

    print("\n" + "=" * 92)
    print("TASK 2/3 — structure: bad-edge Dirichlet mass; negative vertex mass vs I")
    print("=" * 92)
    print(f"  {'graph':14s} {'C/lam':>8} {'bad_mass/lam':>12} {'negmass/lam':>12} {'I/lam':>8}")
    for nn in [80]:
        for q in [0.2, 0.3, 0.5]:
            G = d2(nn, q, 7); p = pieces(G)
            print(f"  deg2d{nn}_{q:<8} {p['C_over_lam']:8.4f} {p['bad_mass']/p['lam']:12.4f} "
                  f"{p['negmass']/p['lam']:12.4f} {p['I']/p['lam']:8.4f}")
    print("  (negmass = Sum_{v: d_v^2<s_v}(d_v^2-s_v)f_v^2 <=0; I>=0 must compensate within O(lam))")

    print("\n" + "=" * 92)
    print("SUMMARY")
    print("=" * 92)
    print(f"  inf C/lam (empirical) = {best[0]:.4f} at {best[1]}; leaf threshold = -1.")
    print(f"  margin to -1: {best[0]-(-1):.4f}. C>=-lam is spectral (fails for arbitrary f).")


if __name__ == "__main__":
    main()
