"""
Universality of the scalar reduction  fᵀDf + Σ_H f² ≥ λ₂ + S²/m  (⟺ Σ_H f² ≥ R),
R = Required/λ₂ = λ₂ + S²/m - fᵀDf.  Test across Required>0 families and H definitions.
Run:  python conjecture_B_scalar_universal.py
"""
import numpy as np
import networkx as nx


def deg2dense(n, q, seed):
    rng = np.random.default_rng(seed)
    G = nx.gnp_random_graph(n - 1, q, seed=int(rng.integers(0, 2**31)))
    G = nx.relabel_nodes(G, {i: i + 1 for i in range(n - 1)}); G.add_node(0)
    for b in rng.choice(range(1, n), size=2, replace=False):
        G.add_edge(0, int(b))
    return G


def info(G):
    nodes = list(G.nodes()); n = len(nodes)
    L = nx.laplacian_matrix(G, nodelist=nodes).toarray().astype(float)
    d = L.diagonal(); A = np.diag(d) - L; m = G.number_of_edges()
    ev, V = np.linalg.eigh(L); l2 = ev[1]
    if l2 < 1e-9:
        return None
    f = V[:, 1] / np.linalg.norm(V[:, 1]); fDf = float((d * f * f).sum()); S = float(d @ f)
    R = l2 + S * S / m - fDf; Req = l2 * R
    if Req <= 1e-9:
        return None
    f2 = np.sort(f * f)[::-1]; cum = np.cumsum(f2)
    H = {'top1': float(f2[0]), 'top5': float(f2[:5].sum()),
         'H80': float(f2[:1 + int(np.searchsorted(cum, 0.8))].sum()),
         'H90': float(f2[:1 + int(np.searchsorted(cum, 0.9))].sum())}
    sz = {'H80': 1 + int(np.searchsorted(cum, 0.8)), 'H90': 1 + int(np.searchsorted(cum, 0.9))}
    marg = {k: (fDf + v) - (l2 + S * S / m) for k, v in H.items()}
    return dict(n=n, l2=l2, R=R, Req=Req, fDf=fDf, S2m=S * S / m,
                fv0_2=float(f2[0]), sz=sz, marg=marg)


def main():
    fams = [('deg2dense', [deg2dense(n, 0.65, 300 + n) for n in (50, 100, 200, 500)])]
    fams.append(('lollipop', [nx.lollipop_graph(m, Lp) for m in (20, 50) for Lp in (3, 5, 10)]))
    fams.append(('barbell', [nx.barbell_graph(m, Lp) for m in (20, 50) for Lp in (1, 3)]))
    rng = np.random.default_rng(0); rnd = []
    for _ in range(200):
        n = int(rng.integers(8, 30)); q = float(rng.uniform(0.3, 0.8))
        G = nx.gnp_random_graph(n, q, seed=int(rng.integers(0, 2**31)))
        if nx.is_connected(G):
            rnd.append(G)
    fams.append(('random', rnd))
    ap = []
    for m, k, pl in ((20, 5, 3), (30, 5, 5), (15, 8, 3)):
        G = nx.complete_graph(m); nxt = m
        for i in range(k):
            prev = i % m
            for _ in range(pl):
                G.add_edge(prev, nxt); prev = nxt; nxt += 1
        ap.append(G)
    fams.append(('appendix', ap))

    print('Required>0 families: margin_H = (sum_H f^2) - R')
    print(f"{'family':10s} {'#Req>0':>7} {'R range':>14} {'R>1':>5} {'m_top1>0':>9} "
          f"{'m_top5>0':>9} {'m_H80>0':>8} {'m_H90>0':>8}")
    for lab, gs in fams:
        rs = [info(G) for G in gs]; rs = [r for r in rs if r]
        if not rs:
            print(f"{lab:10s} {0:>7}"); continue
        Rs = [r['R'] for r in rs]
        frac = lambda k: np.mean([r['marg'][k] > 1e-9 for r in rs])
        print(f"{lab:10s} {len(rs):>7} {min(Rs):6.2f}..{max(Rs):5.2f} "
              f"{100*np.mean([x>1 for x in Rs]):4.0f}% {100*frac('top1'):8.0f}% "
              f"{100*frac('top5'):8.0f}% {100*frac('H80'):7.0f}% {100*frac('H90'):7.0f}%")

    print("\nTASK 3 lollipop detail (fv0^2, |H80|, R, margin_top1, margin_H90):")
    for m, Lp in ((20, 5), (20, 10), (50, 10)):
        r = info(nx.lollipop_graph(m, Lp))
        if r:
            print(f"  lollipop m={m} L={Lp}: fv0^2={r['fv0_2']:.3f} |H80|={r['sz']['H80']} "
                  f"R={r['R']:.3f} m_top1={r['marg']['top1']:.3f} m_H90={r['marg']['H90']:.3f}")

    print("\nTASK 4 deg2+dense Sigma_{v!=v0} d_v f_v^2 (= fDf - 2 fv0^2) vs 2q-1=0.30:")
    for n in (50, 100, 200, 500, 1000):
        G = deg2dense(n, 0.65, 300 + n); nodes = list(G.nodes())
        L = nx.laplacian_matrix(G, nodelist=nodes).toarray().astype(float); d = L.diagonal()
        ev, V = np.linalg.eigh(L); f = V[:, 1] / np.linalg.norm(V[:, 1]); v0 = int(np.argmax(f * f))
        fDf = float((d * f * f).sum()); dense_mass = fDf - d[v0] * f[v0] ** 2
        print(f"  n={n}: Sigma_dense d_v f_v^2 = {dense_mass:.4f}  (>= 0.30: {dense_mass >= 0.30})")


if __name__ == "__main__":
    main()
