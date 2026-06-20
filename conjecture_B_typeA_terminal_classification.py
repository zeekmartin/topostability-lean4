"""
TYPE A classification by TERMINAL response (attachment-vertex resolvent), not core structure.

G = H + v0 (v0~{a,b}). R = (L_H - lam)^{-1} on 1_H^perp; R2 block at a,b.
Terminal variables:
  gamma=lam2(H), Delta, delta
  eff_lambda = (e_a-e_b)^T R (e_a-e_b) = Raa+Rbb-2Rab    (R_minus = eff/2)
  R_plus     = 1^T R2 1 = Raa+Rbb+2Rab                    (symmetric, secular)
  terminal_leverage = Raa+Rbb
  asymmetry  = |Raa-Rbb|
  common_defect = (N-2) - |N_H(a) cap N_H(b)|
  bottleneck ratio lam/gamma
Question: what controls gap/eff?
Run: python conjecture_B_typeA_terminal_classification.py
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
    m = G.number_of_edges(); S = float(d @ f)
    Gsum = sum((f[idx[u]] + f[idx[v]]) ** 2 for u, v in G.edges())
    B2 = sum((min(d[idx[u]], d[idx[v]]) - 1) * (f[idx[u]] - f[idx[v]]) ** 2 for u, v in G.edges())
    gap = lam * (Gsum - S ** 2 / m) - B2
    LH = nx.laplacian_matrix(H, nodelist=list(range(N))).toarray().astype(float)
    mu, phi = np.linalg.eigh(LH); gamma = float(mu[1]); dH = LH.diagonal()
    inv = 1.0 / (mu[1:] - lam)
    R = (phi[:, 1:] * inv) @ phi[:, 1:].T
    Raa, Rbb, Rab = R[a, a], R[b, b], R[a, b]
    eff = Raa + Rbb - 2 * Rab
    NA = set(H.neighbors(a)); NB = set(H.neighbors(b))
    defect = (N - 2) - len((NA & NB) - {a, b})
    return dict(N=N, n=N + 1, m=m, lam=lam, gamma=gamma, Delta=float(dH.max()), delta=float(dH.min()),
                gap=gap, eff=eff, R_plus=Raa + Rbb + 2 * Rab, R_minus=eff / 2,
                leverage=Raa + Rbb, asymmetry=abs(Raa - Rbb), defect=defect,
                lam_over_gamma=lam / gamma, fv0=float(f[v0]), gap_over_eff=gap / eff)


def typeA(r): return r is not None and r['lam'] < r['gamma'] and r['fv0'] ** 2 > 0.3


def collect():
    rng = np.random.default_rng(0); data = []
    for N in [25, 35, 50]:
        for q in [0.3, 0.45, 0.6, 0.75, 0.9]:
            H = nx.gnp_random_graph(N, q, seed=int(rng.integers(1e6)))
            Hc = nx.convert_node_labels_to_integers(H)
            if not nx.is_connected(Hc): continue
            deg = dict(Hc.degree())
            hi = sorted(deg, key=lambda u: -deg[u]); lo = sorted(deg, key=lambda u: deg[u])
            # vary attachment to spread terminal variables
            for a, b in [(0, 1), (hi[0], hi[1]), (lo[0], lo[1]), (hi[0], lo[0])]:
                r = analyze(Hc, a, b)
                if typeA(r): data.append(r)
        for frac in [0.3, 0.5]:
            rr = max(3, int(frac * N)); rr += (rr * N) % 2
            if rr <= N - 1:
                r = analyze(nx.random_regular_graph(rr, N, seed=1), 0, 1)
                if typeA(r): data.append(r)
        r = analyze(nx.circulant_graph(N, list(range(1, N // 5 + 1))), 0, 1)
        if typeA(r): data.append(r)
        r = analyze(nx.complete_graph(N), 0, 1)
        if typeA(r): data.append(r)
    return data


def main():
    data = collect()
    goe = np.array([d['gap_over_eff'] for d in data])
    print(f"  collected {len(data)} TYPE A graphs; gap/eff in [{goe.min():.2f}, {goe.max():.2f}]")

    print("\n" + "=" * 88)
    print("CONTROL OF gap/eff — single-variable Pearson r (raw and gamma-scaled)")
    print("=" * 88)
    cands = {
        'lam/gamma (bottleneck)': np.array([d['lam_over_gamma'] for d in data]),
        'terminal_leverage (Raa+Rbb)': np.array([d['leverage'] for d in data]),
        'asymmetry |Raa-Rbb|': np.array([d['asymmetry'] for d in data]),
        'common_defect': np.array([d['defect'] for d in data]),
        'R_plus (1^T R2 1)': np.array([d['R_plus'] for d in data]),
        'R_minus (eff/2)': np.array([d['R_minus'] for d in data]),
        'gamma': np.array([d['gamma'] for d in data]),
        'lam': np.array([d['lam'] for d in data]),
        'Delta/delta (regularity)': np.array([d['Delta'] / d['delta'] for d in data]),
        'gamma*leverage': np.array([d['gamma'] * d['leverage'] for d in data]),
    }
    for nm, x in sorted(cands.items(), key=lambda kv: -abs(np.corrcoef(kv[1], goe)[0, 1])):
        r = np.corrcoef(x, goe)[0, 1]
        print(f"  corr(gap/eff, {nm:28s}) = {r:+.3f}")

    print("\n" + "=" * 88)
    print("MULTIVARIATE: best 2-var linear fit of gap/eff (residual std; range=%.2f)" % (goe.max()-goe.min()))
    print("=" * 88)
    from itertools import combinations
    feats = {k: v for k, v in cands.items()}
    names = list(feats)
    best = []
    for combo in combinations(names, 2):
        X = np.column_stack([feats[c] for c in combo] + [np.ones(len(goe))])
        coef, *_ = np.linalg.lstsq(X, goe, rcond=None)
        res = (goe - X @ coef).std()
        best.append((res, combo))
    best.sort()
    for res, combo in best[:5]:
        print(f"  residual {res:.3f}  via  {combo}")
    # single best
    sb = sorted(names, key=lambda c: (goe - np.column_stack([feats[c], np.ones(len(goe))]) @
                np.linalg.lstsq(np.column_stack([feats[c], np.ones(len(goe))]), goe, rcond=None)[0]).std())
    print(f"  best single predictor: {sb[0]}")

    print("\n" + "=" * 88)
    print("CLUSTERING by terminal variables (buckets) — gap/eff distribution per cluster")
    print("=" * 88)
    # bucket by lam/gamma (bottleneck strength) and asymmetry
    for lab, cond in [("strong bottleneck lam/gamma<0.1", lambda d: d['lam_over_gamma'] < 0.1),
                      ("mid 0.1-0.3", lambda d: 0.1 <= d['lam_over_gamma'] < 0.3),
                      ("weak 0.3-0.5", lambda d: 0.3 <= d['lam_over_gamma'] < 0.5),
                      ("borderline >=0.5", lambda d: d['lam_over_gamma'] >= 0.5)]:
        sub = [d['gap_over_eff'] for d in data if cond(d)]
        if sub:
            print(f"  {lab:32s} n={len(sub):3d}  gap/eff: min={min(sub):.2f} "
                  f"med={np.median(sub):.2f} max={max(sub):.2f}")
    print("  by asymmetry:")
    asy = np.array([d['asymmetry'] for d in data]); med_asy = np.median(asy)
    for lab, cond in [("symmetric (asym<median)", lambda d: d['asymmetry'] < med_asy),
                      ("asymmetric (asym>=median)", lambda d: d['asymmetry'] >= med_asy)]:
        sub = [d['gap_over_eff'] for d in data if cond(d)]
        print(f"  {lab:32s} n={len(sub):3d}  gap/eff: min={min(sub):.2f} "
              f"med={np.median(sub):.2f} max={max(sub):.2f}")

    print("\n" + "=" * 88)
    print("SUMMARY: which terminal variable controls gap/eff?")
    print("=" * 88)
    top = max(cands.items(), key=lambda kv: abs(np.corrcoef(kv[1], goe)[0, 1]))
    print(f"  top single correlate: {top[0]}  (r={np.corrcoef(top[1],goe)[0,1]:+.3f})")


if __name__ == "__main__":
    main()
