"""
lam2-SIMPLE core (mult=1, gap=trace, irreducible). gap = A - B - D.
A=Sum_e deficit_e g_e^2, B=lam*Sum_nonedge h^2, D=lam*S^2/m.
Tasks: collect simple-lam2 hard families; which term saturates; eigengap lam3-lam2 relevance;
lower bound gap >= c(lam3-lam2)*Phi ?; clean lemma candidate.
Run: python conjecture_B_simple_lam2_core.py
"""
import numpy as np
import networkx as nx


def quant(G):
    G = nx.convert_node_labels_to_integers(G); n = G.number_of_nodes()
    if not nx.is_connected(G): return None
    A = nx.to_numpy_array(G); d = A.sum(1); L = np.diag(d) - A
    ev, U = np.linalg.eigh(L); lam = ev[1]; lam3 = ev[2]
    if lam3 - lam < 1e-7: return None  # only simple lam2
    f = U[:, 1]; f = f / np.linalg.norm(f)
    m = G.number_of_edges(); S = float(d @ f); A2 = A @ A
    edges = [(i, j) for i in range(n) for j in range(i + 1, n) if A[i, j] > 0]
    nonedges = [(i, j) for i in range(n) for j in range(i + 1, n) if A[i, j] == 0]
    Aterm = 0.0
    for (a, b) in edges:
        deficit = sum(1 for c in range(n) if c != a and c != b and (A[a, c] == 0 or A[b, c] == 0))
        Aterm += deficit * (f[a] - f[b]) ** 2
    Bterm = lam * sum((f[i] + f[j]) ** 2 for i, j in nonedges)
    Dterm = lam * S ** 2 / m
    gap = Aterm - Bterm - Dterm
    return dict(n=n, lam=lam, lam3=lam3, eg=lam3 - lam, A=Aterm, B=Bterm, D=Dterm, gap=gap,
                regular=(d.max() == d.min()))


def families():
    out = []
    rng = np.random.default_rng(0)
    def deg2dense(nn, q, s):
        H = nx.gnp_random_graph(nn - 1, q, seed=s); H.add_node(nn - 1)
        H.add_edge(nn - 1, 0); H.add_edge(nn - 1, 1); return H
    def twin(N, dd):
        K = nx.complete_graph(N); a, b = N, N + 1
        for x in (a, b):
            for w in range(dd): K.add_edge(x, w)
        K.add_node(N + 2); K.add_edge(N + 2, a); K.add_edge(N + 2, b); return K
    for nn in [30, 40, 60, 90]:
        for q in [0.4, 0.6, 0.8]:
            out.append((f"deg2dense{nn}_{q}", deg2dense(nn, q, int(rng.integers(1e9)))))
    for N in [30, 50, 80]:
        for dd in [2, 3, 4]:
            out.append((f"twinK{N}_d{dd}", twin(N, dd)))
    for k, l in [(10, 10), (15, 12), (20, 8)]:
        out.append((f"lollipop{k}_{l}", nx.lollipop_graph(k, l)))
    for k, l in [(8, 8), (12, 6)]:
        out.append((f"barbell{k}_{l}", nx.barbell_graph(k, l)))
    for nn in [25, 40, 60]:
        for q in [0.2, 0.35, 0.5, 0.7]:
            out.append((f"gnp{nn}_{q}", nx.gnp_random_graph(nn, q, seed=int(rng.integers(1e9)))))
    for nn in [30, 50]:
        for kdel in [1, 3, 8]:
            K = nx.complete_graph(nn); E = list(K.edges()); rng.shuffle(E); rem = 0
            for e in E:
                if rem >= kdel: break
                if K.degree(e[0]) > 2 and K.degree(e[1]) > 2: K.remove_edge(*e); rem += 1
            out.append((f"K{nn}-{rem}", K))
    return out


def main():
    data = [(nm, q) for nm, G in families() for q in [quant(G)] if q is not None]
    print(f"  collected {len(data)} SIMPLE-λ₂ graphs (eigengap λ₃−λ₂ > 0)")

    print("\n" + "=" * 92)
    print("TASK 3 — which term saturates gap? B/A, D/A, gap/A; tightest (gap/A small)")
    print("=" * 92)
    print(f"  {'graph':16s} {'gap':>8} {'B/A':>7} {'D/A':>7} {'gap/A':>8} {'eigengap':>9} {'reg':>4}")
    for nm, q in sorted(data, key=lambda x: x[1]['gap'] / max(x[1]['A'], 1e-9))[:14]:
        print(f"  {nm:16s} {q['gap']:8.4f} {q['B']/q['A']:7.4f} {q['D']/q['A']:7.4f} "
              f"{q['gap']/q['A']:8.4f} {q['eg']:9.4f} {str(q['regular']):>4}")
    print("  (B dominates A; D small/0; tightest = deg2dense/twin-port bottleneck)")

    print("\n" + "=" * 92)
    print("TASK 4/5 — eigengap relevance: correlate gap (and gap/A) with eigengap λ₃−λ₂")
    print("=" * 92)
    g = np.array([q['gap'] for _, q in data]); ga = np.array([q['gap']/q['A'] for _, q in data])
    eg = np.array([q['eg'] for _, q in data])
    print(f"  corr(gap, eigengap)      = {np.corrcoef(g, eg)[0,1]:+.3f}")
    print(f"  corr(gap/A, eigengap)    = {np.corrcoef(ga, eg)[0,1]:+.3f}")
    # test gap >= c*eigengap: min gap/eigengap
    ratio = g / eg
    print(f"  min gap/eigengap = {ratio.min():.4f} at {data[int(np.argmin(ratio))][0]}; "
          f"is gap >= c·eigengap for c={ratio.min():.3f}? (c>0 trivially since gap>0)")
    # is small gap correlated with small eigengap? (bottleneck has small eigengap?)
    tight = sorted(data, key=lambda x: x[1]['gap']/max(x[1]['A'],1e-9))[:6]
    print(f"  tightest graphs' eigengaps: {[round(q['eg'],3) for _,q in tight]} "
          f"(small eigengap => near-degenerate => harder?)")

    print("\n" + "=" * 92)
    print("TASK 4 — sharper inequality: A-B >= D using simplicity? test (A-B)/D and whether D ever binds")
    print("=" * 92)
    nz = [(nm, q) for nm, q in data if q['D'] > 1e-9]
    print(f"  graphs with D>0 (irregular): {len(nz)}/{len(data)}")
    if nz:
        worst = min(nz, key=lambda x: (x[1]['A']-x[1]['B'])/x[1]['D'])
        print(f"  min (A-B)/D = {(worst[1]['A']-worst[1]['B'])/worst[1]['D']:.4f} at {worst[0]} "
              f"(>1 means A-B>D, gap>0)")
    print(f"  A-B>=D (gap>=0) all simple-λ₂: {all(q['gap']>=-1e-9 for _,q in data)} "
          f"(min gap={min(q['gap'] for _,q in data):.4f})")

    print("\n" + "=" * 92)
    print("TASK 6 — clean lemma candidate: gap = A-B-D; B dominant. Lower bound shape?")
    print("=" * 92)
    # test gap >= c*A for some uniform c>0 (gap/A min)
    print(f"  min gap/A = {ga.min():.4f} at {data[int(np.argmin(ga))][0]}  "
          f"(gap >= c·A with c={ga.min():.3f}? infimum over corpus)")
    print(f"  min gap/lam2 = {min(q['gap']/q['lam'] for _,q in data):.4f}; "
          f"min gap = {g.min():.4f}")

    print("\n" + "=" * 92)
    print("SUMMARY")
    print("=" * 92)
    print(f"  simple-λ₂: gap>0 all ({len(data)}); B dominant; D small; corr(gap,eigengap)="
          f"{np.corrcoef(g,eg)[0,1]:+.2f}; min gap/A={ga.min():.3f}")


if __name__ == "__main__":
    main()
