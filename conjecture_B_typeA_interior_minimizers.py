"""
TYPE A interior minimizers: graphs with gap/eff < 3 (the genuine hard cases).
Extract, characterize the family pattern, scale-test.
Run: python conjecture_B_typeA_interior_minimizers.py
"""
import numpy as np
import networkx as nx


def analyze(H, a, b, fam=""):
    H = nx.convert_node_labels_to_integers(H); N = H.number_of_nodes()
    if not nx.is_connected(H) or a == b or a >= N or b >= N: return None
    G = nx.Graph(H); G.add_node(N); G.add_edge(N, a); G.add_edge(N, b)
    nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}
    A = nx.to_numpy_array(G, nodelist=nodes); d = A.sum(1); L = np.diag(d) - A
    ev, U = np.linalg.eigh(L); lam = ev[1]; f = U[:, 1]; f = f / np.linalg.norm(f)
    v0 = idx[N]
    if f[v0] < 0: f = -f
    m = G.number_of_edges(); S = float(d @ f); fDf = float(d @ (f * f))
    Gsum = sum((f[idx[u]] + f[idx[v]]) ** 2 for u, v in G.edges())
    B2 = sum((min(d[idx[u]], d[idx[v]]) - 1) * (f[idx[u]] - f[idx[v]]) ** 2 for u, v in G.edges())
    gap = lam * (Gsum - S ** 2 / m) - B2
    LH = nx.laplacian_matrix(H, nodelist=list(range(N))).toarray().astype(float)
    mu, phi = np.linalg.eigh(LH); gamma = float(mu[1])
    if gamma - lam <= 1e-9: return None
    inv = 1.0 / (mu[1:] - lam); R = (phi[:, 1:] * inv) @ phi[:, 1:].T
    Raa, Rbb, Rab = R[a, a], R[b, b], R[a, b]
    eff = Raa + Rbb - 2 * Rab
    NA = set(H.neighbors(a)); NB = set(H.neighbors(b))
    defect = (N - 2) - len((NA & NB) - {a, b})
    Req = lam * (lam + S ** 2 / m - fDf)
    return dict(N=N, n=N + 1, m=m, fam=fam, lam=lam, gamma=gamma, lg=lam / gamma,
                da=int(LH[a, a]), db=int(LH[b, b]), Raa=Raa, Rbb=Rbb, Rab=Rab, eff=eff,
                defect=defect, asym=abs(Raa - Rbb), fa=float(f[idx[a]]), fb=float(f[idx[b]]),
                fv0=float(f[v0]), Required=Req, gap=gap, goe=gap / eff,
                degspread=int(LH.diagonal().max() - LH.diagonal().min()))


def typeA(r): return r is not None and r['fv0'] ** 2 > 0.3


def corpus():
    rng = np.random.default_rng(0); out = []
    for N in [18, 24, 30, 40, 55]:
        for q in [0.25, 0.35, 0.5, 0.65, 0.8]:
            for s in range(3):
                H = nx.gnp_random_graph(N, q, seed=int(rng.integers(1e9)))
                Hc = nx.convert_node_labels_to_integers(H)
                if not nx.is_connected(Hc): continue
                deg = dict(Hc.degree()); hi = sorted(deg, key=lambda u: -deg[u]); lo = sorted(deg, key=lambda u: deg[u])
                for tag, a, b in [("sym01", 0, 1), ("hihi", hi[0], hi[1]),
                                  ("lolo", lo[0], lo[1]), ("lohi", lo[0], hi[0])]:
                    r = analyze(Hc, a, b, f"gnp{N}_{q}_{tag}")
                    if typeA(r): out.append(r)
        for rr in [5, 8, 12]:
            if rr <= N - 1 and (rr * N) % 2 == 0:
                r = analyze(nx.random_regular_graph(rr, N, seed=1), 0, 1, f"rr{N}_{rr}")
                if typeA(r): out.append(r)
        for p, q2 in [(5, N - 5), (8, N - 8)]:
            if q2 > 1:
                r = analyze(nx.complete_bipartite_graph(p, q2), 0, p, f"Kbip{p},{q2}")
                if typeA(r): out.append(r)
    return out


def main():
    data = corpus()
    print(f"  corpus: {len(data)} TYPE A graphs; gap/eff in "
          f"[{min(d['goe'] for d in data):.2f}, {max(d['goe'] for d in data):.2f}]")

    print("\n" + "=" * 110)
    print("TASK 1 — minimizers (gap/eff < 3)")
    print("=" * 110)
    mins = sorted([d for d in data if d['goe'] < 3.0], key=lambda d: d['goe'])
    print(f"  {len(mins)} graphs with gap/eff < 3")
    print(f"  {'family':18s} {'n':>4} {'lam':>6} {'gam':>6} {'lg':>5} {'da':>3} {'db':>3} "
          f"{'eff':>7} {'defect':>6} {'asym':>7} {'fa':>7} {'fb':>7} {'Req':>7} {'goe':>6}")
    for d in mins[:25]:
        print(f"  {d['fam']:18s} {d['n']:4d} {d['lam']:6.3f} {d['gamma']:6.2f} {d['lg']:5.2f} "
              f"{d['da']:3d} {d['db']:3d} {d['eff']:7.3f} {d['defect']:6d} {d['asym']:7.4f} "
              f"{d['fa']:7.4f} {d['fb']:7.4f} {d['Required']:7.3f} {d['goe']:6.3f}")

    print("\n" + "=" * 110)
    print("TASK 2 — family pattern of minimizers vs the rest")
    print("=" * 110)
    rest = [d for d in data if d['goe'] >= 3.0]
    def stat(s, k): return (np.mean([d[k] for d in s]), np.median([d[k] for d in s]))
    print(f"  {'feature':24s} {'minimizers(<3) mean/med':>26s} {'rest(>=3) mean/med':>22s}")
    for k in ['n', 'lam', 'lg', 'da', 'db', 'asym', 'defect', 'degspread', 'Required']:
        mm = stat(mins, k); rr = stat(rest, k)
        print(f"  {k:24s} {mm[0]:11.3f}/{mm[1]:8.3f}      {rr[0]:11.3f}/{rr[1]:8.3f}")
    # tag distribution among minimizers
    from collections import Counter
    tags = Counter(d['fam'].split('_')[-1] for d in mins)
    print(f"  attachment-tag distribution among minimizers: {dict(tags)}")
    smalln = sum(1 for d in mins if d['n'] <= 25)
    print(f"  minimizers with n<=25: {smalln}/{len(mins)}")
    asym_hi = sum(1 for d in mins if d['asym'] > np.median([x['asym'] for x in data]))
    print(f"  minimizers with above-median asymmetry: {asym_hi}/{len(mins)}")

    print("\n" + "=" * 110)
    print("TASK 3 — scale test: grow candidate minimizer patterns with n")
    print("=" * 110)
    for tag, builder in [
        ("lohi gnp(.4) [asym lo-hi attach]", lambda N: ("lohi", nx.gnp_random_graph(N, 0.4, seed=7))),
        ("lolo gnp(.4) [both low-deg]", lambda N: ("lolo", nx.gnp_random_graph(N, 0.4, seed=7))),
        ("sym gnp(.35)", lambda N: ("sym", nx.gnp_random_graph(N, 0.35, seed=7))),
        ("complete bipartite K_{8,N-8}", lambda N: ("bip", nx.complete_bipartite_graph(8, N - 8)))]:
        print(f"  pattern: {tag}")
        row = []
        for N in [20, 30, 50, 80, 120, 200]:
            kind, H = builder(N); Hc = nx.convert_node_labels_to_integers(H)
            if not nx.is_connected(Hc): continue
            deg = dict(Hc.degree()); hi = sorted(deg, key=lambda u: -deg[u]); lo = sorted(deg, key=lambda u: deg[u])
            if kind == "lohi": a, b = lo[0], hi[0]
            elif kind == "lolo": a, b = lo[0], lo[1]
            elif kind == "bip": a, b = 0, 8
            else: a, b = 0, 1
            r = analyze(Hc, a, b)
            if typeA(r): row.append((N, r['goe'], r['lg'], r['asym']))
        print("     " + "  ".join(f"n={N}:goe={g:.2f}(lg={lg:.2f})" for N, g, lg, _ in row))

    print("\n" + "=" * 110)
    print("TASK 4 — candidate covering condition for minimizers")
    print("=" * 110)
    # correlate goe with candidate penalties on the FULL corpus
    goe = np.array([d['goe'] for d in data])
    cands = {'asymmetry': np.array([d['asym'] for d in data]),
             '1/n': np.array([1.0 / d['n'] for d in data]),
             'lam (sharpness)': np.array([d['lam'] for d in data]),
             'leverage Raa+Rbb': np.array([d['Raa'] + d['Rbb'] for d in data]),
             'lo-deg min(da,db)': np.array([min(d['da'], d['db']) for d in data])}
    for nm, x in sorted(cands.items(), key=lambda kv: -abs(np.corrcoef(kv[1], goe)[0, 1])):
        print(f"  corr(gap/eff, {nm:20s}) = {np.corrcoef(x, goe)[0,1]:+.3f}")


if __name__ == "__main__":
    main()
