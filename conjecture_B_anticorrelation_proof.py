"""
Test universality of anti-correlation Cov(t_e,g^2)<=0, i.e. m*Sum t_e g^2 <= (Sum t_e)(Sum g^2).
Adversarial: triangle-RICH cut (high t_e AND high g^2 on the bottleneck) could break it.
Run: python conjecture_B_anticorrelation_proof.py
"""
import numpy as np
import networkx as nx


def cov(G):
    G = nx.convert_node_labels_to_integers(G); n = G.number_of_nodes()
    if not nx.is_connected(G): return None
    A = nx.to_numpy_array(G); d = A.sum(1); L = np.diag(d) - A; A2 = A @ A
    ev, U = np.linalg.eigh(L); lam = ev[1]; f = U[:, 1]; f = f / np.linalg.norm(f)
    d_eff = float(d @ (f * f))
    edges = [(i, j) for i in range(n) for j in range(i + 1, n) if A[i, j] > 0]
    m = len(edges)
    if m == 0: return None
    t = np.array([A2[a, b] for a, b in edges])
    g2 = np.array([(f[a] - f[b]) ** 2 for a, b in edges])
    if t.sum() == 0: return None  # triangle-free
    Cov = float((t * g2).mean() - t.mean() * g2.mean())
    T = float((t * g2).sum())
    aggr = T / (lam * d_eff) if lam * d_eff > 0 else 0.0  # T_unord/(lam d_eff) <=1 = aggregate
    eg = ev[2] - ev[1]
    return dict(n=n, Cov=Cov, cov_le0=(Cov <= 1e-9), aggr=aggr, aggr_ok=(aggr <= 1 + 1e-7),
                corr=np.corrcoef(t, g2)[0, 1] if t.std() > 0 and g2.std() > 0 else 0.0, eigengap=eg)


def two_cliques_bridge(k, b):
    """Two K_k cliques + b bridge vertices each joined to ALL vertices (triangle-rich cut)."""
    G = nx.Graph()
    C1 = list(range(k)); C2 = list(range(k, 2 * k)); B = list(range(2 * k, 2 * k + b))
    for C in (C1, C2):
        for i in range(len(C)):
            for j in range(i + 1, len(C)): G.add_edge(C[i], C[j])
    for v in B:
        for u in C1 + C2 + B:
            if u != v: G.add_edge(v, u)
    return G


def cliques_path_dense(k, j):
    """K_k - (bridge K_j fully joined to both) - K_k: cut through dense bridge."""
    G = nx.Graph()
    C1 = list(range(k)); Br = list(range(k, k + j)); C2 = list(range(k + j, 2 * k + j))
    for C in (C1, C2, Br):
        for i in range(len(C)):
            for x in range(i + 1, len(C)): G.add_edge(C[i], C[x])
    for v in Br:
        for u in C1 + C2:
            G.add_edge(v, u)
    return G


def corpus():
    out = []
    # adversarial triangle-rich-cut
    for k in [4, 6, 8, 10]:
        for b in [1, 2, 3]: out.append((f"2clq{k}_brAll{b}", two_cliques_bridge(k, b)))
    for k in [4, 6, 8]:
        for j in [2, 3, 4]: out.append((f"clqPath{k}_br{j}", cliques_path_dense(k, j)))
    # blow-ups / products
    for n5 in [4, 6]: out.append((f"C5xK{n5}", nx.lexicographic_product(nx.cycle_graph(5), nx.complete_graph(n5))))
    for m3 in [3, 4]: out.append((f"P3xK{m3}", nx.lexicographic_product(nx.path_graph(3), nx.complete_graph(m3))))
    # friendship / windmill
    for k in [3, 5, 7]: out.append((f"windmill{k}", nx.windmill_graph(k, 3)))
    # multipartite + standard
    out.append(("Kmp334", nx.complete_multipartite_graph(3, 3, 4)))
    out.append(("Kmp226", nx.complete_multipartite_graph(2, 2, 6)))
    out.append(("cocktail6", nx.complete_multipartite_graph(*([2] * 6))))
    for nn in [10, 20]: out.append((f"K{nn}", nx.complete_graph(nn)))
    for nn in [20]: out.append((f"rr{nn}_6", nx.random_regular_graph(6, nn, seed=1)))
    rng = np.random.default_rng(0)
    for nn in [25, 40]:
        for q in [0.3, 0.6]: out.append((f"gnp{nn}_{q}", nx.gnp_random_graph(nn, q, seed=int(rng.integers(1e9)))))
    def d2(nn, q, s):
        H = nx.gnp_random_graph(nn - 1, q, seed=s); H.add_node(nn - 1); H.add_edge(nn - 1, 0); H.add_edge(nn - 1, 1); return H
    for nn in [40, 60]:
        for q in [0.2, 0.6]: out.append((f"deg2d{nn}_{q}", d2(nn, q, 7)))
    return out


def main():
    data = [(nm, q) for nm, G in corpus() for q in [cov(G)] if q is not None]
    cok = sum(1 for _, q in data if q['cov_le0'])
    print(f"  {len(data)} graphs (with triangles)")
    print(f"  Cov(t,g²) <= 0 (anti-correlation): {cok}/{len(data)}")
    print(f"  aggregate T<=λd_eff: {sum(1 for _,q in data if q['aggr_ok'])}/{len(data)}")

    print("\n" + "=" * 92)
    print("Cov > 0 COUNTEREXAMPLES (anti-correlation BREAKS):")
    print("=" * 92)
    viol = [(nm, q) for nm, q in data if not q['cov_le0']]
    if viol:
        print(f"  {len(viol)} found:")
        for nm, q in sorted(viol, key=lambda x: -x[1]['Cov']):
            print(f"    {nm:16s} Cov={q['Cov']:+.5f} corr={q['corr']:+.3f} aggr(T/λd_eff)={q['aggr']:.3f} "
                  f"{'AGGR OK' if q['aggr_ok'] else 'AGGR FAILS!'}")
    else:
        print("  NONE — anti-correlation holds universally on this corpus.")

    print("\n" + "=" * 92)
    print("Most positive Cov (closest to breaking), by construction:")
    print("=" * 92)
    print(f"  {'graph':16s} {'Cov':>9} {'corr':>7} {'aggr':>7}")
    for nm, q in sorted(data, key=lambda x: -x[1]['Cov'])[:14]:
        print(f"  {nm:16s} {q['Cov']:9.5f} {q['corr']:7.3f} {q['aggr']:7.3f}")

    print("\n" + "=" * 92)
    print("SUMMARY")
    print("=" * 92)
    print(f"  Cov<=0: {cok}/{len(data)}; aggregate: {sum(1 for _,q in data if q['aggr_ok'])}/{len(data)}")
    if viol:
        anti_but_aggr = sum(1 for _, q in viol if q['aggr_ok'])
        print(f"  => anti-correlation NOT universal ({len(viol)} Cov>0); aggregate still holds on "
              f"{anti_but_aggr}/{len(viol)} of them => aggregate NOT explained by anti-correlation there.")
    else:
        print("  => anti-correlation universal on corpus (incl adversarial triangle-rich cuts).")


if __name__ == "__main__":
    main()
