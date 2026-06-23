"""
Aggregate-slack decomposition. CORRECT identity (prompt dropped D=lam*S^2/m):
  gap = lam(2d_eff - lam - S^2/m) - T = S_agg + E,
  S_agg = lam*d_eff - T (aggregate slack, >=0),  E = lam(d_eff - lam - S^2/m) = lam(fAf - S^2/m).
Dichotomy: E>=0 (d_eff>=lam+S^2/m) => gap=S_agg+E>=S_agg>=0 (AGGREGATE SUFFICES). Hard case: E<0.
Run: python conjecture_B_aggregate_slack.py
"""
import numpy as np
import networkx as nx


def quant(G):
    G = nx.convert_node_labels_to_integers(G); n = G.number_of_nodes()
    if not nx.is_connected(G): return None
    A = nx.to_numpy_array(G); d = A.sum(1); L = np.diag(d) - A
    ev, U = np.linalg.eigh(L); lam = ev[1]; f = U[:, 1]; f = f / np.linalg.norm(f)
    m = G.number_of_edges(); S = float(d @ f); d_eff = float(d @ (f * f)); A2 = A @ A
    edges = [(i, j) for i in range(n) for j in range(i + 1, n) if A[i, j] > 0]
    T = sum(A2[a, b] * (f[a] - f[b]) ** 2 for a, b in edges)
    fAf = d_eff - lam
    S_agg = lam * d_eff - T
    E = lam * (d_eff - lam - S ** 2 / m)
    gap = lam * (2 * d_eff - lam - S ** 2 / m) - T
    return dict(n=n, lam=lam, d_eff=d_eff, S2m=S ** 2 / m, T=T, fAf=fAf, S_agg=S_agg, E=E, gap=gap,
                t_eff=T / lam, regular=(d.max() == d.min()))


def corpus():
    out = []; rng = np.random.default_rng(0)
    def deg2dense(nn, q, s):
        H = nx.gnp_random_graph(nn - 1, q, seed=s); H.add_node(nn - 1)
        H.add_edge(nn - 1, 0); H.add_edge(nn - 1, 1); return H
    def twin(N, dd):
        K = nx.complete_graph(N); a, b = N, N + 1
        for x in (a, b):
            for w in range(dd): K.add_edge(x, w)
        K.add_node(N + 2); K.add_edge(N + 2, a); K.add_edge(N + 2, b); return K
    def star(kc, ks):
        G = nx.complete_graph(kc)
        for i in range(ks): G.add_edge(0, kc + i)
        return G
    for nn in [30, 50, 80]:
        for q in [0.3, 0.5, 0.7, 0.9]: out.append((f"deg2d{nn}_{q}", deg2dense(nn, q, int(rng.integers(1e9)))))
    for N in [30, 50, 80]:
        for dd in [2, 3, 4]: out.append((f"twin{N}_{dd}", twin(N, dd)))
    for kc, ks in [(10, 6), (12, 8)]: out.append((f"star{kc}_{ks}", star(kc, ks)))
    for k, l in [(10, 10), (15, 12)]: out.append((f"lolli{k}_{l}", nx.lollipop_graph(k, l)))
    out.append(("barb8_8", nx.barbell_graph(8, 8)))
    for nn in [25, 40, 60]:
        for q in [0.2, 0.35, 0.5, 0.7, 0.85]: out.append((f"gnp{nn}_{q}", nx.gnp_random_graph(nn, q, seed=int(rng.integers(1e9)))))
    for nn in [20, 40]:
        for r in [4, 8]:
            if (r * nn) % 2 == 0: out.append((f"rr{nn}_{r}", nx.random_regular_graph(r, nn, seed=1)))
    for nn in [12, 20]: out.append((f"K{nn}", nx.complete_graph(nn)))
    for nn in [30, 50]:
        for kd in [1, 5, 12]:
            K = nx.complete_graph(nn); E = list(K.edges()); rng.shuffle(E); rem = 0
            for e in E:
                if rem >= kd: break
                if K.degree(e[0]) > 2 and K.degree(e[1]) > 2: K.remove_edge(*e); rem += 1
            out.append((f"K{nn}-{rem}", K))
    return out


def main():
    data = [(nm, q) for nm, G in corpus() for q in [quant(G)] if q is not None]
    print(f"  {len(data)} graphs")

    print("\n" + "=" * 92)
    print("CORRECTED identity: gap = S_agg + E, S_agg=λd_eff-T>=0, E=λ(d_eff-λ-S²/m)")
    print("=" * 92)
    err = max(abs(q['gap'] - (q['S_agg'] + q['E'])) for _, q in data)
    sagg_ok = sum(1 for _, q in data if q['S_agg'] >= -1e-7)
    print(f"  max|gap-(S_agg+E)| = {err:.2e}; S_agg>=0 (aggregate): {sagg_ok}/{len(data)}")

    print("\n" + "=" * 92)
    print("TASK 1 — THE DICHOTOMY: E>=0 => aggregate suffices (gap>=S_agg>=0). Hard case E<0.")
    print("=" * 92)
    Epos = [(nm, q) for nm, q in data if q['E'] >= -1e-9]
    Eneg = [(nm, q) for nm, q in data if q['E'] < -1e-9]
    print(f"  E>=0 (d_eff>=λ+S²/m): {len(Epos)}/{len(data)}  <- AGGREGATE PROVES gap>=0 here")
    print(f"  E<0  (hard case)    : {len(Eneg)}/{len(data)}")
    print(f"  E>=0 examples: {[nm for nm,_ in Epos[:8]]}")
    print(f"  E<0  examples: {[nm for nm,_ in Eneg[:8]]}")

    print("\n" + "=" * 92)
    print("TASK 3/4 — hard case E<0: does S_agg >= -E (= gap>=0)? and how tight?")
    print("=" * 92)
    print(f"  {'graph':12s} {'gap':>8} {'S_agg':>8} {'E':>8} {'-E':>8} {'S_agg/(-E)':>11} {'reg':>4}")
    for nm, q in sorted(Eneg, key=lambda x: x[1]['gap'])[:14]:
        r = q['S_agg'] / (-q['E']) if q['E'] < -1e-9 else float('inf')
        print(f"  {nm:12s} {q['gap']:8.4f} {q['S_agg']:8.4f} {q['E']:8.4f} {-q['E']:8.4f} {r:11.4f} {str(q['regular']):>4}")
    print("  (S_agg/(-E) >= 1 <=> gap>=0; =1 at K_n exact)")

    print("\n" + "=" * 92)
    print("TASK 2 — aggregate slack structure: S_agg/λ = d_eff - t_eff (anti-correlation)")
    print("=" * 92)
    print(f"  {'graph':12s} {'d_eff':>8} {'t_eff=T/λ':>10} {'S_agg/λ':>9} {'-E/λ':>8}")
    for nm, q in sorted(data, key=lambda x: x[1]['gap'])[:8]:
        print(f"  {nm:12s} {q['d_eff']:8.3f} {q['t_eff']:10.3f} {q['d_eff']-q['t_eff']:9.4f} {-q['E']/q['lam']:8.4f}")
    print("  (S_agg/λ = d_eff - t_eff; need >= -E/λ = λ+S²/m-d_eff in hard case)")

    print("\n" + "=" * 92)
    print("K_n check: S_agg = -E exactly (equality)")
    print("=" * 92)
    for nm, q in [("K12", None), ("K20", None)]:
        q = dict(data).get(nm)
        if q: print(f"  {nm}: S_agg={q['S_agg']:.4f} -E={-q['E']:.4f} gap={q['gap']:.4f} (match: {abs(q['S_agg']+q['E'])<1e-6})")

    print("\n" + "=" * 92)
    print("SUMMARY")
    print("=" * 92)
    hardok = sum(1 for _, q in Eneg if q['S_agg'] >= -q['E'] - 1e-9)
    print(f"  DICHOTOMY: E>=0 (aggregate suffices) {len(Epos)}/{len(data)}; E<0 (hard) {len(Eneg)}/{len(data)}")
    print(f"  hard case S_agg>=-E (=gap>=0): {hardok}/{len(Eneg)}")


if __name__ == "__main__":
    main()
