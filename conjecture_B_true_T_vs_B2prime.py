"""
Is T <= lam2 G easier than B2' <= lam2 G?

T = sum_e t_e g_e^2 (t_e = #common neighbors), B2' = sum_e (min(d_a,d_b)-1) g_e^2,
g_e = f_a-f_b, h_e=f_a+f_b, G = sum_e h_e^2 - S^2/m, lam2 = sum_e g_e^2 = f^T L f.
Target: t_eff := T/lam2 <= G  (<=> T <= lam2 G). Compare T/(lam2 G) vs B2'/(lam2 G).
Run: python conjecture_B_true_T_vs_B2prime.py
"""
import numpy as np
import networkx as nx


def metrics(G):
    nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}; n = len(nodes)
    A = nx.to_numpy_array(G, nodelist=nodes); d = A.sum(1); L = np.diag(d) - A
    ev, U = np.linalg.eigh(L); lam = ev[1]; f = U[:, 1]; f = f / np.linalg.norm(f)
    m = G.number_of_edges(); S = float(d @ f)
    A2 = A @ A
    T = lam2sum = B2 = Gsum = 0.0
    for u, v in G.edges():
        a, b = idx[u], idx[v]; g = (f[a] - f[b]) ** 2; h = (f[a] + f[b]) ** 2
        T += A2[a, b] * g; B2 += (min(d[a], d[b]) - 1) * g; lam2sum += g; Gsum += h
    Gvar = Gsum - S ** 2 / m
    lam2G = lam * Gvar
    return dict(n=n, m=m, lam=lam, T=T, B2=B2, lam2sum=lam2sum, Gvar=Gvar, lam2G=lam2G,
                t_eff=T / lam, b2_eff=B2 / lam, T_ratio=T / lam2G, B2_ratio=B2 / lam2G,
                Delta=float(d.max()), delta=float(d.min()))


def corpus():
    rng = np.random.default_rng(0); out = []
    for n in [15, 25, 40, 60]:
        for q in [0.2, 0.35, 0.5, 0.65, 0.8, 0.9]:
            H = nx.gnp_random_graph(n, q, seed=int(rng.integers(1e9)))
            if nx.is_connected(H): out.append((f"gnp{n}_{q}", H))
        for r in [4, n // 3, n - 3]:
            if 3 <= r <= n - 1 and (r * n) % 2 == 0:
                out.append((f"rr{n}_{r}", nx.random_regular_graph(r, n, seed=1)))
        out.append((f"K{n}", nx.complete_graph(n)))
    # hard families
    for n in [40, 80, 160]:
        H = nx.gnp_random_graph(n - 1, 0.65, seed=2); H.add_node(n - 1)
        H.add_edge(n - 1, 0); H.add_edge(n - 1, 1)
        if nx.is_connected(H): out.append((f"deg2dense{n}", H))
    for k, l in [(20, 20), (10, 40), (30, 10)]:
        out.append((f"lollipop{k}_{l}", nx.lollipop_graph(k, l)))
    for k in [10, 20]:
        out.append((f"barbell{k}", nx.barbell_graph(k, 10)))
    # complete bulk + deg-2 twins (the TYPE A extremizer)
    for n in [40, 100]:
        H = nx.complete_graph(n); a, b = n, n + 1
        for x in (a, b): H.add_edge(x, 0); H.add_edge(x, 1)
        H.add_node(n + 2); H.add_edge(n + 2, a); H.add_edge(n + 2, b)
        out.append((f"twinK{n}", H))
    return out


def main():
    data = [(nm, metrics(G)) for nm, G in corpus()]

    print("=" * 96)
    print("TASK 1/3 — T/(lam2 G) vs B2'/(lam2 G); does t_eff <= G (i.e. T_ratio<=1) hold?")
    print("=" * 96)
    print(f"  {'graph':16s} {'lam2':>7} {'T/(lam2G)':>10} {'B2/(lam2G)':>11} {'t_eff':>8} {'G':>8} "
          f"{'t_eff<=G':>9} {'B2<=lam2G':>10}")
    Tok = B2ok = 0
    for nm, q in data:
        teff_le_G = q['t_eff'] <= q['Gvar'] + 1e-9
        b2_le = q['B2'] <= q['lam2G'] + 1e-9
        Tok += teff_le_G; B2ok += b2_le
        print(f"  {nm:16s} {q['lam']:7.4f} {q['T_ratio']:10.4f} {q['B2_ratio']:11.4f} "
              f"{q['t_eff']:8.4f} {q['Gvar']:8.4f} {str(teff_le_G):>9} {str(b2_le):>10}")
    print(f"\n  t_eff <= G (T<=lam2G) : {Tok}/{len(data)};  B2' <= lam2G : {B2ok}/{len(data)}")

    print("\n" + "=" * 96)
    print("TASK 1 — margins: how much slacker is T than B2'?  (1 - ratio)")
    print("=" * 96)
    Tr = np.array([q['T_ratio'] for _, q in data]); B2r = np.array([q['B2_ratio'] for _, q in data])
    print(f"  T/(lam2G):  max={Tr.max():.4f} (sup over corpus) ; median={np.median(Tr):.4f}")
    print(f"  B2/(lam2G): max={B2r.max():.4f} ; median={np.median(B2r):.4f}")
    print(f"  => T-margin (1-max) = {1-Tr.max():.4f} vs B2-margin = {1-B2r.max():.4f}")

    print("\n" + "=" * 96)
    print("TASK 2 — extremizer of T/(lam2 G) (largest = hardest for the TRUE inequality)")
    print("=" * 96)
    order = sorted(data, key=lambda nr: -nr[1]['T_ratio'])
    for nm, q in order[:8]:
        print(f"  {nm:16s} T/(lam2G)={q['T_ratio']:.4f}  B2/(lam2G)={q['B2_ratio']:.4f}  "
              f"lam2={q['lam']:.3f}  (B2 margin here: {1-q['B2_ratio']:.3f})")
    print(f"  TRUE extremizer (max T/(lam2G)) = {order[0][0]} at {order[0][1]['T_ratio']:.4f}")

    print("\n" + "=" * 96)
    print("TASK 5 — where B2 is TIGHT but T is SLACK (the gain from using T not B2')")
    print("=" * 96)
    print(f"  {'graph':16s} {'B2/(lam2G)':>11} {'T/(lam2G)':>10} {'gain=B2r-Tr':>12}")
    for nm, q in sorted(data, key=lambda nr: -(nr[1]['B2_ratio'] - nr[1]['T_ratio']))[:8]:
        print(f"  {nm:16s} {q['B2_ratio']:11.4f} {q['T_ratio']:10.4f} {q['B2_ratio']-q['T_ratio']:12.4f}")
    print("  (large gain = graphs where B2' is near-tight but T has lots of room => T-route easier)")

    print("\n" + "=" * 96)
    print("SUMMARY")
    print("=" * 96)
    print(f"  T<=lam2G margin (1-sup) = {1-Tr.max():.3f}; B2'<=lam2G margin = {1-B2r.max():.3f}.")
    print("  If T-margin >> B2-margin uniformly, T<=lam2G is genuinely easier; extremizer & gain above.")


if __name__ == "__main__":
    main()
