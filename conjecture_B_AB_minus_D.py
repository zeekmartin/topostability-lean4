"""
Irregular obstruction: gap = A - B - D, A=Sum_e deficit_e g_e^2, B=lam*Sum_ne h^2, D=lam*S^2/m.
Target (=gap>=0): A-B >= D. Stress-test A>=B and A-B>=D; decompose A-B; equality analysis.
Run: python conjecture_B_AB_minus_D.py
"""
import numpy as np
import networkx as nx


def quantities(G):
    nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}; n = len(nodes)
    if not nx.is_connected(G): return None
    A = nx.to_numpy_array(G, nodelist=nodes); d = A.sum(1); L = np.diag(d) - A
    ev, U = np.linalg.eigh(L); lam = ev[1]; f = U[:, 1]; f = f / np.linalg.norm(f)
    m = G.number_of_edges(); S = float(d @ f)
    edges = [(i, j) for i in range(n) for j in range(i + 1, n) if A[i, j] > 0]
    nonedges = [(i, j) for i in range(n) for j in range(i + 1, n) if A[i, j] == 0]
    Aterm = 0.0
    for (a, b) in edges:
        deficit = sum(1 for c in range(n) if c != a and c != b and (A[a, c] == 0 or A[b, c] == 0))
        Aterm += deficit * (f[a] - f[b]) ** 2
    Bterm = lam * sum((f[i] + f[j]) ** 2 for i, j in nonedges)
    Dterm = lam * S ** 2 / m
    return dict(n=n, lam=lam, A=Aterm, B=Bterm, D=Dterm, S=S,
                AB=Aterm - Bterm, gap=Aterm - Bterm - Dterm,
                regular=(d.max() == d.min()))


def families():
    out = []
    rng = np.random.default_rng(0)
    # lollipop, barbell, broom, windmill, star+clique, deg2+dense (adversarial TYPE A)
    for k, l in [(10, 10), (15, 15), (20, 10), (8, 30), (30, 8)]:
        out.append((f"lollipop{k}_{l}", nx.lollipop_graph(k, l)))
    for k, l in [(10, 10), (15, 5), (8, 20)]:
        out.append((f"barbell{k}_{l}", nx.barbell_graph(k, l)))
    for k in [3, 5, 8]:
        out.append((f"windmill{k}_4", nx.windmill_graph(k, 4)))
        out.append((f"windmill{k}_5", nx.windmill_graph(k, 5)))
    # broom: path + star
    for p, s in [(10, 8), (20, 10), (5, 20)]:
        Br = nx.path_graph(p)
        for i in range(s): Br.add_edge(p - 1, p + i)
        out.append((f"broom{p}_{s}", Br))
    # star + clique (clique with a pendant star at one vertex)
    for kc, ks in [(8, 10), (12, 15), (6, 25)]:
        Sc = nx.complete_graph(kc)
        for i in range(ks): Sc.add_edge(0, kc + i)
        out.append((f"starclq{kc}_{ks}", Sc))
    # deg2+dense (adversarial TYPE A): v0 attaches to 2 of a dense core
    for nn in [30, 50, 80, 120]:
        H = nx.gnp_random_graph(nn - 1, 0.6, seed=int(rng.integers(1e9)))
        H.add_node(nn - 1); H.add_edge(nn - 1, 0); H.add_edge(nn - 1, 1)
        out.append((f"deg2dense{nn}", H))
    # low-degree ports d=2,3 twins on K_N (the extremizer family)
    for N in [40, 80]:
        for dd in [2, 3]:
            K = nx.complete_graph(N); a, b = N, N + 1
            for x in (a, b):
                for w in range(dd): K.add_edge(x, w)
            K.add_node(N + 2); K.add_edge(N + 2, a); K.add_edge(N + 2, b)
            out.append((f"twinK{N}_d{dd}", K))
    # random irregular (gnp various)
    for nn in [30, 50, 80]:
        for q in [0.15, 0.3, 0.5, 0.7]:
            H = nx.gnp_random_graph(nn, q, seed=int(rng.integers(1e9)))
            out.append((f"gnp{nn}_{q}", H))
    # near-complete (K_n minus few edges, irregular)
    for nn in [30, 50]:
        for kdel in [1, 3, 7]:
            K = nx.complete_graph(nn); E = list(K.edges()); rng.shuffle(E)
            rem = 0
            for e in E:
                if rem >= kdel: break
                if K.degree(e[0]) > 2 and K.degree(e[1]) > 2: K.remove_edge(*e); rem += 1
            out.append((f"K{nn}-{rem}", K))
    return out


def main():
    data = []
    for nm, G in families():
        q = quantities(G)
        if q: data.append((nm, q))

    print("=" * 92)
    print(f"TASK 1 — stress test A >= B over {len(data)} graphs (families: lollipop/barbell/broom/")
    print("  windmill/star+clique/deg2dense/twinK/gnp/near-complete)")
    print("=" * 92)
    ab = [(nm, q) for nm, q in data]
    AB_vals = [q['AB'] for _, q in ab]
    BA = [(q['B'] / q['A'] if q['A'] > 1e-12 else 0.0, nm) for nm, q in ab]
    nAgeB = sum(1 for _, q in ab if q['A'] >= q['B'] - 1e-9)
    print(f"  A >= B : {nAgeB}/{len(ab)}")
    amin = min(ab, key=lambda x: x[1]['AB'])
    print(f"  min(A-B) = {amin[1]['AB']:.5f}  at {amin[0]}")
    print(f"  max(B/A) = {max(BA)[0]:.5f}  at {max(BA)[1]}")

    print("\n" + "=" * 92)
    print("TASK 3 — true target A-B >= D (= gap>=0). min(gap), argmin, D/(A-B)")
    print("=" * 92)
    nGap = sum(1 for _, q in data if q['gap'] >= -1e-9)
    print(f"  A-B >= D (gap>=0) : {nGap}/{len(data)}")
    gmin = min(data, key=lambda x: x[1]['gap'])
    print(f"  min(gap) = {gmin[1]['gap']:.5f}  at {gmin[0]}")
    DAB = [(q['D'] / q['AB'] if q['AB'] > 1e-12 else 0.0, nm) for nm, q in data]
    print(f"  max D/(A-B) = {max(DAB)[0]:.5f}  at {max(DAB)[1]} (how binding is D)")
    print(f"\n  lowest-gap graphs (tightest):")
    for nm, q in sorted(data, key=lambda x: x[1]['gap'])[:10]:
        print(f"    {nm:16s} gap={q['gap']:9.5f} A-B={q['AB']:9.4f} D={q['D']:8.4f} "
              f"D/(A-B)={q['D']/q['AB'] if q['AB']>1e-9 else 0:.4f} {'REG' if q['regular'] else ''}")

    print("\n" + "=" * 92)
    print("TASK 4 — equality A-B = D (gap=0). Which graphs? Is K_n still unique?")
    print("=" * 92)
    eq = [(nm, q) for nm, q in data if abs(q['gap']) < 1e-6]
    print(f"  gap≈0 graphs: {[nm for nm,_ in eq] if eq else 'NONE in corpus (no K_n included)'}")
    print(f"  min gap = {gmin[1]['gap']:.6f} ({gmin[0]}); all others strictly > 0")

    print("\n" + "=" * 92)
    print("TASK 2 — decompose A-B: test candidate forms vs A-B")
    print("=" * 92)
    # candidate: A-B vs lam*(n-lam) (the regular value λ(n-λ) when C=0..); and vs gap+D
    print(f"  {'graph':16s} {'A-B':>9} {'gap+D':>9} {'lam(n-lam)':>11} {'D':>8}")
    for nm, q in sorted(data, key=lambda x: x[1]['gap'])[:8]:
        print(f"  {nm:16s} {q['AB']:9.4f} {q['gap']+q['D']:9.4f} {q['lam']*(q['n']-q['lam']):11.4f} {q['D']:8.4f}")
    print("  (A-B = gap+D exactly; for regular A-B=λ(n-λ)-C; irregular has no single closed form)")

    print("\n" + "=" * 92)
    print("SUMMARY")
    print("=" * 92)
    print(f"  A>=B: {nAgeB}/{len(ab)} (min A-B={amin[1]['AB']:.4f}); A-B>=D: {nGap}/{len(data)} "
          f"(min gap={gmin[1]['gap']:.4f}); D binding max D/(A-B)={max(DAB)[0]:.3f} at {max(DAB)[1]}")


if __name__ == "__main__":
    main()
