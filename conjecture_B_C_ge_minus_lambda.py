"""
Prove/test C >= -lam, where C = (1/2)(A+I) = Sum_e (d_h-d_l) f_h (f_h-f_l) (h=high-deg endpoint).
Equivalent forms: C = lam*d_eff - Sum_e min(d_a,d_b) g^2; A = Sum_v(d_v^2 - s_v)f_v^2 (s_v=Sum_{u~v}d_u).
Test CS sufficient conditions and vertex representation.
Run: python conjecture_B_C_ge_minus_lambda.py
"""
import numpy as np
import networkx as nx


def quant(G, eigvec=None):
    G = nx.convert_node_labels_to_integers(G); n = G.number_of_nodes()
    if not nx.is_connected(G): return None
    Am = nx.to_numpy_array(G); d = Am.sum(1); L = np.diag(d) - Am
    ev, U = np.linalg.eigh(L); lam = ev[1]
    f = U[:, 1] if eigvec is None else eigvec
    f = f / np.linalg.norm(f)
    d_eff = float(d @ (f * f))
    edges = [(i, j) for i in range(n) for j in range(i + 1, n) if Am[i, j] > 0]
    lam_e = sum((f[a] - f[b]) ** 2 for a, b in edges)
    # C and pieces (h=high-deg endpoint)
    C = 0.0; Q = 0.0; J = 0.0; I = 0.0
    for a, b in edges:
        if d[a] >= d[b]: h, l = a, b
        else: h, l = b, a
        delta = d[h] - d[l]; g = f[h] - f[l]
        C += delta * f[h] * g
        Q += delta ** 2 * f[h] ** 2
        J += delta * f[h] ** 2
        I += delta * (f[h] - f[l]) ** 2
    # A via vertex form
    s = Am @ d                          # s_v = sum of neighbor degrees
    A_vertex = float(((d ** 2 - s) * f ** 2).sum())
    A_edge = float(sum((d[a] - d[b]) * (f[a] ** 2 - f[b] ** 2) for a, b in edges))
    return dict(n=n, lam=lam_e, d_eff=d_eff, C=C, Q=Q, J=J, I=I,
                A_vertex=A_vertex, A_edge=A_edge,
                id_A=abs(A_vertex - A_edge), id_C=abs(C - 0.5 * (A_edge + I)),
                CS1=Q / lam_e if lam_e > 0 else 0.0,            # need <=1 for C>=-lam
                CS2=(J * I) / lam_e ** 2 if lam_e > 0 else 0.0,  # need <=1
                C_over_lam=C / lam_e if lam_e > 0 else 0.0)


def corpus():
    out = []; rng = np.random.default_rng(0)
    def d2(nn, q, s):
        H = nx.gnp_random_graph(nn - 1, q, seed=s); H.add_node(nn - 1); H.add_edge(nn - 1, 0); H.add_edge(nn - 1, 1); return H
    def twin(N, dd):
        K = nx.complete_graph(N); a, b = N, N + 1
        for x in (a, b):
            for w in range(dd): K.add_edge(x, w)
        K.add_node(N + 2); K.add_edge(N + 2, a); K.add_edge(N + 2, b); return K
    def star(kc, ks):
        Gr = nx.complete_graph(kc)
        for i in range(ks): Gr.add_edge(0, kc + i)
        return Gr
    for nn in [30, 50, 80]:
        for q in [0.3, 0.5, 0.7, 0.9]: out.append((f"deg2d{nn}_{q}", "TYPEA", d2(nn, q, int(rng.integers(1e9)))))
    for N in [30, 50, 80]:
        for dd in [2, 3, 4]: out.append((f"twin{N}_{dd}", "TYPEA", twin(N, dd)))
    for kc, ks in [(10, 6), (12, 8), (15, 15)]: out.append((f"star{kc}_{ks}", "CLIQUESTAR", star(kc, ks)))
    for k, l in [(10, 10), (15, 12)]: out.append((f"lolli{k}_{l}", "TYPEB", nx.lollipop_graph(k, l)))
    for k, l in [(8, 8)]: out.append((f"barb{k}_{l}", "TYPEB", nx.barbell_graph(k, l)))
    for nn in [25, 40, 60]:
        for q in [0.3, 0.5, 0.7]: out.append((f"gnp{nn}_{q}", "RANDOM", nx.gnp_random_graph(nn, q, seed=int(rng.integers(1e9)))))
    for nn in [20, 40]:
        for r in [4, nn // 2]:
            if 3 <= r < nn and (r * nn) % 2 == 0: out.append((f"rr{nn}_{r}", "REGULAR", nx.random_regular_graph(r, nn, seed=1)))
    # degenerate: cocktail, complete multipartite
    out.append(("cocktail6", "DEGEN", nx.complete_multipartite_graph(*([2] * 6))))
    out.append(("Kmp333", "DEGEN", nx.complete_multipartite_graph(3, 3, 3)))
    for nn in [10, 20, 30, 50]: out.append((f"K{nn}", "REGULAR", nx.complete_graph(nn)))
    return out


def main():
    data = [(nm, cl, q) for nm, cl, G in corpus() for q in [quant(G)] if q is not None]

    print("=" * 92)
    print("TASK 1 — vertex form A = Σ_v(d_v²-s_v)f_v² (s_v=Σ_{u~v}d_u); and C=½(A+I) check")
    print("=" * 92)
    print(f"  max|A_vertex - A_edge| = {max(q['id_A'] for _,_,q in data):.2e}")
    print(f"  max|C - ½(A+I)|        = {max(q['id_C'] for _,_,q in data):.2e}")

    print("\n" + "=" * 92)
    print("TASK 5 — C >= -λ on expanded corpus (the leaf)")
    print("=" * 92)
    ok = sum(1 for _, _, q in data if q['C'] >= -q['lam'] - 1e-7)
    mn = min(data, key=lambda x: x[2]['C_over_lam'])
    print(f"  C >= -λ : {ok}/{len(data)}; min C/λ = {mn[2]['C_over_lam']:.4f} at {mn[0]} (need >= -1)")

    print("\n" + "=" * 92)
    print("TASK 3 — CS sufficient conditions (need <= 1):")
    print("=" * 92)
    cs1 = sum(1 for _, _, q in data if q['CS1'] <= 1 + 1e-7)
    cs2 = sum(1 for _, _, q in data if q['CS2'] <= 1 + 1e-7)
    print(f"  CS1: Q/λ = Σ(d_h-d_l)²f_h²/λ <= 1 : {cs1}/{len(data)}  (max {max(q['CS1'] for _,_,q in data):.2f})")
    print(f"  CS2: J·I/λ² <= 1 (J=Σ(d_h-d_l)f_h², I=Σ(d_h-d_l)g²) : {cs2}/{len(data)}  "
          f"(max {max(q['CS2'] for _,_,q in data):.2f})")
    print(f"  {'graph':12s} {'class':>11} {'C/λ':>8} {'CS1=Q/λ':>9} {'CS2=JI/λ²':>10}")
    for nm, cl, q in sorted(data, key=lambda x: x[2]['C_over_lam'])[:12]:
        print(f"  {nm:12s} {cl:>11} {q['C_over_lam']:8.4f} {q['CS1']:9.3f} {q['CS2']:10.3f}")

    print("\n" + "=" * 92)
    print("TASK 4 — vertex bound: per-vertex c_v (C=Σ_v c_v, c_v over lower-deg neighbors)")
    print("=" * 92)
    # c_v = f_v * sum_{u~v, d_u<d_v}(d_v-d_u)(f_v-f_u); check min c_v / lam
    rows = []
    for nm, cl, G in corpus():
        G2 = nx.convert_node_labels_to_integers(G); n = G2.number_of_nodes()
        if not nx.is_connected(G2): continue
        Am = nx.to_numpy_array(G2); d = Am.sum(1); L = np.diag(d) - Am
        ev, U = np.linalg.eigh(L); lam = ev[1]; f = U[:, 1]; f = f / np.linalg.norm(f)
        edges = [(i, j) for i in range(n) for j in range(i + 1, n) if Am[i, j] > 0]
        lam_e = sum((f[a] - f[b]) ** 2 for a, b in edges)
        cv = np.zeros(n)
        for a, b in edges:
            h, l = (a, b) if d[a] >= d[b] else (b, a)
            cv[h] += (d[h] - d[l]) * f[h] * (f[h] - f[l])
        rows.append((nm, cl, cv.min() / lam_e, (cv >= -1e-9).all()))
    worst = min(rows, key=lambda x: x[2])
    allpos = sum(1 for r in rows if r[3])
    print(f"  per-vertex c_v >= 0 everywhere: {allpos}/{len(rows)} (if not, no per-vertex bound)")
    print(f"  worst min c_v/λ = {worst[2]:.4f} at {worst[0]} ({worst[1]})")

    print("\n" + "=" * 92)
    print("SUMMARY")
    print("=" * 92)
    print(f"  C>=-λ (leaf): {ok}/{len(data)}; vertex form A exact ({max(q['id_A'] for _,_,q in data):.1e}).")
    print(f"  CS1 {cs1}/{len(data)}, CS2 {cs2}/{len(data)} — "
          f"{'a CS route works!' if max(cs1,cs2)==len(data) else 'CS routes TOO WEAK (fail).'}")


if __name__ == "__main__":
    main()
