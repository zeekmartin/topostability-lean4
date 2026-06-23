"""
3x3 compression route for lam+S^2/m<=d_eff+1.
Bases: U1=span{f,1}, U2=span{f,1,Df}, U3=span{f,1,d}, U4=span{f,1,P_perp Df}.
For C = A restricted to U (orthonormal basis): test mu_min(C)>=-1, and whether mu_min(C)>=-1 (or
C+I>=0) IMPLIES target. Note Df and d differ only by... d=D1, Df=D applied to f. P_perp Df is the
part of Df orthogonal to span{f,1}.
Run: python conjecture_B_3x3_compression_irregular.py
"""
import numpy as np
import networkx as nx


def gram_orthonormal(vecs, n):
    """Gram-Schmidt; return orthonormal basis matrix (n x k), dropping ~0 vectors."""
    B = []
    for v in vecs:
        w = v.copy().astype(float)
        for u in B:
            w = w - (u @ w) * u
        nv = np.linalg.norm(w)
        if nv > 1e-9:
            B.append(w / nv)
    return np.array(B).T if B else np.zeros((n, 0))


def analyze(G):
    G = nx.convert_node_labels_to_integers(G); n = G.number_of_nodes()
    if not nx.is_connected(G): return None
    A = nx.to_numpy_array(G); d = A.sum(1); L = np.diag(d) - A
    ev, U = np.linalg.eigh(L); lam = ev[1]; f = U[:, 1]; f = f / np.linalg.norm(f)
    m = G.number_of_edges(); S = float(d @ f); d_eff = float(d @ (f * f))
    one = np.ones(n); Df = d * f
    target_ok = (lam + S ** 2 / m <= d_eff + 1 + 1e-9)
    res = {}
    bases = {"U1_f1": [f, one], "U2_f1Df": [f, one, Df], "U3_f1d": [f, one, d],
             "U4_f1PDf": [f, one, Df]}  # U4 same vecs; GS makes Df-perp automatically
    for name, vecs in bases.items():
        E = gram_orthonormal(vecs, n)
        if E.shape[1] < 2: res[name] = None; continue
        C = E.T @ A @ E
        mm = float(np.linalg.eigvalsh(C)[0])
        res[name] = mm
    return dict(n=n, lam=lam, S=S, m=m, d_eff=d_eff, S2m=S ** 2 / m, target_ok=target_ok,
                target_slack=(d_eff + 1) - (lam + S ** 2 / m), **{f"mm_{k}": v for k, v in res.items()})


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
        for q in [0.4, 0.6, 0.8, 0.9]: out.append((f"deg2d{nn}_{q}", deg2dense(nn, q, int(rng.integers(1e9)))))
    for N in [30, 50, 80]:
        for dd in [2, 3, 4]: out.append((f"twin{N}_{dd}", twin(N, dd)))
    for kc, ks in [(10, 6), (12, 8)]: out.append((f"star{kc}_{ks}", star(kc, ks)))
    for k, l in [(10, 10), (15, 12)]: out.append((f"lolli{k}_{l}", nx.lollipop_graph(k, l)))
    out.append(("barb8_8", nx.barbell_graph(8, 8)))
    for nn in [25, 40, 60]:
        for q in [0.3, 0.5, 0.7, 0.85]: out.append((f"gnp{nn}_{q}", nx.gnp_random_graph(nn, q, seed=int(rng.integers(1e9)))))
    for nn in [12, 20]: out.append((f"K{nn}", nx.complete_graph(nn)))
    for nn in [30, 50]:
        for kd in [1, 4, 10]:
            K = nx.complete_graph(nn); E = list(K.edges()); rng.shuffle(E); rem = 0
            for e in E:
                if rem >= kd: break
                if K.degree(e[0]) > 2 and K.degree(e[1]) > 2: K.remove_edge(*e); rem += 1
            out.append((f"K{nn}-{rem}", K))
    return out


def main():
    data = [(nm, q) for nm, G in corpus() for q in [analyze(G)] if q is not None]
    print(f"  {len(data)} graphs; target holds: {sum(1 for _,q in data if q['target_ok'])}/{len(data)}")

    print("\n" + "=" * 92)
    print("TASK 2 — μ_min(C) >= -1 for each compression (need: holds AND implies target)")
    print("=" * 92)
    for key in ["mm_U1_f1", "mm_U2_f1Df", "mm_U3_f1d"]:
        vals = [q[key] for _, q in data if q[key] is not None]
        ok = sum(1 for v in vals if v >= -1 - 1e-7)
        print(f"  {key:14s}: μ_min>=-1 in {ok}/{len(vals)}; min = {min(vals):.4f}")
    print("  (note: U2,U3,U4 reduce to U1 when Df in span{f,1}, i.e. regular -> 2x2)")

    print("\n" + "=" * 92)
    print("TASK 3 — does μ_min(C_3x3) >= -1 IMPLY target? (compare margins on tight cases)")
    print("=" * 92)
    print(f"  {'graph':12s} {'tgt slack':>10} {'mm_U1':>8} {'mm_U2(Df)':>9} {'mm_U3(d)':>9}")
    for nm, q in sorted(data, key=lambda x: x[1]['target_slack'])[:12]:
        print(f"  {nm:12s} {q['target_slack']:10.5f} {q['mm_U1_f1']:8.4f} "
              f"{(q['mm_U2_f1Df'] if q['mm_U2_f1Df'] is not None else float('nan')):9.4f} "
              f"{(q['mm_U3_f1d'] if q['mm_U3_f1d'] is not None else float('nan')):9.4f}")

    print("\n" + "=" * 92)
    print("TASK 3b — KEY TEST: is target slack >= 0 EXACTLY when μ_min(C)>=-1 for some C? correlate")
    print("=" * 92)
    # the real question: does mu_min(U2 or U3)>=-1 give a SHARPER (target-implying) bound than U1?
    # test: does (mu_min(C)>=-1) hold with the SAME tightness as target? min over corpus:
    for key in ["mm_U1_f1", "mm_U2_f1Df", "mm_U3_f1d"]:
        vals = [(q[key], q['target_slack'], nm) for nm, q in data if q[key] is not None]
        # graphs where mu_min(C) is tight (near -1) -- is target also tight there?
        tightest = min(vals, key=lambda x: x[0])
        print(f"  {key:14s}: tightest μ_min={tightest[0]:.4f} at {tightest[2]} (target slack there={tightest[1]:.4f})")

    print("\n" + "=" * 92)
    print("TASK 6 — the witness direction: eigenvector of (A+I) achieving min on span{f,1,...}")
    print("=" * 92)
    # for the 3x3 to imply target via a determinant minor, check: does C+I have the target as a 2x2 minor?
    # Simpler: report whether ANY 3x3 mu_min>=-1 is STRICTLY tighter than 2x2 (i.e. catches more)
    for nm, q in [("deg2d80_0.9", None), ("twin80_2", None), ("K12", None)]:
        q = dict(data).get(nm)
        if q is None: continue
        print(f"  {nm:12s} U1={q['mm_U1_f1']:.4f} U2(Df)={q['mm_U2_f1Df']:.4f} U3(d)={q['mm_U3_f1d']:.4f} "
              f"target_slack={q['target_slack']:.4f}")

    print("\n" + "=" * 92)
    print("SUMMARY / TASK 5")
    print("=" * 92)
    for key in ["mm_U1_f1", "mm_U2_f1Df", "mm_U3_f1d"]:
        vals = [q[key] for _, q in data if q[key] is not None]
        print(f"  {key}: μ_min>=-1 {sum(1 for v in vals if v>=-1-1e-7)}/{len(vals)} (min {min(vals):.4f})")


if __name__ == "__main__":
    main()
