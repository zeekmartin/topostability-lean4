"""
Search for an EXACT global identity gap = PositiveTerm + Residual (Residual >= 0 structurally),
using ONLY the Fiedler equation Lf=λf (no case split, no local apex bounds).

Key elimination: Af = Df - λf  =>  fᵀA²f = ||Af||² = Σ_v (d_v-λ)² f_v².
gap = 2λ fᵀDf - λ² - λ S²/m - T   (T = fᵀL_t f, t-weighted Laplacian).
Run: python conjecture_B_global_identity.py
"""
import numpy as np
import networkx as nx


def Q(G):
    nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}; n = len(nodes)
    A = nx.to_numpy_array(G, nodelist=nodes); d = A.sum(1); L = np.diag(d) - A
    ev, U = np.linalg.eigh(L); lam = ev[1]; f = U[:, 1]; f = f / np.linalg.norm(f)
    m = G.number_of_edges(); S = float(d @ f); fDf = float(d @ (f * f))
    A2 = A @ A
    T = sum(A2[idx[u], idx[v]] * (f[idx[u]] - f[idx[v]]) ** 2 for u, v in G.edges())
    gap = lam * (2 * fDf - lam - S ** 2 / m) - T
    fA2f = float(f @ A2 @ f)                 # = ||Af||^2
    Af = A @ f
    elim = float(np.sum((d - lam) ** 2 * f * f))   # Σ(d_v-λ)² f_v²
    return dict(n=n, A=A, d=d, lam=lam, f=f, m=m, S=S, fDf=fDf, T=T, gap=gap, A2=A2,
                fA2f=fA2f, Afnorm=float(Af @ Af), elim=elim, idx=idx, G=G)


def corpus():
    out = [("K10", nx.complete_graph(10)), ("K20", nx.complete_graph(20))]
    Ge = nx.complete_graph(20); Ge.remove_edge(0, 1); out.append(("K20-e", Ge))
    out += [("gnp20_.5", nx.gnp_random_graph(20, 0.5, seed=1)),
            ("gnp30_.4", nx.gnp_random_graph(30, 0.4, seed=2)),
            ("rr20_4", nx.random_regular_graph(4, 20, seed=1)),
            ("rr30_6", nx.random_regular_graph(6, 30, seed=1)),
            ("cycle30", nx.cycle_graph(30))]
    H = nx.gnp_random_graph(39, 0.65, seed=2); H.add_node(39); H.add_edge(39, 0); H.add_edge(39, 1)
    out.append(("deg2dense40", H))
    return [(nm, G) for nm, G in out if nx.is_connected(G)]


def main():
    data = [(nm, Q(G)) for nm, G in corpus()]

    print("=" * 92)
    print("TASK 1 — clean elimination: fᵀA²f = ||Af||² = Σ_v(d_v-λ)²f_v²  (eliminates 2-step nbr sums)")
    print("=" * 92)
    for nm, q in data:
        print(f"  {nm:12s} fᵀA²f={q['fA2f']:10.4f}  ||Af||²={q['Afnorm']:10.4f}  Σ(d-λ)²f²={q['elim']:10.4f}  "
              f"match={abs(q['fA2f']-q['elim'])<1e-6}")
    print("  (BUT T uses A⊙A² [t-weighted], NOT A²; so fᵀA²f does not directly simplify T.)")

    print("\n" + "=" * 92)
    print("TASK 2/4 — candidate split gap = PositiveTerm + Residual; test PositiveTerm>=0 & Residual sign")
    print("=" * 92)
    print(f"  {'graph':12s} {'gap':>9} {'λfDf-T':>9} {'2λfDf-T':>9} {'-Required':>10} "
          f"{'R1':>9}")
    for nm, q in data:
        lam, fDf, T, S, m, d, f = q['lam'], q['fDf'], q['T'], q['S'], q['m'], q['d'], q['f']
        Req = lam * (lam + S ** 2 / m - fDf)
        termA1 = lam * fDf - T            # is T <= λfDf? (stronger aggregate)
        termA2 = 2 * lam * fDf - T        # aggregate Poincare slack (>=0)
        R1 = 2 * lam * float(np.sum((d - lam) ** 2 * f * f / d)) - lam ** 2 - lam * S ** 2 / m
        print(f"  {nm:12s} {q['gap']:9.4f} {termA1:9.4f} {termA2:9.4f} {-Req:10.4f} {R1:9.4f}")
    print("  (gap = (λfDf - T) - Required = (2λfDf-T) - λ(λ+S²/m).  λfDf-T sign? Required sign? R1 sign?)")

    print("\n" + "=" * 92)
    print("TASK 3/5 — is any candidate Residual STRUCTURALLY >=0? test signs across corpus")
    print("=" * 92)
    # (i) is T <= lam fDf (=> gap = (λfDf-T) - Required, first term >=0)?
    a1 = [lam_fDf_T(q) for nm, q in data]
    print(f"  T <= λ·fDf : {sum(1 for x in a1 if x>=-1e-9)}/{len(a1)}  (min λfDf-T = {min(a1):.4f})")
    # (ii) R1 >= 0 ?
    r1 = []
    for nm, q in data:
        lam, S, m, d, f = q['lam'], q['S'], q['m'], q['d'], q['f']
        r1.append(2 * lam * float(np.sum((d - lam) ** 2 * f * f / d)) - lam ** 2 - lam * S ** 2 / m)
    print(f"  R1 >= 0    : {sum(1 for x in r1 if x>=-1e-9)}/{len(r1)}  (min R1 = {min(r1):.4f})")
    # (iii) Cauchy-Schwarz residual: ||Af||²·||f||² - (fᵀAf)² >= 0 (Gram, always true); relate to gap?
    cs = []
    for nm, q in data:
        fAf = q['fDf'] - q['lam']          # fᵀAf = fᵀDf - λ
        cs.append(q['fA2f'] - fAf ** 2)    # Gram det of (f, Af) (>=0 always)
    print(f"  Gram(f,Af)=||Af||²-(fᵀAf)² >= 0 : {sum(1 for x in cs if x>=-1e-9)}/{len(cs)} (always; = Σ(d-λ)²f² - (fDf-λ)²)")

    print("\n" + "=" * 92)
    print("TASK 4 — exact residual values on K_n, K_n-e, deg2dense, regular sparse")
    print("=" * 92)
    print(f"  {'graph':12s} {'gap':>9} {'Required':>10} {'λfDf-T':>9} {'R1':>9} {'Gram(f,Af)':>11}")
    for nm, q in data:
        if nm in ("K20", "K20-e", "deg2dense40", "rr20_4", "cycle30"):
            lam, fDf, T, S, m, d, f = q['lam'], q['fDf'], q['T'], q['S'], q['m'], q['d'], q['f']
            Req = lam * (lam + S ** 2 / m - fDf)
            R1 = 2 * lam * float(np.sum((d - lam) ** 2 * f * f / d)) - lam ** 2 - lam * S ** 2 / m
            fAf = fDf - lam; gram = q['fA2f'] - fAf ** 2
            print(f"  {nm:12s} {q['gap']:9.4f} {Req:10.4f} {lam*fDf-T:9.4f} {R1:9.4f} {gram:11.4f}")

    print("\n" + "=" * 92)
    print("SUMMARY")
    print("=" * 92)
    print("  Report which (if any) candidate residual is structurally >=0; if none, the global identity")
    print("  reduces to gap>=0 itself (no independent certificate).")


def lam_fDf_T(q):
    return q['lam'] * q['fDf'] - q['T']


if __name__ == "__main__":
    main()
