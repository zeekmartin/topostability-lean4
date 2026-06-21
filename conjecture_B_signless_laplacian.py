"""
Signless-Laplacian route for B2' <= lam2 G, i.e. fᵀL_w f <= lam2 (fᵀQ f - S²/m).
L_w: weighted Laplacian, w_e = min(d_a,d_b)-1; Q = D+A signless Laplacian; f = Fiedler; S=Σ d_v f_v.

TASK1 operator form (regular check).  TASK2 L_w decomposition.  TASK3 Cauchy-Schwarz bound
(Δ-1)lam2 and the test Δ-1 <= fᵀQf - S²/m.  TASK4 fᵀQf vs signless eigenvalues + projection.
Run: python conjecture_B_signless_laplacian.py
"""
import numpy as np
import networkx as nx


def quantities(G):
    nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}; n = len(nodes)
    A = nx.to_numpy_array(G, nodelist=nodes); d = A.sum(1); D = np.diag(d)
    L = D - A; Q = D + A
    ev, U = np.linalg.eigh(L); lam = ev[1]; f = U[:, 1]; f = f / np.linalg.norm(f)
    m = G.number_of_edges(); S = float(d @ f)
    fQf = float(f @ Q @ f); fLwf = 0.0
    for u, v in G.edges():
        a, b = idx[u], idx[v]; fLwf += (min(d[a], d[b]) - 1) * (f[a] - f[b]) ** 2
    Gvar = fQf - S ** 2 / m           # = lam2G/lam2 (the RHS quantity / lam2)
    B2 = fLwf
    RHS = lam * Gvar
    # signless Laplacian spectrum + Fiedler projection
    qev, qU = np.linalg.eigh(Q); qmin = float(qev[0]); q2 = float(qev[1])
    proj = qU.T @ f                   # coords of f in Q-eigenbasis
    return dict(n=n, m=m, lam=lam, Delta=float(d.max()), delta=float(d.min()),
                fQf=fQf, S=S, Gvar=Gvar, B2=B2, RHS=RHS, gap=RHS - B2,
                qmin=qmin, q2=q2, wmax=float(max((min(d[idx[u]], d[idx[v]]) - 1)
                                                 for u, v in G.edges())))


def corpus():
    rng = np.random.default_rng(0); out = []
    for n in [20, 40, 60]:
        for q in [0.2, 0.35, 0.5, 0.7, 0.9]:
            H = nx.gnp_random_graph(n, q, seed=int(rng.integers(1e9)))
            if nx.is_connected(H): out.append((f"gnp{n}_{q}", H))
        for r in [4, n // 3]:
            if (r * n) % 2 == 0 and 3 <= r <= n - 1:
                out.append((f"rr{n}_{r}", nx.random_regular_graph(r, n, seed=1)))
        out.append((f"K{n}", nx.complete_graph(n)))
    # deg2+dense (the hard family)
    for n in [40, 80]:
        H = nx.gnp_random_graph(n - 1, 0.65, seed=2); H.add_node(n - 1)
        H.add_edge(n - 1, 0); H.add_edge(n - 1, 1)
        if nx.is_connected(H): out.append((f"deg2dense{n}", H))
    # lollipop (TYPE B)
    out.append(("lollipop", nx.lollipop_graph(20, 20)))
    return out


def main():
    data = [(nm, quantities(G)) for nm, G in corpus()]

    print("=" * 92)
    print("TASK 1 — operator/Rayleigh check: B2 <= RHS (the target) holds on corpus?")
    print("=" * 92)
    ok = sum(1 for _, q in data if q['B2'] <= q['RHS'] + 1e-9)
    print(f"  B2' <= lam2 G : {ok}/{len(data)}")

    print("\n" + "=" * 92)
    print("TASK 3 — Cauchy-Schwarz: B2 <= wmax*lam2 = (loose); and test (Δ-1) <= fᵀQf - S²/m ?")
    print("=" * 92)
    print(f"  {'graph':14s} {'Δ-1':>6} {'fQf-S²/m':>10} {'(Δ-1)<=?':>9} {'B2/lam2':>9} {'wmax':>6} "
          f"{'B2<=wmax*lam2':>13}")
    t3 = 0; cs = 0
    for nm, q in data:
        cond = (q['Delta'] - 1) <= q['Gvar'] + 1e-9
        t3 += cond
        csb = q['B2'] <= q['wmax'] * q['lam'] + 1e-9; cs += csb
        print(f"  {nm:14s} {q['Delta']-1:6.1f} {q['Gvar']:10.4f} {str(cond):>9} "
              f"{q['B2']/q['lam']:9.4f} {q['wmax']:6.0f} {str(csb):>13}")
    print(f"  (Δ-1) <= fᵀQf-S²/m : {t3}/{len(data)}   [if FALSE: the CS route is too lossy]")
    print(f"  B2 <= wmax*lam2 (Cauchy-Schwarz, valid): {cs}/{len(data)}")

    print("\n" + "=" * 92)
    print("TASK 3b — WHY CS fails: wmax=Δ-1=O(n) but Gvar=fᵀQf-S²/m=O(1); ratio blows up")
    print("=" * 92)
    for nm, q in data:
        if nm.startswith("K") or nm.startswith("deg2"):
            print(f"  {nm:14s} Δ-1={q['Delta']-1:.0f}  Gvar={q['Gvar']:.3f}  "
                  f"(Δ-1)/Gvar={(q['Delta']-1)/q['Gvar']:.1f}  [need <=1 for CS, but it's >>1]")

    print("\n" + "=" * 92)
    print("TASK 4 — signless Laplacian: fᵀQf vs q_min,q2; is fᵀQf >= q2 (2nd-smallest Q-eig)?")
    print("=" * 92)
    print(f"  {'graph':14s} {'fᵀQf':>9} {'q_min':>8} {'q2':>8} {'fᵀQf>=q2?':>10} {'fᵀQf-S²/m':>10}")
    bd = 0
    for nm, q in data:
        cond = q['fQf'] >= q['q2'] - 1e-9; bd += cond
        print(f"  {nm:14s} {q['fQf']:9.4f} {q['qmin']:8.4f} {q['q2']:8.4f} {str(cond):>10} "
              f"{q['Gvar']:10.4f}")
    print(f"  fᵀQf >= q2 : {bd}/{len(data)}  (Fiedler need not align with Q's low modes)")
    print(f"  fᵀQf >= q_min always (Rayleigh, ‖f‖=1): "
          f"{sum(1 for _,q in data if q['fQf'] >= q['qmin']-1e-9)}/{len(data)}")

    print("\n" + "=" * 92)
    print("TASK 1b — regular-core sanity: L_w=(d-1)L, Q=(d+1)I on Fiedler; (d-1)lam2 <= lam2(2d-lam2)")
    print("=" * 92)
    for nm, q in [(nm, q) for nm, q in data if nm.startswith("rr") or nm.startswith("K")][:5]:
        d = q['Delta']
        print(f"  {nm:12s} d={d:.0f} lam2={q['lam']:.3f}: (d-1)={d-1:.0f} <= (2d-lam2)="
              f"{2*d-q['lam']:.2f} ? {(d-1)<=2*d-q['lam']+1e-9}  [<=> lam2<=d+1]")

    print("\n" + "=" * 92)
    print("SUMMARY")
    print("=" * 92)
    print("  Report: does the scalar CS route (Δ-1 <= Gvar) work? (expect NO, Δ-1=O(n)>>Gvar=O(1)).")
    print("  Does fᵀQf>=q2 hold? The operator inequality L_w <= lam2(Q - S²/m·proj) is the real target.")


if __name__ == "__main__":
    main()
