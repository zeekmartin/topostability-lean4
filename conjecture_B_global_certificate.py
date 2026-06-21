"""
Search for a global inter-apex cancellation certificate for gap = lam2 G - T >= 0.

Exact decomposition (derived): gap = Σ_c (w* W_c - E_c), w* = lam2G/fDf, W_c=Σ_{N(c)}f², E_c=apex energy.
Eigenvector local constraint: m_c := Σ_{v∈N(c)} f_v = (d_c - lam) f_c  (the per-apex consequence of Lf=λf).
Tests: (1) exact decomposition; (2) per-apex u_c sign at w*; (3) CENTERED apex bound using m_c;
(4) matrix S-procedure circularity (lam2 simple => ker(L-λ)=span(f) => certificate == gap>=0).
Run: python conjecture_B_global_certificate.py
"""
import numpy as np
import networkx as nx


def setup(G):
    nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}; n = len(nodes)
    A = nx.to_numpy_array(G, nodelist=nodes); d = A.sum(1); L = np.diag(d) - A
    ev, U = np.linalg.eigh(L); lam = ev[1]; f = U[:, 1]; f = f / np.linalg.norm(f)
    m = G.number_of_edges(); S = float(d @ f); fDf = float(d @ (f * f))
    Gvar = (2 * fDf - lam - S ** 2 / m); lam2G = lam * Gvar
    return nodes, idx, n, A, d, lam, f, m, S, fDf, Gvar, lam2G, ev


def apex_terms(A, f, c):
    nb = np.where(A[c] > 0)[0]
    Wc = float(sum(f[v] ** 2 for v in nb))
    mc = float(sum(f[v] for v in nb))
    Ec = 0.0
    for a in nb:
        for b in nb:
            if A[a, b] > 0: Ec += (f[a] - f[b]) ** 2
    return Wc, mc, Ec, len(nb)  # Ec is ORDERED (=2*unordered)


def main():
    graphs = [("gnp20_.5", nx.gnp_random_graph(20, 0.5, seed=1)),
              ("gnp30_.4", nx.gnp_random_graph(30, 0.4, seed=2)),
              ("rr20_6", nx.random_regular_graph(6, 20, seed=1)),
              ("deg2dense40", None), ("K15", nx.complete_graph(15))]
    print("=" * 90)
    print("TASK 1 — exact decomposition gap = Σ_c (w* W_c - E_c/2),  w* = lam2G/fDf  (E_c ordered)")
    print("=" * 90)
    for nm, G in graphs:
        if nm == "deg2dense40":
            G = nx.gnp_random_graph(39, 0.65, seed=2); G.add_node(39); G.add_edge(39, 0); G.add_edge(39, 1)
        if not nx.is_connected(G): continue
        nodes, idx, n, A, d, lam, f, m, S, fDf, Gvar, lam2G, ev = setup(G)
        wstar = lam2G / fDf
        T = 0.0; dec = 0.0; mc_ok = True
        for c in range(n):
            Wc, mc, Ec, dc = apex_terms(A, f, c)
            T += Ec / 2                      # unordered T
            dec += wstar * Wc - Ec / 2
            if abs(mc - (d[c] - lam) * f[c]) > 1e-7: mc_ok = False
        gap = lam2G - T
        print(f"  {nm:14s} gap={gap:9.4f}  Σ_c(w*W_c-E_c/2)={dec:9.4f}  match={abs(gap-dec)<1e-6}  "
              f"local m_c=(d_c-λ)f_c: {mc_ok}")

    print("\n" + "=" * 90)
    print("TASK 2 — per-apex u_c = w* W_c - E_c/2 sign at w*=lam2G/fDf (< 2λ => more violations)")
    print("=" * 90)
    for nm, G in graphs:
        if nm == "deg2dense40":
            G = nx.gnp_random_graph(39, 0.65, seed=2); G.add_node(39); G.add_edge(39, 0); G.add_edge(39, 1)
        if not nx.is_connected(G): continue
        nodes, idx, n, A, d, lam, f, m, S, fDf, Gvar, lam2G, ev = setup(G)
        wstar = lam2G / fDf
        neg = 0; mn = 1e9
        for c in range(n):
            Wc, mc, Ec, dc = apex_terms(A, f, c); u = wstar * Wc - Ec / 2
            if u < -1e-9: neg += 1
            mn = min(mn, u)
        print(f"  {nm:14s} w*={wstar:.3f} (2λ={2*lam:.3f}) ; #u_c<0={neg}/{n} ; min u_c={mn:.4f}")
    print("  (w* < 2λ => stronger per-apex bound => MORE negatives than weight-2λ; no per-apex cert.)")

    print("\n" + "=" * 90)
    print("TASK 3 — CENTERED apex bound using m_c=(d_c-λ)f_c: Var_c = W_c - m_c²/d_c; E_c/2 <= w·Var_c?")
    print("=" * 90)
    for nm, G in graphs:
        if nm == "deg2dense40":
            G = nx.gnp_random_graph(39, 0.65, seed=2); G.add_node(39); G.add_edge(39, 0); G.add_edge(39, 1)
        if not nx.is_connected(G): continue
        nodes, idx, n, A, d, lam, f, m, S, fDf, Gvar, lam2G, ev = setup(G)
        # test centered per-apex: is E_c/2 <= 2λ·Var_c ?  and <= λ·Var_c ?
        neg2 = neg1 = 0; sumVar = 0.0
        for c in range(n):
            Wc, mc, Ec, dc = apex_terms(A, f, c)
            Var_c = Wc - mc ** 2 / dc if dc > 0 else Wc
            sumVar += Var_c
            if Ec / 2 > 2 * lam * Var_c + 1e-9: neg2 += 1
            if Ec / 2 > lam * Var_c + 1e-9: neg1 += 1
        print(f"  {nm:14s} E_c/2 <= 2λ·Var_c fails {neg2}/{n} ; <= λ·Var_c fails {neg1}/{n} ; "
              f"ΣVar_c={sumVar:.3f}")
    print("  (centered Var_c uses eigvec local mean; does centering remove the per-apex violations?)")

    print("\n" + "=" * 90)
    print("TASK 4 — matrix S-procedure circularity: is lam2 SIMPLE? (=> ker(L-λI)=span(f) => cert==gap>=0)")
    print("=" * 90)
    for nm, G in graphs:
        if nm == "deg2dense40":
            G = nx.gnp_random_graph(39, 0.65, seed=2); G.add_node(39); G.add_edge(39, 0); G.add_edge(39, 1)
        if not nx.is_connected(G): continue
        nodes, idx, n, A, d, lam, f, m, S, fDf, Gvar, lam2G, ev = setup(G)
        gaps_ev = ev[2] - ev[1]
        print(f"  {nm:14s} lam2={ev[1]:.4f} lam3={ev[2]:.4f} gap(lam3-lam2)={gaps_ev:.4f} "
              f"=> lam2 {'SIMPLE' if gaps_ev>1e-6 else 'DEGENERATE'}")
    print("  (lam2 simple => the only Fiedler-constraint subspace is span(f); the matrix-multiplier")
    print("   S-procedure M+(L-λI)Y+Y(L-λI)⪰0 is feasible IFF M⪰0 on span(f) IFF gap>=0 = CIRCULAR.)")

    print("\n" + "=" * 90)
    print("SUMMARY")
    print("=" * 90)
    print("  exact decomposition gap=Σ_c(w*W_c-E_c/2) [w*=lam2G/fDf]; per-apex u_c NOT >=0 (w*<2λ);")
    print("  centered Var_c test; matrix S-procedure circular for simple lam2. Report what survives.")


if __name__ == "__main__":
    main()
