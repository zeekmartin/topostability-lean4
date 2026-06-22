"""
Analyze correction terms: gap = A - B - C - D, A=Σmdeg·D_v, B=λΣ_ne h², C=Σ_c Ēbar_c, D=λS²/m.
KEY: A - C = Σ_e deficit_e g_e² (real positive term). So gap = (A-C) - B - D = Σdef·g² - B - D.
Run: python conjecture_B_correction_terms.py
"""
import numpy as np
import networkx as nx


def terms(G):
    nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}; n = len(nodes)
    A = nx.to_numpy_array(G, nodelist=nodes); d = A.sum(1); L = np.diag(d) - A
    ev, U = np.linalg.eigh(L); lam = ev[1]; f = U[:, 1]; f = f / np.linalg.norm(f)
    m = G.number_of_edges(); S = float(d @ f); mdeg = (n - 1) - d
    A2 = A @ A
    edges = [(i, j) for i in range(n) for j in range(i + 1, n) if A[i, j] > 0]
    nonedges = [(i, j) for i in range(n) for j in range(i + 1, n) if A[i, j] == 0]
    Dloc = np.array([sum((f[i] - f[j]) ** 2 for j in range(n) if A[i, j] > 0) for i in range(n)])
    Aterm = float(np.sum(mdeg * Dloc))
    Bterm = lam * sum((f[i] + f[j]) ** 2 for i, j in nonedges)
    # C = Σ_e tbar_e g_e²  (common non-neighbors)
    Cterm = 0.0; defsum = 0.0
    for (a, b) in edges:
        tbar = sum(1 for c in range(n) if c != a and c != b and A[a, c] == 0 and A[b, c] == 0)
        deficit = sum(1 for c in range(n) if c != a and c != b and (A[a, c] == 0 or A[b, c] == 0))
        g2 = (f[a] - f[b]) ** 2
        Cterm += tbar * g2; defsum += deficit * g2
    Dterm = lam * S ** 2 / m
    T = sum(A2[i, j] * (f[i] - f[j]) ** 2 for (i, j) in edges)
    gap = lam * (2 * float(d @ (f * f)) - lam - S ** 2 / m) - T
    return dict(n=n, lam=lam, A=Aterm, B=Bterm, C=Cterm, D=Dterm, defsum=defsum, gap=gap, S=S)


def corpus():
    out = [("gnp20_.5", nx.gnp_random_graph(20, 0.5, seed=1)),
           ("gnp30_.4", nx.gnp_random_graph(30, 0.4, seed=2)),
           ("gnp20_.8", nx.gnp_random_graph(20, 0.8, seed=3)),
           ("gnp40_.3", nx.gnp_random_graph(40, 0.3, seed=4)),
           ("rr20_6", nx.random_regular_graph(6, 20, seed=1)),
           ("rr30_10", nx.random_regular_graph(10, 30, seed=1)),
           ("cycle20", nx.cycle_graph(20)),
           ("path20", nx.path_graph(20))]
    H = nx.gnp_random_graph(39, 0.65, seed=2); H.add_node(39); H.add_edge(39, 0); H.add_edge(39, 1)
    out.append(("deg2dense40", H))
    Ge = nx.complete_graph(20); Ge.remove_edge(0, 1); out.append(("K20-e", Ge))
    # lollipop (strong irregularity + bottleneck)
    out.append(("lollipop", nx.lollipop_graph(15, 15)))
    return [(nm, G) for nm, G in out if nx.is_connected(G)]


def main():
    data = [(nm, terms(G)) for nm, G in corpus()]

    print("=" * 100)
    print("Real structure: gap = (A-C) - B - D = Σdef·g² - λΣ_ne h² - λS²/m. Verify A-C=Σdef·g².")
    print("=" * 100)
    print(f"  {'graph':12s} {'A-C':>9} {'Σdef·g²':>9} {'B=λΣh²':>9} {'D=λS²/m':>9} {'gap':>9} {'check':>6}")
    for nm, q in data:
        AC = q['A'] - q['C']
        recon = AC - q['B'] - q['D']
        print(f"  {nm:12s} {AC:9.4f} {q['defsum']:9.4f} {q['B']:9.4f} {q['D']:9.4f} {q['gap']:9.4f} "
              f"{abs(recon-q['gap'])<1e-6}")

    print("\n" + "=" * 100)
    print("TASK 1/2 — ratios vs (A-B); which correction is dangerous: C (Ēbar/tbar) or D (S²/m)?")
    print("=" * 100)
    print(f"  {'graph':12s} {'A-B':>9} {'C/(A-B)':>9} {'D/(A-B)':>9} {'(C+D)/(A-B)':>12} {'D=0?(reg)':>9}")
    for nm, q in data:
        AB = q['A'] - q['B']
        if abs(AB) < 1e-9: continue
        print(f"  {nm:12s} {AB:9.4f} {q['C']/AB:9.4f} {q['D']/AB:9.4f} {(q['C']+q['D'])/AB:12.4f} "
              f"{'yes' if abs(q['D'])<1e-9 else 'no'}")

    print("\n" + "=" * 100)
    print("TASK 3 — sub-inequalities: Σdef·g² >= B ?  >= D ?  >= B+D (=gap>=0)?")
    print("=" * 100)
    bd_def = sum(1 for nm, q in data if q['defsum'] >= q['B'] - 1e-9)
    dd_def = sum(1 for nm, q in data if q['defsum'] >= q['D'] - 1e-9)
    bpd = sum(1 for nm, q in data if q['defsum'] >= q['B'] + q['D'] - 1e-9)
    print(f"  Σdef·g² >= B (=λΣ_ne h²): {bd_def}/{len(data)}")
    print(f"  Σdef·g² >= D (=λS²/m)   : {dd_def}/{len(data)}")
    print(f"  Σdef·g² >= B+D (=gap>=0): {bpd}/{len(data)}")
    # margin (B+D)/Σdef·g² = tightness
    print(f"  {'graph':12s} {'B/Σdef':>8} {'D/Σdef':>8} {'(B+D)/Σdef':>11} {'gap/Σdef':>9}")
    for nm, q in data:
        s = q['defsum']
        if s < 1e-9: continue
        print(f"  {nm:12s} {q['B']/s:8.4f} {q['D']/s:8.4f} {(q['B']+q['D'])/s:11.4f} {q['gap']/s:9.4f}")

    print("\n" + "=" * 100)
    print("TASK 2 detail — is D (S²/m) the dangerous/irregularity term? D=0 for regular; D large where?")
    print("=" * 100)
    for nm, q in sorted(data, key=lambda x: -x[1]['D'] / max(x[1]['defsum'], 1e-9)):
        s = q['defsum']
        print(f"  {nm:12s} D/Σdef={q['D']/max(s,1e-9):.4f}  S={q['S']:+.4f}  D={q['D']:.4f}")

    print("\n" + "=" * 100)
    print("SUMMARY")
    print("=" * 100)
    print("  Identify dangerous term; whether Σdef·g²>=B, >=D, >=B+D; tightness (B+D)/Σdef near 1 where.")


if __name__ == "__main__":
    main()
