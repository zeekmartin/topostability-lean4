"""
Exact decomposition of the slack  gap := lam2 G - B2'  for the triangle-free inequality

  B2' = Sum_e (min(d_a,d_b)-1) g_e^2   <=   lam2 G ,   g_e=f_a-f_b, h_e=f_a+f_b,
  G = Sum_e h_e^2 - S^2/m  = Sum_e (h_e - hbar)^2 ,  S = Sum_v d_v f_v = Sum_e h_e.

Using min(a,b) = (a+b)/2 - |a-b|/2:
  B2' = P - N - lam2,   P = 1/2 Sum(d_a+d_b)g^2 = <d,Gamma>,  N = 1/2 Sum|d_a-d_b|g^2,  Sum g^2 = lam2.
Hence (with <d,Gamma> = lam2 fDf - A/2, A = Cov_L(d,f^2)):

  gap = R'' + N + A/2,   R'' = lam2(fDf - lam2 + 1 - S^2/m).
And the per-edge collapse N + A/2 = C, where
  C = Sum_{edges, h=higher-deg endpoint, l=lower} (d_h - d_l) f_h (f_h - f_l).
So  gap = R'' + C   (an oriented lower->higher-degree edge sum + the spectral term).
Regular: degrees equal => C=N=A=0, gap = R'' = lam2(d+1-lam2) (the equality base case, =0 at K_n).

Run: python conjecture_B_B2prime_proof.py
"""
import numpy as np
import networkx as nx
from conjecture_B_nodal_decomposition import corpus
from conjecture_B_same_sign_reservoir import glue, chain_cliques
from conjecture_B_B2prime_scaling import deg2_dense


def quant(G):
    nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}; n = len(nodes)
    A = nx.to_numpy_array(G, nodelist=nodes); d = A.sum(1)
    L = np.diag(d) - A
    ev, U = np.linalg.eigh(L); lam = ev[1]; f = U[:, 1]; f = f / np.linalg.norm(f)
    m = G.number_of_edges(); S = float(d @ f); fDf = float(d @ (f * f))
    es = [(idx[a], idx[b]) for a, b in G.edges()]
    B2 = Gsum = N = Acal = C = 0.0
    for a, b in es:
        g = f[a] - f[b]; h = f[a] + f[b]; dd = d[a] - d[b]
        B2 += (min(d[a], d[b]) - 1) * g * g
        Gsum += h * h
        N += 0.5 * abs(dd) * g * g
        Acal += dd * (f[a] ** 2 - f[b] ** 2)
        # oriented higher-degree endpoint
        if d[a] > d[b]:
            C += (d[a] - d[b]) * f[a] * (f[a] - f[b])
        elif d[b] > d[a]:
            C += (d[b] - d[a]) * f[b] * (f[b] - f[a])
    G_ = Gsum - S ** 2 / m
    gap = lam * G_ - B2
    Rpp = lam * (fDf - lam + 1 - S ** 2 / m)
    return dict(n=n, m=m, lam=lam, fDf=fDf, S=S, B2=B2, G=G_, gap=gap, Rpp=Rpp,
                N=N, A=Acal, C=C, dmax=float(d.max()), dmin=float(d.min()),
                regular=bool(np.allclose(d, d[0])), d0=float(d[0]))


def corpus_graphs():
    out = []
    for fam, G in ([("corpus", g) for _, g in corpus()]
                   + [("glue", glue(a, b)) for a, b in ((5, 5), (20, 20), (3, 60))]
                   + [("chain", chain_cliques(mm, k)) for mm, k in ((10, 2), (20, 2), (15, 4))]):
        if G.number_of_nodes() < 4 or not nx.is_connected(G):
            continue
        ev = np.linalg.eigvalsh(nx.laplacian_matrix(G, nodelist=list(G.nodes()))
                                .toarray().astype(float))
        if ev[1] < 1e-9:
            continue
        out.append((fam, G))
    return out


def main():
    data = [quant(G) for _, G in corpus_graphs()]
    ng = len(data); tol = 1e-6

    print("=" * 76)
    print("EXACT decomposition  gap = lam2 G - B2'  (residuals over corpus)")
    print("=" * 76)
    r1 = max(abs(q['gap'] - (q['Rpp'] + q['N'] + q['A'] / 2)) for q in data)
    r2 = max(abs(q['gap'] - (q['Rpp'] + q['C'])) for q in data)
    r3 = max(abs(q['C'] - (q['N'] + q['A'] / 2)) for q in data)
    print(f"  gap == R'' + N + A/2            : max residual {r1:.2e}")
    print(f"  gap == R'' + C  (oriented edges): max residual {r2:.2e}")
    print(f"  C == N + A/2  (per-edge collapse): max residual {r3:.2e}")
    print("  R'' = lam2(fDf - lam2 + 1 - S^2/m); C = Sum_{h>l}(d_h-d_l) f_h (f_h - f_l).")

    print("\n" + "=" * 76)
    print("sign structure of the two terms")
    print("=" * 76)
    rpp_pos = sum(1 for q in data if q['Rpp'] >= -tol)
    c_neg = sum(1 for q in data if q['C'] < -tol)
    print(f"  R'' >= 0 : {rpp_pos}/{ng}   (R'' min={min(q['Rpp'] for q in data):.4f})")
    print(f"  C  < 0   : {c_neg}/{ng}     (C mostly negative -> R'' must dominate -C)")
    print(f"  gap = R''+C >= 0 : {sum(1 for q in data if q['gap']>=-tol)}/{ng} (the conjecture)")
    # ratio -C / R'' (how much of R'' the negative C eats)
    rr = [(-q['C']) / q['Rpp'] for q in data if q['Rpp'] > 1e-9]
    print(f"  -C / R'' (must be <=1): max={max(rr):.4f} median={np.median(rr):.4f}")

    print("\n" + "=" * 76)
    print("REGULAR graphs: C=N=A=0, gap = R'' = lam2(d+1-lam2)  (equality base case)")
    print("=" * 76)
    for name, Gr in [("C20", nx.cycle_graph(20)), ("Petersen", nx.petersen_graph()),
                     ("K8", nx.complete_graph(8)), ("Q4", nx.hypercube_graph(4))]:
        q = quant(Gr)
        print(f"  {name:9s} reg={q['regular']} d={q['d0']:.0f} lam2={q['lam']:.3f} "
              f"C={q['C']:.2e} N={q['N']:.2e} A={q['A']:.2e} gap={q['gap']:.4f} "
              f"R''={q['Rpp']:.4f} lam2(d+1-lam2)={q['lam']*(q['d0']+1-q['lam']):.4f}")

    print("\n" + "=" * 76)
    print("deg2+dense scaling: which term gives gap ~ c/n ?")
    print("=" * 76)
    ns = [50, 100, 200, 500, 1000, 2000]
    rows = [quant(deg2_dense(n)) for n in ns]
    print(f"  {'n':>5} {'gap':>10} {'Rpp':>10} {'C':>10} {'N':>10} {'A/2':>10}")
    for n, q in zip(ns, rows):
        print(f"  {n:5d} {q['gap']:10.5f} {q['Rpp']:10.5f} {q['C']:10.5f} {q['N']:10.5f} {q['A']/2:10.5f}")
    def fit(ys, lab):
        ys = np.array(ys); ms = ys != 0
        if ms.sum() >= 2 and np.all(np.abs(ys[ms]) > 0):
            a = np.polyfit(np.log(np.array(ns)[ms]), np.log(np.abs(ys[ms])), 1)
            print(f"    |{lab}| ~ n^{a[0]:.3f}")
    fit([q['gap'] for q in rows], "gap")
    fit([q['Rpp'] for q in rows], "R''")
    fit([q['C'] for q in rows], "C")
    fit([q['N'] for q in rows], "N")
    fit([q['A'] / 2 for q in rows], "A/2")

    print("\n" + "=" * 76)
    print("SUMMARY")
    print("=" * 76)
    print("  EXACT: gap = lam2 G - B2' = R'' + C, R''=lam2(fDf-lam2+1-S^2/m),")
    print("         C = Sum_{edges, h higher-deg}(d_h-d_l) f_h (f_h-f_l) = N + Cov_L(d,f^2)/2.")
    print("  Regular: C=N=A=0 => gap=R''=lam2(d+1-lam2) (=0 at K_n: equality base case).")
    print("  Open step: R'' + C >= 0 i.e. -C <= R''  (the only remaining inequality).")


if __name__ == "__main__":
    main()
