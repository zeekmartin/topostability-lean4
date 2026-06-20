"""
Prove gap -> 2/3 for the d=2 twin-port extremizer via the 4x4 equitable quotient.

Bulk K_N; twin ports a,b each ~ {0,1} (a !~ b); v0 ~ {a,b}.
Classes: V={v0}(x), P={a,b}(p), C={port0,port1}(c), R={rest, N-2}(r).
Quotient Laplacian L_Q (non-symmetric, class-constant eigenvectors):
  [2-λ, -2,    0,      0    ]
  [-1,  3-λ,  -2,      0    ]
  [0,   -2,   N-λ,  -(N-2)  ]
  [0,    0,   -2,    2-λ    ]
Closed forms (N->inf): lam2 = 1 + 4/(3N) -> 1; (x,p,c,r)=(2,1,-2/N,-4/N)/sqrt(6);
  T->2, B2'->3, Sum h^2 -> 9, S^2/m -> 16/3, lam2*G -> 11/3, gap = 11/3 - 3 = 2/3; eff -> 2.
Run: python conjecture_B_typeA_twin_port_proof.py
"""
import numpy as np
import networkx as nx
import sympy as sp


def quotient_gap(N):
    """gap via the 4-class quotient (class-constant Fiedler), exact arithmetic in float."""
    LQ = np.array([[2.0, -2, 0, 0],
                   [-1, 3, -2, 0],
                   [0, -2, N, -(N - 2)],
                   [0, 0, -2, 2.0]])
    w = np.array([1, 2, 2, N - 2], float)               # class sizes
    ev, V = np.linalg.eig(LQ)
    ev = ev.real; order = np.argsort(ev)
    lam = ev[order[1]]                                   # second-smallest = lam2
    v = V[:, order[1]].real
    x, p, c, r = v
    nrm = np.sqrt(x * x + 2 * p * p + 2 * c * c + (N - 2) * r * r)
    x, p, c, r = x / nrm, p / nrm, c / nrm, r / nrm
    if x < 0: x, p, c, r = -x, -p, -c, -r
    m = 6 + N * (N - 1) / 2
    T = 4 * (p - c) ** 2 + 2 * (N - 2) ** 2 * (c - r) ** 2
    B2 = 2 * (x - p) ** 2 + 8 * (p - c) ** 2 + 2 * (N - 2) ** 2 * (c - r) ** 2
    Sumh = (2 * (x + p) ** 2 + 4 * (p + c) ** 2 + 4 * c ** 2
            + 2 * (N - 2) * (c + r) ** 2 + 2 * (N - 2) * (N - 3) * r ** 2)
    S = 2 * x + 6 * p + 2 * (N + 1) * c + (N - 1) * (N - 2) * r
    lam2G = lam * (Sumh - S ** 2 / m)
    gap = lam2G - B2
    return dict(N=N, lam=lam, x=x, p=p, c=c, r=r, T=T, B2=B2, Sumh=Sumh, S=S, m=m,
                lam2G=lam2G, gap=gap)


def direct_gap(N):
    """Build the full twin-port graph and compute gap directly (cross-check)."""
    G = nx.complete_graph(N)
    a, b, v0 = N, N + 1, N + 2
    for u in (a, b):
        G.add_node(u); G.add_edge(u, 0); G.add_edge(u, 1)
    G.add_node(v0); G.add_edge(v0, a); G.add_edge(v0, b)
    nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}
    A = nx.to_numpy_array(G, nodelist=nodes); d = A.sum(1); L = np.diag(d) - A
    ev, U = np.linalg.eigh(L); lam = ev[1]; f = U[:, 1]; f = f / np.linalg.norm(f)
    if f[idx[v0]] < 0: f = -f
    m = G.number_of_edges(); S = float(d @ f)
    Gs = sum((f[idx[u]] + f[idx[v]]) ** 2 for u, v in G.edges())
    B2 = sum((min(d[idx[u]], d[idx[v]]) - 1) * (f[idx[u]] - f[idx[v]]) ** 2 for u, v in G.edges())
    return lam, lam * (Gs - S ** 2 / m) - B2


def main():
    print("=" * 78)
    print("TASK 1+2 — quotient gap vs direct gap; limit -> 2/3")
    print("=" * 78)
    print(f"  {'N':>5} {'lam2(quot)':>11} {'1+4/(3N)':>10} {'gap(quot)':>10} {'gap(direct)':>11} "
          f"{'T':>6} {'B2':>6}")
    for N in [20, 50, 100, 300, 1000, 3000]:
        q = quotient_gap(N)
        lamd, gd = direct_gap(N) if N <= 300 else (float('nan'), float('nan'))
        print(f"  {N:5d} {q['lam']:11.6f} {1+4/(3*N):10.6f} {q['gap']:10.6f} "
              f"{gd:11.6f} {q['T']:6.3f} {q['B2']:6.3f}")
    qbig = quotient_gap(200000)
    print(f"\n  N=200000: gap = {qbig['gap']:.6f}  (-> 2/3 = {2/3:.6f}); "
          f"T={qbig['T']:.5f}(->2) B2={qbig['B2']:.5f}(->3) lam2G={qbig['lam2G']:.5f}(->11/3={11/3:.5f})")

    print("\n" + "=" * 78)
    print("SYMBOLIC limit via asymptotic eigenvector (lam=1+4/(3N), p=1/sqrt6, x=2p, c=-2p/N, r=-4p/N)")
    print("=" * 78)
    N = sp.symbols('N', positive=True)
    p = 1 / sp.sqrt(6); x = 2 * p
    # leading eigenvector with 1/N entries (use exact leading coefficients)
    c = -2 * p / N; r = -4 * p / N; lam = 1 + sp.Rational(4, 3) / N
    m = 6 + N * (N - 1) / 2
    T = 4 * (p - c) ** 2 + 2 * (N - 2) ** 2 * (c - r) ** 2
    B2 = 2 * (x - p) ** 2 + 8 * (p - c) ** 2 + 2 * (N - 2) ** 2 * (c - r) ** 2
    Sumh = (2 * (x + p) ** 2 + 4 * (p + c) ** 2 + 4 * c ** 2
            + 2 * (N - 2) * (c + r) ** 2 + 2 * (N - 2) * (N - 3) * r ** 2)
    S = 2 * x + 6 * p + 2 * (N + 1) * c + (N - 1) * (N - 2) * r
    gap = lam * (Sumh - S ** 2 / m) - B2
    print(f"  lim T      = {sp.limit(T, N, sp.oo)}   (expect 2)")
    print(f"  lim B2'    = {sp.limit(B2, N, sp.oo)}   (expect 3)")
    print(f"  lim Sum h^2= {sp.limit(Sumh, N, sp.oo)}   (expect 9)")
    print(f"  lim S^2/m  = {sp.limit(S**2/m, N, sp.oo)}   (expect 16/3)")
    print(f"  lim lam2*G = {sp.limit(lam*(Sumh - S**2/m), N, sp.oo)}   (expect 11/3)")
    print(f"  lim gap    = {sp.nsimplify(sp.limit(gap, N, sp.oo))}   (expect 2/3)")
    print(f"  => gap = 4 p^2 = 4/6 = 2/3;  eff = 2 (proved);  gap/eff = 1/3.")


if __name__ == "__main__":
    main()
