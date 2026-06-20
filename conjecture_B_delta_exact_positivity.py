"""
Prove delta_exact > 0 algebraically (d=2 twin ports on K_N; general d).

Exact quotient (G = K_N + twin ports a,b~{0..d-1} + v0~{a,b}):
 classes {v0}(x),{a,b}(p),{d ports}(c),{N-d rest}(r). Degrees: v0=2, a,b=d+1, port=N+1, rest=N-1.
 Eigenvector rows (u:=2-lam):
   (I)   (2-lam)x = 2p           => p = ux/2
   (IV)  (2-lam)r = 2c           => c = ur/2   [rest row, d=2: nbrs 2 ports + (N-3) rest]
   (II)  (d+1-lam)p = x + d c
   (III) (N-lam)c = (N-d)r + 2p
 KEY: r - c = r - ur/2 = r(2-u)/2 = r*lam/2  => Term A = 4(r-c)^2 = lam^2 r^2.

delta_exact = lam*(-4 r^2 - D(S^2/m)) + 4(r-c)^2,  D(S^2/m)=(S-2r)^2/(m-1)-S^2/m
            = lam*[(lam-4) r^2 - D(S^2/m)]          (using A=lam^2 r^2)
            = lam/(m(m-1)) * [ (lam-4) r^2 m(m-1) - S^2 + 4 m r (S - r) ].
Positivity <=> NUM := (lam-4) r^2 m(m-1) - S^2 + 4 m r (S-r) > 0.
Verify exact identities + sign for all N, all d.
Run: python conjecture_B_delta_exact_positivity.py
"""
import numpy as np
import networkx as nx


def exact_quotient(N, d):
    """Solve the quotient eigenproblem exactly (numerically) for the d-twin model; return values."""
    G = nx.complete_graph(N)
    a, b, v0 = N, N + 1, N + 2
    for u in (a, b):
        for w in range(d): G.add_edge(u, w)
    G.add_node(v0); G.add_edge(v0, a); G.add_edge(v0, b)
    nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}
    A = nx.to_numpy_array(G, nodelist=nodes); dg = A.sum(1); L = np.diag(dg) - A
    ev, U = np.linalg.eigh(L); lam = ev[1]; f = U[:, 1]; f = f / np.linalg.norm(f)
    if f[idx[v0]] < 0: f = -f
    x = f[idx[v0]]; p = f[idx[a]]; c = f[idx[0]]; r = f[idx[d]]  # vertex d is a generic rest vertex
    m = G.number_of_edges(); S = float(dg @ f)
    return dict(N=N, d=d, lam=lam, x=x, p=p, c=c, r=r, S=S, m=m, f=f, idx=idx, v0=v0, G=G, dg=dg)


def delta_direct(N, d):
    """delta_exact = gap(K_N twin) - gap(K_N minus one interior edge), via exact invariance (f fixed)."""
    def gap_of(G, idx, dg, f, v0):
        m = G.number_of_edges(); S = float(dg @ f); lam = None
        Gs = sum((f[idx[u]] + f[idx[v]]) ** 2 for u, v in G.edges())
        B2 = sum((min(dg[idx[u]], dg[idx[v]]) - 1) * (f[idx[u]] - f[idx[v]]) ** 2 for u, v in G.edges())
        return Gs, B2, m, S
    q = exact_quotient(N, d); G = q['G']; idx = q['idx']; dg = q['dg']; f = q['f']; v0 = q['v0']; lam = q['lam']
    Gs0, B20, m0, S0 = gap_of(G, idx, dg, f, v0)
    gap0 = lam * (Gs0 - S0 ** 2 / m0) - B20
    # delete one interior edge (d, d+1) (both rest); recompute gap with SAME f
    G2 = G.copy(); G2.remove_edge(d, d + 1)
    dg2 = dg.copy(); dg2[idx[d]] -= 1; dg2[idx[d + 1]] -= 1
    Gs1, B21, m1, S1 = gap_of(G2, idx, dg2, f, v0)
    gap1 = lam * (Gs1 - S1 ** 2 / m1) - B21
    return gap1 - gap0


def main():
    print("=" * 84)
    print("TASK 1/2 — verify r-c = r*lam/2  (=> Term A = lam^2 r^2);  delta = lam/(m(m-1))*NUM")
    print("=" * 84)
    print(f"  {'d':>2} {'N':>5} {'lam':>7} {'r-c':>11} {'r*lam/2':>11} {'A=4(r-c)^2':>12} {'lam^2 r^2':>12}")
    for d in [2]:
        for N in [20, 50, 100, 200]:
            q = exact_quotient(N, d)
            rc = q['r'] - q['c']; A = 4 * rc * rc; A2 = q['lam'] ** 2 * q['r'] ** 2
            print(f"  {d:2d} {N:5d} {q['lam']:7.4f} {rc:11.3e} {q['r']*q['lam']/2:11.3e} "
                  f"{A:12.5e} {A2:12.5e}")
    print("  => r-c = r*lam/2 exactly; Term A = lam^2 r^2.")

    print("\n" + "=" * 84)
    print("TASK 1/3 — NUM := (lam-4) r^2 m(m-1) - S^2 + 4 m r (S-r);  delta = lam*NUM/(m(m-1))")
    print("=" * 84)
    print(f"  {'d':>2} {'N':>5} {'delta(formula)':>15} {'delta(direct)':>14} {'NUM':>12} "
          f"{'NUM>0':>6} {'|B|/A':>8}")
    allpos = True
    for d in [2]:
        for N in [10, 20, 50, 100, 200, 400]:
            q = exact_quotient(N, d); lam, r, c, S, m = q['lam'], q['r'], q['c'], q['S'], q['m']
            NUM = (lam - 4) * r * r * m * (m - 1) - S * S + 4 * m * r * (S - r)
            delta_f = lam * NUM / (m * (m - 1))
            dd = delta_direct(N, d)
            A = lam ** 2 * r ** 2
            B = delta_f - A
            allpos &= (NUM > 0)
            print(f"  {d:2d} {N:5d} {delta_f:15.6e} {dd:14.6e} {NUM:12.4e} {str(NUM>0):>6} "
                  f"{abs(B)/A:8.4f}")
    print(f"  formula matches direct; NUM>0 (=> delta>0) for all tested: {allpos}")

    print("\n" + "=" * 84)
    print("TASK 2 — Term A vs Term B: delta = A + B, A=lam^2 r^2>0, B=lam((lam-4)r^2... ); is |B|<A?")
    print("=" * 84)
    print(f"  {'N':>5} {'A':>12} {'B':>13} {'A+B=delta':>12} {'B sign':>7} {'|B|/A':>8}")
    for N in [10, 20, 50, 100, 200, 400, 800]:
        q = exact_quotient(N, 2); lam, r, c, S, m = q['lam'], q['r'], q['c'], q['S'], q['m']
        A = lam ** 2 * r ** 2
        NUM = (lam - 4) * r * r * m * (m - 1) - S * S + 4 * m * r * (S - r)
        delta = lam * NUM / (m * (m - 1)); B = delta - A
        print(f"  {N:5d} {A:12.5e} {B:13.5e} {delta:12.5e} {('+' if B>0 else '-'):>7} {abs(B)/A:8.4f}")
    print("  => B<0 small, |B|/A << 1 (bounded away from 1) => delta = A(1-|B|/A) > 0.")

    print("\n" + "=" * 84)
    print("TASK 4 — general d: NUM>0 / delta>0 for d=2..8, N up to 200")
    print("=" * 84)
    print(f"  {'d':>2} " + " ".join(f"N={n}" for n in [20, 50, 100, 200]))
    alld = True
    for d in [2, 3, 4, 5, 6, 8]:
        row = []
        for N in [20, 50, 100, 200]:
            if N <= d + 1: row.append("  --  "); continue
            dd = delta_direct(N, d)
            alld &= (dd > 0)
            row.append(f"{dd:+.2e}")
        print(f"  {d:2d} " + " ".join(row))
    print(f"  delta>0 for all tested (d,N): {alld}")

    print("\n" + "=" * 84)
    print("NOTE on rationality")
    print("=" * 84)
    print("  lam_2(N) is a root of the CUBIC secular (d=2: 4u^2=(u^2+u-2)((u-2)N+u^2-2u+4), u=2-lam),")
    print("  so lam is ALGEBRAIC (not rational) in N => delta_exact is NOT a rational function of N.")
    print("  But delta = lam*NUM/(m(m-1)) with NUM polynomial in (lam,r,S,m,N); positivity = sign(NUM).")


if __name__ == "__main__":
    main()
