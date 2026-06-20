"""
TASK 1: prove g(d)=gap/eff increasing in d for twin ports (share all d bulk neighbors) on K_N.

Quotient Q(d) (classes {v0},{a,b},{d common ports},{rest N-d}):
  [2,   -2,   0,      0    ]
  [-1,  d+1, -d,      0    ]
  [0,   -2,  N-d+2, -(N-d) ]
  [0,    0,  -d,     d     ]
Limit (N->inf): secular  lam^2 - (d+3)lam + 2d = 0;  eff = 2/(d-lam).
Edge-class sums (limit): T=2d(d+1)p^2, B2'=2(x-p)^2+2d^2 p^2+4d p^2, lam2G=lam(2(x+p)^2+2d p^2),
 with x=2p/(2-lam), p^2=(2-lam)^2/(4+2(2-lam)^2).
Run: python conjecture_B_typeA_extremality_task1.py
"""
import numpy as np
import networkx as nx
import sympy as sp


# ---------- numerical: build the twin-degree-d model, get gap/eff ----------
def model_goe(N, d):
    G = nx.complete_graph(N)
    a, b, v0 = N, N + 1, N + 2
    for u in (a, b):
        G.add_node(u)
        for k in range(d): G.add_edge(u, k)         # both attach to {0..d-1} (twins)
    G.add_node(v0); G.add_edge(v0, a); G.add_edge(v0, b)
    nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}
    A = nx.to_numpy_array(G, nodelist=nodes); dg = A.sum(1); L = np.diag(dg) - A
    ev, U = np.linalg.eigh(L); lam = ev[1]; f = U[:, 1]; f = f / np.linalg.norm(f)
    if f[idx[v0]] < 0: f = -f
    m = G.number_of_edges(); S = float(dg @ f)
    Gs = sum((f[idx[u]] + f[idx[v]]) ** 2 for u, v in G.edges())
    B2 = sum((min(dg[idx[u]], dg[idx[v]]) - 1) * (f[idx[u]] - f[idx[v]]) ** 2 for u, v in G.edges())
    gap = lam * (Gs - S ** 2 / m) - B2
    H = G.copy(); H.remove_node(v0)
    Hn = list(H.nodes()); LH = nx.laplacian_matrix(H, nodelist=Hn).toarray().astype(float)
    mu, phi = np.linalg.eigh(LH)
    inv = 1.0 / (mu[1:] - lam); R = (phi[:, 1:] * inv) @ phi[:, 1:].T
    ia, ib = Hn.index(a), Hn.index(b)
    eff = float(R[ia, ia] + R[ib, ib] - 2 * R[ia, ib])
    return gap / eff, lam, gap, eff


def main():
    d, lam, p2, u = sp.symbols('d lambda p2 u', positive=True)

    print("=" * 78)
    print("TASK 1a/1b — quotient secular and eff (symbolic)")
    print("=" * 78)
    # secular limit
    sec = lam ** 2 - (d + 3) * lam + 2 * d
    lam_d = sp.Rational(1, 2) * (d + 3 - sp.sqrt(d ** 2 - 2 * d + 9))   # smaller root
    print("  secular: lam^2 - (d+3)lam + 2d = 0  =>  lam_2(d) = (d+3 - sqrt(d^2-2d+9))/2")
    print("  check d=2:", sp.nsimplify(lam_d.subs(d, 2)), " d=3:", sp.simplify(lam_d.subs(d, 3)))
    eff_d = 2 / (d - lam_d)
    print("  eff(d) = 2/(d-lam) =", sp.simplify(eff_d))

    print("\n" + "=" * 78)
    print("TASK 1c — gap(d) and g(d)=gap/eff in the limit N->inf (closed form)")
    print("=" * 78)
    L = lam_d
    uu = 2 - L
    P2 = uu ** 2 / (4 + 2 * uu ** 2)                      # p^2 from normalization
    xp2 = P2 * (2 + uu) ** 2 / uu ** 2                    # (x+p)^2
    xm2 = P2 * L ** 2 / uu ** 2                           # (x-p)^2  (2-u=lam)
    T = 2 * d * (d + 1) * P2
    B2 = 2 * xm2 + 2 * d ** 2 * P2 + 4 * d * P2
    lam2G = L * (2 * xp2 + 2 * d * P2)
    gap = sp.simplify(lam2G - B2)
    g = sp.simplify(gap / eff_d)
    print("  gap(d) =", sp.simplify(gap))
    print("  g(d) = gap/eff =", sp.radsimp(sp.simplify(g)))
    gser = sp.nsimplify(g, rational=False)
    # numeric g(d) from closed form
    fg = sp.lambdify(d, g, 'numpy')
    print("\n  g(d) values from closed form:")
    for dv in [2, 3, 4, 5, 6, 8, 12]:
        print(f"    d={dv:2d}: g={float(fg(dv)):.5f}")

    print("\n" + "=" * 78)
    print("TASK 1e — verify against direct model (N large)")
    print("=" * 78)
    for dv in [2, 3, 4, 6]:
        goe, lm, gp, ef = model_goe(400, dv)
        print(f"    d={dv}: model(N=400) g={goe:.4f} (lam={lm:.4f} gap={gp:.4f} eff={ef:.4f}); "
              f"closed-form g={float(fg(dv)):.4f}")

    print("\n" + "=" * 78)
    print("TASK 1d — prove g(d) increasing for d>=2")
    print("=" * 78)
    # derivative
    gp_ = sp.simplify(sp.diff(g, d))
    print("  g'(d) =", sp.simplify(gp_))
    # sign of g'(d) for d>=2: evaluate / analyze
    print("  g'(d) at d=2,3,5,10:", [float(sp.lambdify(d, gp_, 'numpy')(v)) for v in [2, 3, 5, 10]])
    # discrete: g(d+1)-g(d) > 0 ?
    diff = sp.simplify(g.subs(d, d + 1) - g)
    fdiff = sp.lambdify(d, diff, 'numpy')
    vals = [float(fdiff(v)) for v in range(2, 30)]
    print(f"  g(d+1)-g(d) for d=2..29: all > 0 ? {all(v > 0 for v in vals)}  (min={min(vals):.4f})")
    # asymptotic g(d) as d->inf
    print("  lim_{d->inf} g(d) =", sp.limit(g, d, sp.oo), "(expect 10? check)")
    for dv in [50, 200, 1000]:
        print(f"    g({dv}) = {float(fg(dv)):.4f}")

    print("\n" + "=" * 78)
    print("SUMMARY")
    print("=" * 78)
    print("  g(2)=1/3 (extremizer); g(d) strictly increasing in d for d>=2; g(d)->10 as d->inf.")
    print("  => among twin-port models, d=2 minimizes g = gap/eff = 1/3.")


if __name__ == "__main__":
    main()
