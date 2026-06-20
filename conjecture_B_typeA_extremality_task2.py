"""
TASK 2: g(d,s)=gap/eff decreasing in overlap s, minimum at s=d (twins).

Ports a,b in K_N: a~{common s}+{a-only d-s}, b~{common s}+{b-only d-s}, a!~b, v0~{a,b}.
Claim (derived): in the limit N->inf,
  eff(d,s) -> 2/(d-lam)  (s-INDEPENDENT; antisymmetric exclusive response -> 0)
  gap(d,s) = C(d) - 2 p^2 s    (LINEAR decreasing in s),  p^2 = (2-lam)^2/(4+2(2-lam)^2)
  => g(d,s) linear in s, slope -2p^2/eff < 0, minimum at s=d.
Verify numerically (large N) and check g(2,s) = 2/3 - s/6.
Run: python conjecture_B_typeA_extremality_task2.py
"""
import numpy as np
import networkx as nx


def model(N, d, s):
    if 2 * d - s > N: return None
    G = nx.complete_graph(N)
    a, b, v0 = N, N + 1, N + 2
    common = list(range(s)); aonly = list(range(s, d)); bonly = list(range(d, 2 * d - s))
    for u in (a, b): G.add_node(u)
    for u in common + aonly: G.add_edge(a, u)
    for u in common + bonly: G.add_edge(b, u)
    G.add_node(v0); G.add_edge(v0, a); G.add_edge(v0, b)
    nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}
    A = nx.to_numpy_array(G, nodelist=nodes); dg = A.sum(1); L = np.diag(dg) - A
    ev, U = np.linalg.eigh(L); lam = ev[1]; f = U[:, 1]; f = f / np.linalg.norm(f)
    if f[idx[v0]] < 0: f = -f
    m = G.number_of_edges(); S = float(dg @ f)
    Gs = sum((f[idx[u]] + f[idx[v]]) ** 2 for u, v in G.edges())
    B2 = sum((min(dg[idx[u]], dg[idx[v]]) - 1) * (f[idx[u]] - f[idx[v]]) ** 2 for u, v in G.edges())
    gap = lam * (Gs - S ** 2 / m) - B2
    H = G.copy(); H.remove_node(v0); Hn = list(H.nodes())
    LH = nx.laplacian_matrix(H, nodelist=Hn).toarray().astype(float)
    mu, phi = np.linalg.eigh(LH)
    inv = 1.0 / (mu[1:] - lam); R = (phi[:, 1:] * inv) @ phi[:, 1:].T
    ia, ib = Hn.index(a), Hn.index(b)
    eff = float(R[ia, ia] + R[ib, ib] - 2 * R[ia, ib])
    return dict(lam=lam, gap=gap, eff=eff, goe=gap / eff)


def main():
    print("=" * 84)
    print("TASK 2b/2c/2e — g(d,s), eff(d,s), gap(d,s) at large N; is gap linear in s?")
    print("=" * 84)
    N = 600
    for d in [2, 3, 4, 5]:
        print(f"  d={d} (N={N}):")
        gaps, effs, goes = [], [], []
        for s in range(0, d + 1):
            r = model(N, d, s)
            if r is None: continue
            gaps.append(r['gap']); effs.append(r['eff']); goes.append(r['goe'])
            print(f"    s={s}: lam={r['lam']:.4f} gap={r['gap']:.5f} eff={r['eff']:.5f} g={r['goe']:.5f}")
        # linear fit of gap vs s
        if len(gaps) >= 2:
            sv = np.arange(len(gaps))
            slope, intercept = np.polyfit(sv, gaps, 1)
            resid = max(abs(np.array(gaps) - (slope * sv + intercept)))
            print(f"    gap vs s: slope={slope:.5f}  intercept(C)={intercept:.5f}  "
                  f"max nonlinearity={resid:.2e}")
            print(f"    eff range: [{min(effs):.4f},{max(effs):.4f}] (s-independent?); "
                  f"g decreasing: {all(goes[i] > goes[i+1] for i in range(len(goes)-1))}")

    print("\n" + "=" * 84)
    print("TASK 2e — exact d=2: predict g(2,s) = 2/3 - s/6, gap(2,s)=4/3 - s/3, eff=2")
    print("=" * 84)
    for s in [0, 1, 2]:
        r = model(800, 2, s)
        print(f"  s={s}: gap={r['gap']:.5f} (pred {4/3 - s/3:.5f})  eff={r['eff']:.5f} (pred 2)  "
              f"g={r['goe']:.5f} (pred {2/3 - s/6:.5f})")

    print("\n" + "=" * 84)
    print("TASK 2d — slope = -2 p^2 / eff ? check the linear-decrease coefficient")
    print("=" * 84)
    for d in [2, 3, 4]:
        # lam from secular lam^2-(d+3)lam+2d=0 (TASK1)
        lam = 0.5 * (d + 3 - np.sqrt(d * d - 2 * d + 9))
        p2 = (2 - lam) ** 2 / (4 + 2 * (2 - lam) ** 2)
        eff = 2 / (d - lam)
        slope_pred = -2 * p2 / eff          # d g(d,s)/d s
        # numeric slope of g
        gv = [model(600, d, s)['goe'] for s in range(0, d + 1)]
        slope_num = np.polyfit(range(d + 1), gv, 1)[0]
        print(f"  d={d}: lam={lam:.4f} p^2={p2:.5f} eff={eff:.4f}  "
              f"slope(g) pred=-2p^2/eff={slope_pred:.5f}  numeric={slope_num:.5f}")

    print("\n" + "=" * 84)
    print("SUMMARY")
    print("=" * 84)
    print("  gap(d,s) LINEAR decreasing in s (slope -2p^2); eff s-independent => g(d,s) linear")
    print("  decreasing, slope -2p^2/eff < 0 => minimum at s=d (twins). g(2,s)=2/3-s/6: 2/3,1/2,1/3.")


if __name__ == "__main__":
    main()
