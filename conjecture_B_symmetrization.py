"""
Global symmetrization route for R = T/(lam2 G) <= 1, equality iff K_n.

Test operations moving G toward K_n and whether they do NOT decrease R:
  (a) edge addition G+e
  (b) Zykov symmetrization: non-adjacent u,v with d(u)>=d(v) -> N(v):=N(u) (v becomes a twin of u)
  (c) batched completion toward K_n (add all missing edges)
Track T, lam2G, R, Fiedler localization. TASK5: does R=1 force every t_e=n-2 (=> K_n)?
Run: python conjecture_B_symmetrization.py
"""
import numpy as np
import networkx as nx


def R_of(G):
    nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}; n = len(nodes)
    if n < 2 or not nx.is_connected(G): return None
    A = nx.to_numpy_array(G, nodelist=nodes); d = A.sum(1); L = np.diag(d) - A
    ev, U = np.linalg.eigh(L); lam = ev[1]; f = U[:, 1]; f = f / np.linalg.norm(f)
    m = G.number_of_edges(); S = float(d @ f); A2 = A @ A
    T = sum(A2[idx[u], idx[v]] * (f[idx[u]] - f[idx[v]]) ** 2 for u, v in G.edges())
    Gsum = sum((f[idx[u]] + f[idx[v]]) ** 2 for u, v in G.edges())
    Gvar = Gsum - S ** 2 / m; lam2G = lam * Gvar
    floc = float(np.max(np.abs(f)))      # Fiedler localization (max |f_v|)
    return dict(n=n, lam=lam, T=T, Gvar=Gvar, lam2G=lam2G, R=T / lam2G if lam2G > 1e-12 else float('nan'),
                floc=floc)


def zykov(G, u, v):
    """Make v a twin of u: N(v) := N(u)\{v}, keep u,v non-adjacent."""
    H = G.copy()
    for w in list(H.neighbors(v)):
        if w != u: H.remove_edge(v, w)
    for w in list(H.neighbors(u)):
        if w != v: H.add_edge(v, w)
    if H.has_edge(u, v): H.remove_edge(u, v)
    return H


def main():
    rng = np.random.default_rng(0)

    print("=" * 84)
    print("(a) EDGE ADDITION toward K_n: R(G+e) >= R(G)? (expect non-monotone, reverse of deletion)")
    print("=" * 84)
    inc = tot = 0
    for trial in range(20):
        n = int(rng.integers(12, 26)); q = float(rng.uniform(0.5, 0.9))
        H = nx.gnp_random_graph(n, q, seed=int(rng.integers(1e9)))
        if not nx.is_connected(H): continue
        ne = [(u, v) for u in range(n) for v in range(u + 1, n) if not H.has_edge(u, v)]
        if not ne: continue
        r0 = R_of(H)
        for e in ne[:5]:
            H2 = H.copy(); H2.add_edge(*e); r1 = R_of(H2)
            if r1 is None: continue
            tot += 1; inc += (r1['R'] >= r0['R'] - 1e-9)
    print(f"  R(G+e) >= R(G): {inc}/{tot}  ({'monotone' if inc==tot else 'NON-monotone (some additions LOWER R)'})")

    print("\n" + "=" * 84)
    print("(b) ZYKOV symmetrization (v := twin of u): R non-decreasing?")
    print("=" * 84)
    zinc = ztot = 0; zex = []
    for trial in range(40):
        n = int(rng.integers(10, 24)); q = float(rng.uniform(0.4, 0.85))
        H = nx.gnp_random_graph(n, q, seed=int(rng.integers(1e9)))
        if not nx.is_connected(H): continue
        deg = dict(H.degree())
        nonadj = [(u, v) for u in range(n) for v in range(n)
                  if u != v and not H.has_edge(u, v) and deg[u] >= deg[v]]
        if not nonadj: continue
        r0 = R_of(H)
        for (u, v) in nonadj[:4]:
            H2 = zykov(H, u, v); r1 = R_of(H2)
            if r1 is None: continue
            ztot += 1; ok = r1['R'] >= r0['R'] - 1e-9; zinc += ok
            if not ok and len(zex) < 4: zex.append((n, round(r0['R'], 4), round(r1['R'], 4)))
    print(f"  R(zykov) >= R(G): {zinc}/{ztot}  "
          f"({'monotone' if zinc==ztot else 'NON-monotone'})")
    for e in zex: print(f"    counterexample: n={e[0]} R={e[1]} -> R(zykov)={e[2]}")

    print("\n" + "=" * 84)
    print("(c) BATCHED completion: add ALL missing edges at once (G -> K_n). R monotone along path?")
    print("=" * 84)
    for n in [16, 24]:
        H = nx.gnp_random_graph(n, 0.5, seed=1)
        if not nx.is_connected(H): H = nx.gnp_random_graph(n, 0.6, seed=2)
        ne = [(u, v) for u in range(n) for v in range(u + 1, n) if not H.has_edge(u, v)]
        rng.shuffle(ne)
        Rs = [R_of(H)['R']]; cur = H.copy()
        for e in ne:
            cur.add_edge(*e); Rs.append(R_of(cur)['R'])
        Rs = np.array(Rs)
        dec = int((np.diff(Rs) < -1e-9).sum())
        print(f"  n={n}: G->K_n in {len(Rs)} steps; R {Rs[0]:.4f}->{Rs[-1]:.4f}(=1); "
              f"steps R DECREASES: {dec}/{len(Rs)-1}; final R={Rs[-1]:.5f}")
    print("  (even completing toward K_n, R is non-monotone; but endpoint K_n has R=1, the max)")

    print("\n" + "=" * 84)
    print("TASK 5 — does R=1 force every edge t_e = n-2 (=> G=K_n)? near-complete approach")
    print("=" * 84)
    print(f"  {'graph':14s} {'R':>9} {'min t_e':>8} {'n-2':>5} {'all t=n-2?':>11}")
    for n in [12, 20, 30]:
        for k in [0, 1, 2, 5]:
            G = nx.complete_graph(n); ed = list(G.edges()); rng.shuffle(ed)
            rem = 0
            for e in ed:
                if rem >= k: break
                if G.degree(e[0]) > 2 and G.degree(e[1]) > 2: G.remove_edge(*e); rem += 1
            r = R_of(G); nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}
            A = nx.to_numpy_array(G, nodelist=nodes); A2 = A @ A
            mint = min(int(A2[idx[u], idx[v]]) for u, v in G.edges())
            allc = all(int(A2[idx[u], idx[v]]) == n - 2 for u, v in G.edges())
            print(f"  K{n}-{rem:<11d} {r['R']:9.5f} {mint:8d} {n-2:5d} {str(allc):>11}")
    print("  => R=1 only when all t_e=n-2 (=K_n); any deleted edge drops some t_e below n-2 and R<1.")

    print("\n" + "=" * 84)
    print("SUMMARY")
    print("=" * 84)
    print("  Classify: edge-add / Zykov / batched completion monotone? equality forces K_n?")


if __name__ == "__main__":
    main()
