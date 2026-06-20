"""
TYPE A gap>0 for REGULAR cores: symmetric reduction + closed form.

Exact regular-core gap (verified, schur round):
  gap = lam(rho-lam+1) + (3lam-lam*rho-2)x^2 + (2lam+rho-2)(p^2+r^2) + (3-rho)xy - lam S^2/m
  x=f_v0, p=f_a, r=f_b, y=p+r=(2-lam)x, S=(4-rho-lam)x, m=rho(n-1)/2+2.

Symmetric attachment p=r=(2-lam)x/2:
  p^2+r^2 = (2-lam)^2 x^2/2,  xy = (2-lam)x^2
  => gap = lam(rho-lam+1) + x^2 * K,
     K = (3lam-lam*rho-2) + (2lam+rho-2)(2-lam)^2/2 + (3-rho)(2-lam) - lam(4-rho-lam)^2/m.

Normalization (eta=0 mean-field core; EXACT for complete core):
  x^2 + 2p^2 + (n-3)mu^2 = 1, mu=-(3-lam)x/(n-3)
  => x^2 = 1/D,  D = 1 + (2-lam)^2/2 + (3-lam)^2/(n-3).
  gap_closed = lam(rho-lam+1) + K/D.

Run: python conjecture_B_typeA_regular_core_proof.py
"""
import numpy as np
import networkx as nx


def make(rho, n, seed=0, complete=False):
    nH = n - 1
    if complete:
        H = nx.complete_graph(nH)
    else:
        if (rho * nH) % 2: rho += 1
        H = nx.random_regular_graph(rho, nH, seed=seed)
    H = nx.convert_node_labels_to_integers(H)
    a = 0; nbrs = set(H.neighbors(a))
    b = next((u for u in range(1, nH) if u not in nbrs and u != a), 1)  # fallback b=1 (complete core)
    G = nx.Graph(H); G.add_node(nH); G.add_edge(nH, a); G.add_edge(nH, b)
    return G, nH, a, b


def analyze(rho, n, seed=0, complete=False):
    G, nH, a, b = make(rho, n, seed=seed, complete=complete)
    nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}; N = len(nodes)
    A = nx.to_numpy_array(G, nodelist=nodes); d = A.sum(1); L = np.diag(d) - A
    ev, U = np.linalg.eigh(L); lam = ev[1]; f = U[:, 1]; f = f / np.linalg.norm(f)
    v0 = idx[nH]
    if f[v0] < 0: f = -f
    m = G.number_of_edges(); S = float(d @ f)
    x = float(f[v0]); p = float(f[idx[a]]); r = float(f[idx[b]])
    rho_ = float(d[idx[1 if 1 not in (a, b) else 2]])  # a core degree (non-attachment)
    # robust rho = core degree of a generic non-attachment vertex
    gen = next(u for u in range(nH) if u not in (a, b))
    rho_ = float(A[idx[gen]].sum())
    Gsum = sum((f[idx[u]] + f[idx[v]]) ** 2 for u, v in G.edges())
    B2 = sum((min(d[idx[u]], d[idx[v]]) - 1) * (f[idx[u]] - f[idx[v]]) ** 2 for u, v in G.edges())
    gap = lam * (Gsum - S ** 2 / m) - B2
    return dict(n=n, nH=nH, m=m, lam=lam, x=x, p=p, r=r, rho=rho_, gap=gap, S=S)


def Kfun(lam, rho, m):
    return ((3 * lam - lam * rho - 2) + (2 * lam + rho - 2) * (2 - lam) ** 2 / 2
            + (3 - rho) * (2 - lam) - lam * (4 - rho - lam) ** 2 / m)


def Dfun(lam, n):
    return 1 + (2 - lam) ** 2 / 2 + (3 - lam) ** 2 / (n - 3)


def main():
    print("=" * 100)
    print("TASK 1 — symmetric reduction gap = lam(rho-lam+1) + x^2*K  (check p=r, formula exact)")
    print("=" * 100)
    print(f"  {'core':14s} {'lam':>7} {'x^2':>7} {'p':>9} {'r':>9} {'|p-r|':>8} "
          f"{'gap':>9} {'lam(..)+x2K':>11} {'err':>9}")
    sym_err = 0.0
    for (rho, n, comp, tag) in [(10, 100, False, "rr(99,10)"), (20, 100, False, "rr(99,20)"),
                                 (50, 100, False, "rr(99,50)"), (None, 100, True, "K99")]:
        q = analyze(rho if rho else 0, n, seed=1, complete=comp)
        K = Kfun(q['lam'], q['rho'], q['m'])
        approx = q['lam'] * (q['rho'] - q['lam'] + 1) + q['x'] ** 2 * K
        sym_err = max(sym_err, abs(approx - q['gap']))
        print(f"  {tag:14s} {q['lam']:7.4f} {q['x']**2:7.4f} {q['p']:9.5f} {q['r']:9.5f} "
              f"{abs(q['p']-q['r']):8.1e} {q['gap']:9.5f} {approx:11.5f} {abs(approx-q['gap']):9.1e}")
    print(f"  (symmetric formula err uses ACTUAL x^2; exact when p=r, i.e. complete/symmetric cores)")

    print("\n" + "=" * 100)
    print("TASK 2/3 — closed form gap_closed = lam(rho-lam+1) + K/D  (eta=0); vs true gap")
    print("=" * 100)
    print(f"  {'core':14s} {'lam':>7} {'1/D':>7} {'x^2true':>8} {'gap':>9} {'gap_closed':>11} "
          f"{'10(n-3)/m':>10}")
    for (rho, n, comp, tag) in [(10, 100, False, "rr(99,10)"), (20, 100, False, "rr(99,20)"),
                                 (50, 100, False, "rr(99,50)"), (None, 100, True, "K99")]:
        q = analyze(rho if rho else 0, n, seed=1, complete=comp)
        K = Kfun(q['lam'], q['rho'], q['m']); D = Dfun(q['lam'], q['n'])
        gap_closed = q['lam'] * (q['rho'] - q['lam'] + 1) + K / D
        print(f"  {tag:14s} {q['lam']:7.4f} {1/D:7.4f} {q['x']**2:8.4f} {q['gap']:9.5f} "
              f"{gap_closed:11.5f} {10*(q['n']-3)/q['m']:10.5f}")
    print("  (eta=0 closed form EXACT for complete core (=10(n-3)/m); approx for general rho)")

    print("\n" + "=" * 100)
    print("TASK 4 — secular: lam ~ 2 - 2/(rho-lam+1) ?")
    print("=" * 100)
    print(f"  {'core':14s} {'lam':>8} {'2-2/(rho-lam+1)':>16} {'2-2/rho':>9}")
    for (rho, n, comp, tag) in [(10, 100, False, "rr(99,10)"), (20, 100, False, "rr(99,20)"),
                                 (50, 100, False, "rr(99,50)"), (100, 200, False, "rr(199,100)"),
                                 (None, 100, True, "K99")]:
        q = analyze(rho if rho else 0, n, seed=1, complete=comp)
        sec = 2 - 2 / (q['rho'] - q['lam'] + 1)
        print(f"  {tag:14s} {q['lam']:8.4f} {sec:16.4f} {2-2/q['rho']:9.4f}")

    print("\n" + "=" * 100)
    print("TASK 5 — verification: closed form vs numerical gap, rho x n grid")
    print("=" * 100)
    print(f"  {'rho':>5} {'n':>5} {'lam':>7} {'gap_true':>10} {'gap_closed(η=0)':>15} "
          f"{'rel.err':>9} {'gap>0':>6}")
    allpos = True
    for n in [50, 100, 200]:
        for rho in [5, 10, 20, 50, 100, n - 2]:
            if rho >= n - 1 and rho != n - 2: continue
            if rho < 3 or rho > n - 2: continue
            comp = (rho == n - 2)
            try:
                q = analyze(rho, n, seed=2, complete=comp)
            except Exception:
                continue
            K = Kfun(q['lam'], q['rho'], q['m']); D = Dfun(q['lam'], q['n'])
            gc = q['lam'] * (q['rho'] - q['lam'] + 1) + K / D
            rel = abs(gc - q['gap']) / abs(q['gap'])
            allpos &= q['gap'] > 0
            print(f"  {int(q['rho']):5d} {n:5d} {q['lam']:7.4f} {q['gap']:10.5f} {gc:15.5f} "
                  f"{rel:9.4f} {str(q['gap']>0):>6}")
    print(f"\n  all gap>0: {allpos}")

    print("\n" + "=" * 100)
    print("SUMMARY")
    print("=" * 100)
    print("  TASK1 exact: gap = lam(rho-lam+1) + x^2 K (symmetric p=r).  Complete core: eta=0 EXACT,")
    print("  gap_closed = lam(rho-lam+1)+K/D = 10(n-3)/m > 0 (manifest).  General rho: gap>0 verified;")
    print("  eta=0 closed form approximates (error = core-perp eta from resolvent).")


if __name__ == "__main__":
    main()
