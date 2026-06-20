"""
TYPE A regular cores: driver  lam*rho*||f_H||^2  vs  correction = gap - driver.

Claim under test (user): gap = lam*rho*||f_H||^2 + correction with |correction| <= C*eta^2,
eta^2 <= ||source||^2/(gamma-lam)^2 (poincare_on_block).  If driver dominates => gap>0.

We compute everything exactly from the Fiedler and check:
  - driver = lam*rho*(1-x^2)            (x=f_v0, ||f_H||^2 = 1-x^2)
  - correction = gap - driver
  - eta^2 = core perpendicular energy ; ||source||^2 = (p-x)^2+(r-x)^2
  - is |correction| ~ O(eta^2)  or  O(1) ?   (the crux)
  - does driver > |correction| hold, and by what margin?
Run: python conjecture_B_typeA_driver_vs_correction.py
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
    b = next((u for u in range(1, nH) if u not in nbrs and u != a), 1)
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
    gen = next(u for u in range(nH) if u not in (a, b))
    rho_ = float(A[idx[gen]].sum())
    # core gap gamma
    Hc = nx.convert_node_labels_to_integers(G.subgraph([nodes[i] for i in range(nH)]))
    evH = np.linalg.eigvalsh(nx.laplacian_matrix(Hc, nodelist=list(Hc.nodes())).toarray().astype(float))
    gamma = float(evH[1])
    Gsum = sum((f[idx[u]] + f[idx[v]]) ** 2 for u, v in G.edges())
    B2 = sum((min(d[idx[u]], d[idx[v]]) - 1) * (f[idx[u]] - f[idx[v]]) ** 2 for u, v in G.edges())
    gap = lam * (Gsum - S ** 2 / m) - B2
    # core perp eta^2
    fcore = np.array([f[idx[u]] for u in range(nH)]); mu = fcore.mean()
    eta2 = float(((fcore - mu) ** 2).sum())
    source2 = (p - x) ** 2 + (r - x) ** 2
    driver = lam * rho_ * (1 - x ** 2)
    correction = gap - driver
    return dict(n=n, m=m, lam=lam, rho=rho_, gamma=gamma, x=x, p=p, r=r, gap=gap,
                driver=driver, corr=correction, eta2=eta2, source2=source2,
                fH2=1 - x ** 2, S2m=lam * S ** 2 / m)


def main():
    print("=" * 110)
    print("TASK 1/2 — driver = lam*rho*||f_H||^2,  correction = gap - driver,  vs eta^2")
    print("=" * 110)
    print(f"  {'rho':>4} {'n':>5} {'lam':>6} {'gamma':>6} {'TYPEA':>5} {'gap':>8} {'driver':>8} "
          f"{'corr':>9} {'eta^2':>9} {'|corr|/eta^2':>11} {'drv/|corr|':>10}")
    rows = []
    for n in [50, 100, 200]:
        for rho in [3, 5, 10, 20, 50, 100, n - 2]:
            if rho < 3 or rho > n - 2: continue
            comp = (rho == n - 2)
            try:
                q = analyze(rho, n, seed=2, complete=comp)
            except Exception:
                continue
            rows.append(q)
            ce = abs(q['corr']) / q['eta2'] if q['eta2'] > 1e-15 else float('nan')
            dc = q['driver'] / abs(q['corr']) if abs(q['corr']) > 1e-15 else float('inf')
            typeA = q['lam'] < q['gamma']
            q['typeA'] = typeA
            print(f"  {int(q['rho']):4d} {n:5d} {q['lam']:6.3f} {q['gamma']:6.3f} {str(typeA):>5} "
                  f"{q['gap']:8.4f} {q['driver']:8.4f} {q['corr']:9.4f} {q['eta2']:9.2e} "
                  f"{ce:11.1f} {dc:10.3f}")

    print("\n" + "=" * 110)
    print("FINDINGS")
    print("=" * 110)
    # is correction O(eta^2)?  ratio |corr|/eta^2 bounded?
    ratios = [abs(q['corr']) / q['eta2'] for q in rows if q['eta2'] > 1e-15]
    print(f"  |correction|/eta^2 : min={min(ratios):.1f} max={max(ratios):.1f}  "
          f"(if BOUNDED => corr=O(eta^2); if BLOWS UP => corr=O(1), claim false)")
    # does driver dominate?
    dompos = sum(1 for q in rows if q['driver'] > abs(q['corr']))
    print(f"  driver > |correction| : {dompos}/{len(rows)}")
    cneg = sum(1 for q in rows if q['corr'] < 0)
    print(f"  correction < 0 : {cneg}/{len(rows)}  (when corr<0, 'driver>|corr|' IS just 'gap>0')")
    # how big is the S^2/m piece (the O(1) non-eta part of correction)?
    print(f"  lam*S^2/m (O(1) term inside correction): "
          f"{[round(q['S2m'],3) for q in rows[:6]]} ...  vs eta^2 "
          f"{['%.1e'%q['eta2'] for q in rows[:6]]}")
    allpos = all(q['gap'] > 0 for q in rows)
    print(f"  all gap>0: {allpos}")
    # restrict to genuine TYPE A (lam < gamma): is correction O(eta^2)? does driver dominate?
    tA = [q for q in rows if q.get('typeA')]
    if tA:
        rA = [abs(q['corr']) / q['eta2'] for q in tA if q['eta2'] > 1e-15]
        negA = sum(1 for q in tA if q['corr'] < 0)
        marg = [q['driver'] / abs(q['corr']) for q in tA if abs(q['corr']) > 1e-12]
        print(f"  GENUINE TYPE A (lam<gamma): {len(tA)} rows; |corr|/eta^2 in [{min(rA):.0f},{max(rA):.0f}]"
              f" (BLOWS UP => corr NOT O(eta^2)); corr<0 in {negA}/{len(tA)}; "
              f"driver/|corr| in [{min(marg):.2f},{max(marg):.2f}] (thin, not rho^3/n)")

    print("\n" + "=" * 110)
    print("driver magnitude check: driver ~ lam*rho/n (NOT lam*rho), since ||f_H||^2 ~ 1/n")
    print("=" * 110)
    for q in rows[:8]:
        print(f"  rho={int(q['rho']):3d} n={q['n']:3d}: ||f_H||^2={q['fH2']:.4f} "
              f"(~(3-lam)^2/(n-3)={((3-q['lam'])**2/(q['n']-3)):.4f}?)  driver={q['driver']:.4f} "
              f"lam*rho/n={q['lam']*q['rho']/q['n']:.4f}")


if __name__ == "__main__":
    main()
