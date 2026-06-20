"""
TYPE A electrical-network view: invariant search + Green's-function sum rule for eff_resist.

G = H + v0 (v0~{a,b}).  gap = lam2G - B2'.  c = gap*m/n.
eff_resist(a,b) = R_aa + R_bb - 2R_ab,  R = (L_H - lam I)^{-1} on 1_H^perp.

Spectral sum rule (TASK 3):
  eff_resist = sum_{k>=2} (phi_k(a)-phi_k(b))^2 / (mu_k - lam),  with  sum_{k>=2}(...)^2 = 2
  (since e_a-e_b is already orthogonal to 1).  => 2/(mu_max-lam) <= eff <= 2/(gamma-lam).
Run: python conjecture_B_typeA_electrical.py
"""
import numpy as np
import networkx as nx


def analyze(H, a=0, b=1):
    H = nx.convert_node_labels_to_integers(H); nH = H.number_of_nodes()
    if not nx.is_connected(H): return None
    G = nx.Graph(H); G.add_node(nH); G.add_edge(nH, a); G.add_edge(nH, b)
    nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}
    A = nx.to_numpy_array(G, nodelist=nodes); d = A.sum(1); L = np.diag(d) - A
    ev, U = np.linalg.eigh(L); lam = ev[1]; f = U[:, 1]; f = f / np.linalg.norm(f)
    v0 = idx[nH]
    if f[v0] < 0: f = -f
    m = G.number_of_edges(); S = float(d @ f)
    Gsum = sum((f[idx[u]] + f[idx[v]]) ** 2 for u, v in G.edges())
    B2 = sum((min(d[idx[u]], d[idx[v]]) - 1) * (f[idx[u]] - f[idx[v]]) ** 2 for u, v in G.edges())
    gap = lam * (Gsum - S ** 2 / m) - B2
    LH = nx.laplacian_matrix(H, nodelist=list(range(nH))).toarray().astype(float)
    mu, phi = np.linalg.eigh(LH); gamma = float(mu[1]); mu_max = float(mu[-1])
    # spectral eff_resist
    w = (phi[a, 1:] - phi[b, 1:]) ** 2           # weights, sum=2
    eff_spec = float(np.sum(w / (mu[1:] - lam)))
    # direct eff_resist
    R = (phi[:, 1:] / (mu[1:] - lam)) @ phi[:, 1:].T
    eff = float(R[a, a] + R[b, b] - 2 * R[a, b])
    return dict(nH=nH, n=nH + 1, m=m, lam=lam, gamma=gamma, mu_max=mu_max, gap=gap,
                eff=eff, eff_spec=eff_spec, wsum=float(np.sum(w)),
                Raa=float(R[a, a]), Rbb=float(R[b, b]), Rab=float(R[a, b]),
                fv0=float(f[v0]), c=gap * m / (nH + 1))


def typeA(r): return r is not None and r['lam'] < r['gamma'] and r['fv0'] ** 2 > 0.3


def fam():
    out = []
    for nH in [30, 60, 120]:
        out.append((f"K{nH}", nx.complete_graph(nH)))
        for q in [0.3, 0.5, 0.7, 0.9]:
            out.append((f"gnp{nH}_{q}", nx.gnp_random_graph(nH, q, seed=3)))
        for frac in [0.25, 0.5]:
            r = max(3, int(frac * nH)); r += (r * nH) % 2
            if r <= nH - 1:
                out.append((f"rr{nH}_{r}", nx.random_regular_graph(r, nH, seed=3)))
        out.append((f"circ{nH}", nx.circulant_graph(nH, list(range(1, nH // 5 + 1)))))
    return out


def main():
    data = [(nm, analyze(H)) for nm, H in fam()]
    data = [(nm, r) for nm, r in data if typeA(r)]

    print("=" * 100)
    print("TASK 1 — invariant candidates: which is constant / bounded away from 0?")
    print("=" * 100)
    print(f"  {'family':12s} {'n':>4} {'lam':>6} {'gamma':>7} {'gap':>8} {'eff':>8} "
          f"{'c=gap*m/n':>9} {'gap/eff':>8} {'c*eff':>8} {'c/gamma':>8}")
    for nm, r in data:
        print(f"  {nm:12s} {r['n']:4d} {r['lam']:6.3f} {r['gamma']:7.2f} {r['gap']:8.4f} "
              f"{r['eff']:8.4f} {r['c']:9.4f} {r['gap']/r['eff']:8.3f} {r['c']*r['eff']:8.4f} "
              f"{r['c']/r['gamma']:8.4f}")
    for key, lab in [('gap/eff', lambda r: r['gap'] / r['eff']),
                     ('c*eff', lambda r: r['c'] * r['eff']),
                     ('c/gamma', lambda r: r['c'] / r['gamma']),
                     ('gap*gamma', lambda r: r['gap'] * r['gamma'])]:
        vals = np.array([lab(r) for _, r in data])
        print(f"  {key:10s}: min={vals.min():.3f} median={np.median(vals):.3f} max={vals.max():.3f} "
              f"spread(max/min)={vals.max()/max(vals.min(),1e-9):.1f}")

    print("\n" + "=" * 100)
    print("TASK 3 — Green's-function sum rule for eff_resist + bounds")
    print("=" * 100)
    serr = max(abs(r['eff'] - r['eff_spec']) for _, r in data)
    werr = max(abs(r['wsum'] - 2.0) for _, r in data)
    print(f"  eff (direct) == eff (spectral sum): max diff {serr:.2e}")
    print(f"  weight sum  sum_k (phi_k(a)-phi_k(b))^2 == 2 : max |.-2| = {werr:.2e}")
    ok = sum(1 for _, r in data
             if 2 / (r['mu_max'] - r['lam']) - 1e-9 <= r['eff'] <= 2 / (r['gamma'] - r['lam']) + 1e-9)
    print(f"  bounds  2/(mu_max-lam) <= eff <= 2/(gamma-lam) : {ok}/{len(data)}")
    print(f"  => eff_resist > 0 ALWAYS (all terms (phi_a-phi_b)^2/(mu_k-lam) > 0 for lam<gamma).")
    # gamma*eff range (re-confirm)
    ge = np.array([r['gamma'] * r['eff'] for _, r in data])
    print(f"  gamma*eff: min={ge.min():.3f} max={ge.max():.3f}  (eff ~ Theta(1/gamma))")

    print("\n" + "=" * 100)
    print("TASK 4 — rank-2 / eigenvalue-shift view: gap vs (gamma-lam) and (2-lam)")
    print("=" * 100)
    print(f"  {'family':12s} {'gamma-lam':>9} {'2-lam':>7} {'gap':>8} {'gap*(gamma-lam)':>15} "
          f"{'gap/(2-lam)':>11}")
    for nm, r in data:
        g2 = r['gap'] * (r['gamma'] - r['lam'])
        print(f"  {nm:12s} {r['gamma']-r['lam']:9.3f} {2-r['lam']:7.4f} {r['gap']:8.4f} "
              f"{g2:15.4f} {r['gap']/(2-r['lam']) if 2-r['lam']>1e-6 else float('inf'):11.2f}")

    print("\n" + "=" * 100)
    print("SUMMARY")
    print("=" * 100)
    print("  Report which invariant (if any) is constant; eff_resist sum rule gives eff>0 with")
    print("  bounds 2/(mu_max-lam) <= eff <= 2/(gamma-lam). Honest read on whether c has a clean")
    print("  electrical closed form.")


if __name__ == "__main__":
    main()
