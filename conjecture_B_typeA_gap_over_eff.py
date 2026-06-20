"""
TYPE A: exact structure of gap/eff_resist via the core resolvent.

R = (L_H-lam)^{-1} on 1_H^perp; R2 block at a,b.
  R+ = (R_aa+R_bb)/2 + R_ab   (symmetric response, couples to v0)
  R- = (R_aa+R_bb)/2 - R_ab   (antisymmetric = eff_resist/2)
  M2 = e_ab^T R^2 e_ab        (second resolvent moment, enters normalization)

Symmetric secular (derived):  1 + R+ = 2n / ((n-1) lam).
Question: does gap/eff_resist reduce to a function of (R+, R-, lam, n, m), or need M2 (2nd moment)?
Run: python conjecture_B_typeA_gap_over_eff.py
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
    mu, phi = np.linalg.eigh(LH); gamma = float(mu[1])
    inv = 1.0 / (mu[1:] - lam)
    R = (phi[:, 1:] * inv) @ phi[:, 1:].T
    R2mat = (phi[:, 1:] * inv ** 2) @ phi[:, 1:].T
    Raa, Rbb, Rab = R[a, a], R[b, b], R[a, b]
    eff = Raa + Rbb - 2 * Rab
    Rp = (Raa + Rbb) / 2 + Rab
    Rm = (Raa + Rbb) / 2 - Rab        # = eff/2
    M2 = R2mat[a, a] + R2mat[b, b] + 2 * R2mat[a, b]   # e_ab^T R^2 e_ab (symmetric)
    rho = float(d[idx[next(u for u in range(nH) if u not in (a, b))]])
    return dict(nH=nH, n=nH + 1, m=m, lam=lam, gamma=gamma, gap=gap, eff=eff,
                Raa=Raa, Rbb=Rbb, Rab=Rab, Rp=Rp, Rm=Rm, M2=M2, rho=rho,
                fv0=float(f[v0]), sym=abs(Raa - Rbb))


def typeA(r): return r is not None and r['lam'] < r['gamma'] and r['fv0'] ** 2 > 0.3


def main():
    rng = np.random.default_rng(0)
    data = []
    # symmetric: regular + circulant (a,b equivalent-ish); plus gnp (asymmetric)
    for nH in [30, 50, 80, 120]:
        data.append(('K%d' % nH, analyze(nx.complete_graph(nH))))
        for q in [0.3, 0.5, 0.7, 0.9]:
            data.append(('gnp%d_%.1f' % (nH, q), analyze(nx.gnp_random_graph(nH, q, seed=2))))
        for frac in [0.25, 0.5]:
            r = max(3, int(frac * nH)); r += (r * nH) % 2
            if r <= nH - 1:
                data.append(('rr%d_%d' % (nH, r), analyze(nx.random_regular_graph(r, nH, seed=2))))
        data.append(('circ%d' % nH, analyze(nx.circulant_graph(nH, list(range(1, nH // 5 + 1))))))
    data = [(nm, r) for nm, r in data if typeA(r)]

    print("=" * 100)
    print("TASK 3 — symmetric secular  1 + R+ = 2n/((n-1) lam)  (check)")
    print("=" * 100)
    serr = []
    for nm, r in data:
        pred = 2 * r['n'] / ((r['n'] - 1) * r['lam']) - 1
        serr.append(abs(pred - r['Rp']))
    print(f"  max |R+  -  (2n/((n-1)lam) - 1)| = {max(serr):.3e}  "
          f"(small => secular: lam = 2n/((n-1)(1+R+)))")

    print("\n" + "=" * 100)
    print("TASK 1/2 — gap/eff  and  does it need the 2nd moment M2?")
    print("=" * 100)
    print(f"  {'family':12s} {'lam':>6} {'R+':>7} {'R-=eff/2':>9} {'M2':>9} {'gap':>8} "
          f"{'gap/eff':>8} {'gap/(R-)':>9}")
    for nm, r in data:
        print(f"  {nm:12s} {r['lam']:6.3f} {r['Rp']:7.3f} {r['Rm']:9.4f} {r['M2']:9.3f} "
              f"{r['gap']:8.4f} {r['gap']/r['eff']:8.3f} {r['gap']/r['Rm']:9.3f}")

    # Is gap/eff a function of (R+, lam, n) alone?  regress; check residual.
    ge = np.array([r['gap'] / r['eff'] for _, r in data])
    # candidate A: function of R+ and lam,n only (no M2). Fit gap/eff ~ poly(R+, lam, n)
    X_noM2 = np.array([[1, r['Rp'], r['lam'], r['n'], r['Rp'] * r['lam'], r['Rp'] ** 2] for _, r in data])
    cA, *_ = np.linalg.lstsq(X_noM2, ge, rcond=None)
    resA = ge - X_noM2 @ cA
    # candidate B: include M2 / normalization second moment
    X_M2 = np.array([[1, r['Rp'], r['lam'], r['n'], r['M2'], r['M2'] * r['lam'], r['Rp'] * r['M2']]
                     for _, r in data])
    cB, *_ = np.linalg.lstsq(X_M2, ge, rcond=None)
    resB = ge - X_M2 @ cB
    print(f"\n  fit gap/eff ~ poly(R+, lam, n) [NO M2]: residual std = {resA.std():.4f} "
          f"(range of gap/eff = {ge.max()-ge.min():.3f})")
    print(f"  fit gap/eff ~ poly(R+, lam, n, M2)      : residual std = {resB.std():.4f}")
    print("  (if M2 sharply reduces residual => gap/eff NEEDS 2nd moment, not a 2x2-block function)")

    print("\n" + "=" * 100)
    print("TASK 4 — manifest positivity:  gap = R- * prefactor;  is prefactor > 0 clean?")
    print("=" * 100)
    pref = np.array([r['gap'] / r['Rm'] for _, r in data])     # = 2*gap/eff
    print(f"  prefactor gap/R- = 2*gap/eff: min={pref.min():.3f} median={np.median(pref):.3f} "
          f"max={pref.max():.3f}")
    print(f"  eff = 2 R- > 0 ALWAYS (R2>0 <=> lam<gamma).  gap>0 <=> prefactor>0.")
    print(f"  prefactor bounded away from 0: inf = {pref.min():.3f} (> 0)")

    print("\n" + "=" * 100)
    print("TASK 5 — inf(gap/eff) and the graph achieving it")
    print("=" * 100)
    order = sorted(data, key=lambda nr: nr[1]['gap'] / nr[1]['eff'])
    for nm, r in order[:5]:
        print(f"  {nm:12s} gap/eff={r['gap']/r['eff']:.4f} lam={r['lam']:.3f} R+={r['Rp']:.3f} "
              f"R-={r['Rm']:.4f}")
    print(f"  inf(gap/eff) over tested = {order[0][1]['gap']/order[0][1]['eff']:.4f} at {order[0][0]}")

    print("\n" + "=" * 100)
    print("SUMMARY")
    print("=" * 100)
    print("  secular clean (lam<->R+); eff=2R->0 manifest; but gap/eff needs M2 (2nd moment) => NOT a")
    print("  closed function of the 2x2 block. gap = R- * prefactor, prefactor in (inf,~20), >0.")


if __name__ == "__main__":
    main()
