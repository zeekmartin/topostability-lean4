"""
Tighten the D_core bound for Case 2A. D_core = s^T (R L_H R) s, R=(L_H-lam)^{-1}_perp,
s = port-boundary source (supported on dD = core vertices adjacent to ports).
Exact: D_core = sum_k gamma_k/(gamma_k-lam)^2 <s,phi_k>^2.
Bounds tested: max (current), trace(R^2), n_eff, BLOCK lambda_max((RLR)_{dD,dD}), diag.
Closure: (delta-1)D_port + maxt_core*D_core_bound <= RHS, 2*[...]<=RHS (ordered).
Run: python case2A_dcore_tightening.py
"""
import numpy as np
import networkx as nx


def split_ports(d):
    n = len(d); order = np.argsort(d); sd = d[order]
    gaps = [(sd[i + 1] - sd[i], i) for i in range(n - 1)]; gap, idx = max(gaps)
    return set(order[:idx + 1].tolist()) if (gap >= 2 and idx < n - 1) else set()


def analyze(G, name):
    G = nx.convert_node_labels_to_integers(G); n = G.number_of_nodes()
    if not nx.is_connected(G): return None
    A = nx.to_numpy_array(G); d = A.sum(1); L = np.diag(d) - A; A2 = A @ A
    ev, U = np.linalg.eigh(L); lam = ev[1]; f = U[:, 1]; f = f / np.linalg.norm(f)
    mE = G.number_of_edges(); degQuad = float(d @ (f * f)); degLin = float(d @ f)
    required = 2 * lam * (lam + degLin ** 2 / mE - degQuad)
    if required <= 1e-9: return None
    RHS = 2 * lam * (2 * degQuad - lam - degLin ** 2 / mE)
    P = split_ports(d); H = sorted(set(range(n)) - P)
    if len(H) < 2 or len(P) == 0: return None
    edges = [(i, j) for i in range(n) for j in range(i + 1, n) if A[i, j] > 0]
    Dport = sum((f[a] - f[b]) ** 2 for a, b in edges if (a in P) != (b in P))
    delta = max(d[p] for p in P)
    maxt_core = max((A2[a, b] for a, b in edges if a not in P and b not in P), default=0.0)
    # core block
    idx = {v: i for i, v in enumerate(H)}
    Ah = A[np.ix_(H, H)]; dh = Ah.sum(1); Lh = np.diag(dh) - Ah
    evh, Uh = np.linalg.eigh(Lh); gamma = evh[1]; nz = evh > 1e-9
    fH = f[H]; source = Lh @ fH - lam * fH
    s2 = float(source @ source)
    # exact D_core via modes
    ck = Uh.T @ source                                   # <s,phi_k>
    contrib = np.array([ck[k] ** 2 / (evh[k] - lam) ** 2 for k in range(len(H))])   # flatness modal
    Dcontrib = np.array([evh[k] * ck[k] ** 2 / (evh[k] - lam) ** 2 if abs(evh[k] - lam) > 1e-9 else 0.0
                         for k in range(len(H))])
    Dcore = float(Dcontrib.sum())
    # participation ratio of D_core modal contributions
    pr = (Dcontrib.sum() ** 2 / (Dcontrib ** 2).sum()) if (Dcontrib ** 2).sum() > 0 else 0.0
    nsig = int((Dcontrib > 0.01 * Dcontrib.max()).sum())
    # R L_H R operator
    Rinv2 = np.zeros((len(H), len(H)))
    for k in range(len(H)):
        if nz[k] and abs(evh[k] - lam) > 1e-9:
            Rinv2 += (evh[k] / (evh[k] - lam) ** 2) * np.outer(Uh[:, k], Uh[:, k])   # R L_H R
    # boundary set dD = core vertices adjacent to ports
    dD = [idx[v] for v in H if any((p in P) and A[v, p] > 0 for p in range(n))]
    # bounds (all * s2 unless noted)
    b_max = gamma / (gamma - lam) ** 2 * s2
    b_traceR2 = s2 * sum(1 / (evh[k] - lam) ** 2 for k in range(len(H)) if nz[k] and abs(evh[k] - lam) > 1e-9)
    sumInv = sum(1 / (evh[k] - lam) for k in range(len(H)) if nz[k] and abs(evh[k] - lam) > 1e-9)
    sumInv2 = sum(1 / (evh[k] - lam) ** 2 for k in range(len(H)) if nz[k] and abs(evh[k] - lam) > 1e-9)
    n_eff = (sumInv ** 2 / sumInv2) if sumInv2 > 0 else 1.0
    b_neff = s2 / (n_eff * (gamma - lam) ** 2)
    # BLOCK bound: lambda_max((R L_H R)_{dD,dD}) * s2   (valid: source supported on dD)
    if dD:
        Mblk = Rinv2[np.ix_(dD, dD)]
        b_block = float(np.linalg.eigvalsh(Mblk)[-1]) * s2
        b_diag = float(np.max(np.diag(Rinv2)[dD])) * s2 * len(dD)   # rough diag*|dD|
    else:
        b_block = b_diag = float('inf')
    def clo(b): return 2 * ((delta - 1) * Dport + maxt_core * b) / RHS
    return dict(name=name, n=n, s2=s2, Dport=Dport, s2_eq_Dport=abs(s2 - Dport),
                Dcore=Dcore, gamma=gamma, lam=lam, pr=pr, nsig=nsig, ncore=len(H), ndD=len(dD),
                eff_factor=Dcore / s2, max_factor=gamma / (gamma - lam) ** 2,
                valid_block=b_block >= Dcore - 1e-9, valid_traceR2=b_traceR2 >= Dcore - 1e-9,
                valid_neff=b_neff >= Dcore - 1e-9,
                c_max=clo(b_max), c_traceR2=clo(b_traceR2), c_neff=clo(b_neff),
                c_block=clo(b_block), c_exact=clo(Dcore))


def corpus():
    out = []
    def d2(nn, q, s):
        H = nx.gnp_random_graph(nn - 1, q, seed=s); H.add_node(nn - 1); H.add_edge(nn - 1, 0); H.add_edge(nn - 1, 1); return H
    def twin(N, dd):
        K = nx.complete_graph(N); a, b = N, N + 1
        for x in (a, b):
            for w in range(dd): K.add_edge(x, w)
        K.add_node(N + 2); K.add_edge(N + 2, a); K.add_edge(N + 2, b); return K
    for nn in [40, 60, 80]:
        for q in [0.2, 0.4, 0.6, 0.85]: out.append((f"deg2d{nn}_{q}", d2(nn, q, 7)))
    for N in [30, 50, 80]:
        for dd in [2, 3, 4]: out.append((f"twin{N}_{dd}", twin(N, dd)))
    return out


def main():
    data = [(nm, q) for nm, G in corpus() for q in [analyze(G, nm)] if q is not None]
    N = len(data)
    print(f"  {N} Case 2A graphs.  ||s||²=D_port: max err {max(q['s2_eq_Dport'] for _,q in data):.1e}")

    print("\n" + "=" * 98)
    print("TASK 1 — source spectrum: effective vs max modal factor; participation ratio; #significant modes")
    print("=" * 98)
    print(f"  {'graph':12s} {'eff_factor':>10} {'max_factor':>10} {'eff/max':>8} {'PR':>6} {'#sig':>5} {'ncore':>6} {'|∂|':>4}")
    for nm, q in sorted(data, key=lambda x: -x[1]['eff_factor'] / x[1]['max_factor'])[:10]:
        print(f"  {nm:12s} {q['eff_factor']:10.4f} {q['max_factor']:10.4f} {q['eff_factor']/q['max_factor']:8.3f} "
              f"{q['pr']:6.1f} {q['nsig']:5d} {q['ncore']:6d} {q['ndD']:4d}")

    print("\n" + "=" * 98)
    print("TASK 2/3/4 — bound validity (>= actual D_core?) and closure count (closes if 2[...]/RHS<=1)")
    print("=" * 98)
    bounds = [('max γ/(γ-λ)²', 'c_max', 'valid (always)'),
              ('traceR2 ‖s‖²Σ1/(γ-λ)²', 'c_traceR2', 'valid_traceR2'),
              ('n_eff', 'c_neff', 'valid_neff'),
              ('BLOCK λmax((RLR)_∂∂)', 'c_block', 'valid_block'),
              ('exact D_core', 'c_exact', 'valid (=)')]
    for label, ckey, vkey in bounds:
        clo = sum(1 for _, q in data if q[ckey] <= 1 + 1e-7)
        if vkey.startswith('valid_'):
            valid = sum(1 for _, q in data if q[vkey])
            vstr = f"valid {valid}/{N}"
        else:
            vstr = vkey
        mx = max(q[ckey] for _, q in data)
        print(f"  {label:24s} closes {clo:2d}/{N}  (max ratio {mx:.3f})  [{vstr}]")

    print("\n" + "=" * 98)
    print("BLOCK bound detail (the candidate tighter VALID bound)")
    print("=" * 98)
    print(f"  {'graph':12s} {'c_block':>8} {'c_max':>8} {'c_exact':>8} {'valid_block':>11}")
    for nm, q in sorted(data, key=lambda x: -x[1]['c_block'])[:12]:
        print(f"  {nm:12s} {q['c_block']:8.3f} {q['c_max']:8.3f} {q['c_exact']:8.3f} {str(q['valid_block']):>11}")

    print("\n" + "=" * 98)
    print("SUMMARY")
    print("=" * 98)
    for label, ckey, vkey in bounds:
        clo = sum(1 for _, q in data if q[ckey] <= 1 + 1e-7)
        print(f"  {label:24s}: {clo}/{N} close")


if __name__ == "__main__":
    main()
