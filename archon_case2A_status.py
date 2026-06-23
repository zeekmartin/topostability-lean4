"""
Case 2A (vertex bottleneck, Required>0): resolvent + CF block gap closure of triEnergy <= RHS.
Bridge: triEnergy <= (delta-1)D_port + maxt_core*D_core (per-class triCount bounds).
Resolvent: core H gap gamma=lam2(L_H); (L_H-lam)f_H = source (port boundary);
  D_core = sum mu_k/(mu_k-lam)^2 <source,phi_k>^2 <= [gamma/(gamma-lam)^2]||source||^2 (CF block gap).
Check: (delta-1)D_port + maxt_core*D_core_bound <= RHS.
Run: python archon_case2A_status.py
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
    if required <= 1e-9: return None                                   # Case 2A: Required>0 only
    RHS = 2 * lam * (2 * degQuad - lam - degLin ** 2 / mE)             # = triEnergy bound (Case 2A target)
    P = split_ports(d); H = sorted(set(range(n)) - P)
    if len(H) < 2 or len(P) == 0: return None
    edges = [(i, j) for i in range(n) for j in range(i + 1, n) if A[i, j] > 0]
    Dport = Dcore = 0.0
    for a, b in edges:
        g2 = (f[a] - f[b]) ** 2; inP = (a in P) + (b in P)
        if inP == 0: Dcore += g2
        elif inP == 1: Dport += g2
    delta = max(d[p] for p in P)
    maxt_core = max((A2[a, b] for a, b in edges if a not in P and b not in P), default=0.0)
    # core block resolvent
    Ah = A[np.ix_(H, H)]; dh = Ah.sum(1); Lh = np.diag(dh) - Ah
    evh, Uh = np.linalg.eigh(Lh); gamma = evh[1] if len(evh) > 1 else 0.0; lmaxH = evh[-1]
    fH = np.array([f[v] for v in H])
    source = Lh @ fH - lam * fH                                        # (L_H - lam) f_H
    one = np.ones(len(H)) / np.sqrt(len(H))
    src_perp = source - (source @ one) * one                          # off 1_H
    src2 = float(src_perp @ src_perp)
    # exact resolvent D_core (eigendecomp of L_H, modes mu_k>lam): should equal actual Dcore
    Dcore_exact = 0.0
    for k in range(len(H)):
        if abs(evh[k] - lam) > 1e-9:
            ck = float(Uh[:, k] @ source)
            Dcore_exact += evh[k] / (evh[k] - lam) ** 2 * ck ** 2
    # resolvent bounds
    res_gamma = gamma / (gamma - lam) ** 2 * src2 if gamma > lam else float('inf')   # tight CF bound
    res_lmax = lmaxH / (gamma - lam) ** 2 * src2 if gamma > lam else float('inf')    # Rayleigh (loose)
    Tcore = sum(A2[a, b] * (f[a] - f[b]) ** 2 for a, b in edges if a not in P and b not in P)
    closure_gamma = (delta - 1) * Dport + maxt_core * res_gamma                       # ordered? unordered
    # NB: bridge uses ordered triEnergy = 2*(...); RHS already ordered. compare 2*bound to RHS.
    return dict(name=name, n=n, gamma=gamma, lam=lam, gamma_over_lam=gamma / lam, lmaxH=lmaxH,
                Dcore=Dcore, Dcore_exact=Dcore_exact, src2=src2, delta=delta, maxt_core=maxt_core,
                res_gamma=res_gamma, res_lmax=res_lmax, Tcore=Tcore, Dport=Dport, RHS=RHS,
                T_over_RHS=(2 * (Tcore + (sum(A2[a, b] * (f[a] - f[b]) ** 2 for a, b in edges
                                              if (a in P) != (b in P))))) / RHS,
                bound_gamma_over_RHS=2 * ((delta - 1) * Dport + maxt_core * res_gamma) / RHS,
                bound_lmax_over_RHS=2 * ((delta - 1) * Dport + maxt_core * res_lmax) / RHS,
                res_tight=Dcore / res_gamma if res_gamma not in (0, float('inf')) else 0.0)


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
    print(f"  {len(data)} Case 2A graphs (Required>0, vertex bottleneck)")

    print("\n" + "=" * 96)
    print("TASK 2 — CF block gap γ and resolvent. D_core_exact == D_core (sanity); gap ratio γ/λ")
    print("=" * 96)
    print(f"  D_core resolvent-exact vs actual: max err {max(abs(q['Dcore']-q['Dcore_exact']) for _,q in data):.2e}")
    print(f"  {'graph':12s} {'γ/λ':>7} {'γ':>7} {'λ_maxH':>7} {'res tight (D/bnd)':>17}")
    for nm, q in sorted(data, key=lambda x: x[1]['gamma_over_lam'])[:8]:
        print(f"  {nm:12s} {q['gamma_over_lam']:7.1f} {q['gamma']:7.2f} {q['lmaxH']:7.1f} {q['res_tight']:17.3f}")

    print("\n" + "=" * 96)
    print("TASK 2 — closure: 2[(δ-1)D_port + maxt_core·res_bound] ≤ RHS ?  (γ-tight vs λ_max)")
    print("=" * 96)
    cg = sum(1 for _, q in data if q['bound_gamma_over_RHS'] <= 1 + 1e-7)
    cl = sum(1 for _, q in data if q['bound_lmax_over_RHS'] <= 1 + 1e-7)
    print(f"  γ-resolvent closes (bound/RHS<=1): {cg}/{len(data)} (max {max(q['bound_gamma_over_RHS'] for _,q in data):.3f})")
    print(f"  λ_max-resolvent closes:            {cl}/{len(data)} (max {max(q['bound_lmax_over_RHS'] for _,q in data):.3f})")
    print(f"  {'graph':12s} {'T/RHS':>7} {'γ-bnd/RHS':>10} {'λmax-bnd/RHS':>12} {'γ/λ':>7}")
    for nm, q in sorted(data, key=lambda x: -x[1]['bound_gamma_over_RHS'])[:12]:
        print(f"  {nm:12s} {q['T_over_RHS']:7.3f} {q['bound_gamma_over_RHS']:10.3f} {q['bound_lmax_over_RHS']:12.3f} {q['gamma_over_lam']:7.1f}")

    print("\n" + "=" * 96)
    print("SUMMARY")
    print("=" * 96)
    print(f"  γ-resolvent Case 2A closure: {cg}/{len(data)}; λ_max: {cl}/{len(data)}")
    print(f"  actual T/RHS <= {max(q['T_over_RHS'] for _,q in data):.3f}; γ/λ >= {min(q['gamma_over_lam'] for _,q in data):.1f}")


if __name__ == "__main__":
    main()
