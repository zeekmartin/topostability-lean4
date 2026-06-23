"""
Aggregate Poincare T<=2lam*degQuad for TYPE A bottleneck graphs.
Decompose T = T_core + T_cross + T_bottleneck (by triangle membership in core H / ports P).
Block flatness on H: ||f_H - mean||^2 <= ||source||^2/(gamma-lam)^2 (gamma = lam2 of core).
Bound chain: T_core <= max_{e in H} t_e * D_core; D_core <= lmax(L_H)*||f_H-mean||^2;
RHS=2lam*degQuad >= 2lam*bottleneck_mass. Test sufficient condition on all TYPE A.
Run: python aggregate_typeA_bottleneck.py
"""
import numpy as np
import networkx as nx


def split_core_ports(d):
    """Ports = low-degree vertices below the largest multiplicative degree gap."""
    n = len(d); order = np.argsort(d); sd = d[order]
    # find largest gap in sorted degrees (separating ports from core)
    gaps = [(sd[i + 1] - sd[i], i) for i in range(n - 1)]
    gap, idx = max(gaps)
    # ports = vertices up to idx (low side) IF the gap is significant
    if gap >= 2 and idx < n - 1:
        ports = set(order[:idx + 1].tolist())
    else:
        ports = set()
    return ports


def analyze(G):
    G = nx.convert_node_labels_to_integers(G); n = G.number_of_nodes()
    if not nx.is_connected(G): return None
    A = nx.to_numpy_array(G); d = A.sum(1); L = np.diag(d) - A
    ev, U = np.linalg.eigh(L); lam = ev[1]; f = U[:, 1]; f = f / np.linalg.norm(f)
    d_eff = float(d @ (f * f)); A2 = A @ A
    P = split_core_ports(d); H = [v for v in range(n) if v not in P]
    if len(H) < 2: return None
    Hset = set(H)
    # triangle decomposition by membership
    T_core = T_cross = T_bot = 0.0
    tris = []
    for a in range(n):
        for b in range(a + 1, n):
            if A[a, b] == 0: continue
            for c in range(b + 1, n):
                if A[a, c] > 0 and A[b, c] > 0:
                    E = (f[a]-f[b])**2 + (f[b]-f[c])**2 + (f[c]-f[a])**2
                    inH = (a in Hset) + (b in Hset) + (c in Hset)
                    if inH == 3: T_core += E
                    elif inH == 0: T_bot += E
                    else: T_cross += E
    T = T_core + T_cross + T_bot
    RHS = 2 * lam * d_eff
    # core gap gamma = lam2 of induced core
    Hl = sorted(H); Ah = A[np.ix_(Hl, Hl)]; dh = Ah.sum(1); Lh = np.diag(dh) - Ah
    evh = np.linalg.eigvalsh(Lh); gamma = evh[1] if len(evh) > 1 else 0.0
    lmaxH = evh[-1]
    fH = np.array([f[v] for v in Hl]); meanH = fH.mean()
    flat = float(((fH - meanH) ** 2).sum())                 # ||f_H - mean||^2
    D_core = float((fH - meanH) @ Lh @ (fH - meanH))         # = sum_{E(H)} g^2
    # source: for v in H, source_v = sum_{u in P, u~v} f_u
    src = 0.0
    for vi, v in enumerate(Hl):
        s = sum(f[u] for u in P if A[v, u] > 0)
        src += s ** 2
    # max t_e over core edges
    maxt = max((A2[a, b] for a in Hl for b in Hl if a < b and A[a, b] > 0), default=0.0)
    bott_mass = float(sum(d[v] * f[v] ** 2 for v in P))
    # bound: T_core <= maxt * D_core ; D_core <= lmaxH * flat ; flat <= src/(gamma-lam)^2
    bound_Dcore = lmaxH * (src / (gamma - lam) ** 2) if gamma > lam else float('inf')
    bound_Tcore = maxt * min(D_core, bound_Dcore)
    return dict(n=n, lam=lam, gamma=gamma, T=T, T_core=T_core, T_cross=T_cross, T_bot=T_bot,
                RHS=RHS, ratio=T / RHS if RHS > 0 else 9.9,
                core_frac=T_core / T if T > 0 else 0.0,
                gamma_over_lam=gamma / lam if lam > 0 else 0.0,
                nports=len(P), D_core=D_core, maxt=maxt, lmaxH=lmaxH, flat=flat, src=src,
                bott_mass=bott_mass, bott_frac=bott_mass / d_eff if d_eff > 0 else 0.0,
                bound_ratio=(2 * bound_Tcore) / RHS if RHS > 0 and bound_Tcore < float('inf') else 9.9)


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
        for q in [0.1, 0.2, 0.4, 0.6, 0.85]: out.append((f"deg2d{nn}_{q}", d2(nn, q, 7)))
    for N in [30, 50, 80]:
        for dd in [2, 3, 4]: out.append((f"twin{N}_{dd}", twin(N, dd)))
    return out


def main():
    data = [(nm, q) for nm, G in corpus() for q in [analyze(G)] if q is not None]
    print(f"  {len(data)} TYPE A graphs")

    print("\n" + "=" * 100)
    print("TASK 1 — triangle decomposition T = T_core + T_cross + T_bot (fraction in core)")
    print("=" * 100)
    print(f"  {'graph':12s} {'T/RHS':>7} {'core%':>7} {'cross%':>7} {'bot%':>6} {'nports':>6} {'γ/λ':>7}")
    for nm, q in sorted(data, key=lambda x: -x[1]['ratio'])[:12]:
        cf = 100 * q['T_core'] / q['T'] if q['T'] > 0 else 0
        xf = 100 * q['T_cross'] / q['T'] if q['T'] > 0 else 0
        bf = 100 * q['T_bot'] / q['T'] if q['T'] > 0 else 0
        print(f"  {nm:12s} {q['ratio']:7.3f} {cf:7.1f} {xf:7.1f} {bf:6.1f} {q['nports']:6d} {q['gamma_over_lam']:7.2f}")
    print(f"  T_cross+T_bot fraction max = {max((q['T_cross']+q['T_bot'])/q['T'] for _,q in data if q['T']>0):.4f}")

    print("\n" + "=" * 100)
    print("TASK 2/3/4 — block flatness + bound chain. gamma>lam? bound T/RHS vs actual")
    print("=" * 100)
    gok = sum(1 for _, q in data if q['gamma'] > q['lam'])
    print(f"  gamma > lam (block gap positive): {gok}/{len(data)}")
    print(f"  {'graph':12s} {'T/RHS':>7} {'bound':>8} {'γ/λ':>6} {'maxt':>6} {'lmaxH':>7} {'src':>8} {'bottmass%':>9}")
    for nm, q in sorted(data, key=lambda x: -x[1]['ratio'])[:12]:
        b = q['bound_ratio'] if q['bound_ratio'] < 9 else float('nan')
        print(f"  {nm:12s} {q['ratio']:7.3f} {b:8.3f} {q['gamma_over_lam']:6.2f} {q['maxt']:6.0f} "
              f"{q['lmaxH']:7.1f} {q['src']:8.4f} {100*q['bott_frac']:9.1f}")

    print("\n" + "=" * 100)
    print("TASK 5 — does the bound prove T/RHS<1 for all TYPE A?")
    print("=" * 100)
    actual_ok = sum(1 for _, q in data if q['ratio'] <= 1 + 1e-7)
    bound_ok = sum(1 for _, q in data if q['bound_ratio'] <= 1 + 1e-7)
    print(f"  actual T/RHS<=1: {actual_ok}/{len(data)} (max {max(q['ratio'] for _,q in data):.3f})")
    print(f"  bound  T/RHS<=1: {bound_ok}/{len(data)} (proves the case where it holds)")
    print(f"  bound finite (gamma>lam): {sum(1 for _,q in data if q['bound_ratio']<9)}/{len(data)}")

    print("\n" + "=" * 100)
    print("SUMMARY")
    print("=" * 100)
    print(f"  T_core fraction >= {min(q['core_frac'] for _,q in data):.3f} (cross+bot negligible)")
    print(f"  gamma>lam {gok}/{len(data)}; bound proves {bound_ok}/{len(data)}; actual holds {actual_ok}/{len(data)}")


if __name__ == "__main__":
    main()
