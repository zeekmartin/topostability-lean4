"""
Hard band E<0. KEY: Required = lam(lam+S^2/m-d_eff) = -E. So E<0 <=> Required>0 = REGIME ii.
The aggregate-slack dichotomy IS the original regime i/ii split.
Tasks: collect E<0; asymptotics S_agg,-E,ratio,gap; structure; hard-band lemma; coverage by
regular/TYPE A/TYPE B.
Run: python conjecture_B_hard_band_E_negative.py
"""
import numpy as np
import networkx as nx


def quant(G):
    G = nx.convert_node_labels_to_integers(G); n = G.number_of_nodes()
    if not nx.is_connected(G): return None
    A = nx.to_numpy_array(G); d = A.sum(1); L = np.diag(d) - A
    ev, U = np.linalg.eigh(L); lam = ev[1]; f = U[:, 1]; f = f / np.linalg.norm(f)
    m = G.number_of_edges(); S = float(d @ f); d_eff = float(d @ (f * f)); A2 = A @ A
    edges = [(i, j) for i in range(n) for j in range(i + 1, n) if A[i, j] > 0]
    T = sum(A2[a, b] * (f[a] - f[b]) ** 2 for a, b in edges)
    S_agg = lam * d_eff - T
    E = lam * (d_eff - lam - S ** 2 / m)
    Required = lam * (lam + S ** 2 / m - d_eff)
    gap = S_agg + E
    dmin = float(d.min())
    return dict(n=n, lam=lam, d_eff=d_eff, S2m=S ** 2 / m, T=T, S_agg=S_agg, E=E, Required=Required,
                gap=gap, regular=(d.max() == d.min()), dmin=dmin, lam_over_deff=lam / d_eff)


def corpus():
    out = []; rng = np.random.default_rng(0)
    def deg2dense(nn, q, s):
        H = nx.gnp_random_graph(nn - 1, q, seed=s); H.add_node(nn - 1)
        H.add_edge(nn - 1, 0); H.add_edge(nn - 1, 1); return H
    def twin(N, dd):
        K = nx.complete_graph(N); a, b = N, N + 1
        for x in (a, b):
            for w in range(dd): K.add_edge(x, w)
        K.add_node(N + 2); K.add_edge(N + 2, a); K.add_edge(N + 2, b); return K
    for nn in [30, 50, 80, 120]:
        for q in [0.3, 0.5, 0.7, 0.9]: out.append((f"deg2d{nn}_{q}", deg2dense(nn, q, int(rng.integers(1e9)))))
    for N in [30, 50, 80, 120]:
        for dd in [2, 3, 4]: out.append((f"twin{N}_{dd}", twin(N, dd)))
    for nn in [20, 40, 60]:
        for r in [int(0.5 * nn), nn - 4]:
            if 3 <= r <= nn - 1 and (r * nn) % 2 == 0: out.append((f"rr{nn}_{r}", nx.random_regular_graph(r, nn, seed=1)))
    for nn in [12, 20, 30]: out.append((f"K{nn}", nx.complete_graph(nn)))
    for nn in [30, 50]:
        for kd in [1, 5, 12]:
            K = nx.complete_graph(nn); E = list(K.edges()); rng.shuffle(E); rem = 0
            for e in E:
                if rem >= kd: break
                if K.degree(e[0]) > 2 and K.degree(e[1]) > 2: K.remove_edge(*e); rem += 1
            out.append((f"K{nn}-{rem}", K))
    # sparse (E>=0, for contrast)
    for nn in [25, 40]:
        for q in [0.2, 0.3]: out.append((f"gnp{nn}_{q}", nx.gnp_random_graph(nn, q, seed=int(rng.integers(1e9)))))
    return out


def classify(nm):
    if nm.startswith("twin") or nm.startswith("deg2d"): return "TYPE A (vertex bottleneck)"
    if nm.startswith("rr") or nm.startswith("K") and "-" not in nm: return "regular"
    if nm.startswith("K") and "-" in nm: return "near-complete irregular"
    return "other"


def main():
    data = [(nm, q) for nm, G in corpus() for q in [quant(G)] if q is not None]

    print("=" * 92)
    print("KEY IDENTITY: E = -Required  (E<0 <=> Required>0 = REGIME ii). Verify.")
    print("=" * 92)
    err = max(abs(q['E'] + q['Required']) for _, q in data)
    print(f"  max|E + Required| = {err:.2e}  => E = -Required EXACTLY")
    print(f"  => the aggregate-slack dichotomy E>=0/E<0 IS the regime i/ii split (Required<=0 / >0).")

    Eneg = [(nm, q) for nm, q in data if q['E'] < -1e-9]
    Epos = [(nm, q) for nm, q in data if q['E'] >= -1e-9]
    print(f"\n  E<0 (regime ii): {len(Eneg)}/{len(data)}; E>=0 (regime i, aggregate proves): {len(Epos)}")

    print("\n" + "=" * 92)
    print("TASK 2 — asymptotics in E<0: S_agg, -E(=Required), ratio, gap")
    print("=" * 92)
    print(f"  {'graph':12s} {'S_agg':>8} {'-E=Req':>8} {'ratio':>8} {'gap':>8} {'λ/d_eff':>8} {'class':>12}")
    for nm, q in sorted(Eneg, key=lambda x: x[1]['gap'])[:16]:
        r = q['S_agg'] / (-q['E']) if q['E'] < -1e-9 else float('inf')
        print(f"  {nm:12s} {q['S_agg']:8.3f} {-q['E']:8.3f} {r:8.3f} {q['gap']:8.4f} {q['lam_over_deff']:8.3f} "
              f"{classify(nm).split()[0]:>12}")

    print("\n" + "=" * 92)
    print("TASK 3 — structure of E<0: lam/d_eff (>=? 1 means lam close to/above d_eff)")
    print("=" * 92)
    lo_neg = [q['lam_over_deff'] for _, q in Eneg]
    lo_pos = [q['lam_over_deff'] for _, q in Epos]
    print(f"  E<0: λ/d_eff range [{min(lo_neg):.3f},{max(lo_neg):.3f}] mean {np.mean(lo_neg):.3f}")
    print(f"  E>=0: λ/d_eff range [{min(lo_pos):.3f},{max(lo_pos):.3f}] mean {np.mean(lo_pos):.3f}")
    print("  (E<0 => lam+S^2/m>d_eff => lam relatively large; dense/bottleneck)")

    print("\n" + "=" * 92)
    print("TASK 4 — hard-band lemma S_agg >= -E (=gap>=0 in regime ii): holds?")
    print("=" * 92)
    hb = sum(1 for _, q in Eneg if q['S_agg'] >= -q['E'] - 1e-9)
    print(f"  S_agg >= -E in E<0 band: {hb}/{len(Eneg)} (= gap>=0, circular but confined to regime ii)")

    print("\n" + "=" * 92)
    print("TASK 5 — COVERAGE of E<0 by regular / TYPE A / TYPE B / other")
    print("=" * 92)
    from collections import Counter
    cls = Counter(classify(nm) for nm, _ in Eneg)
    for k, v in cls.items(): print(f"  {k:30s}: {v}")
    # near-complete irregular: is it TYPE A-like (low-deg vertex)? check dmin
    print(f"\n  near-complete irregular E<0: do they have a low-degree bottleneck?")
    for nm, q in Eneg:
        if "K" in nm and "-" in nm:
            print(f"    {nm}: dmin={q['dmin']:.0f} n={q['n']} (dmin close to n-1 => NOT a low-deg bottleneck; near-regular)")
    print("\n  regular E<0 -> proven by interlacing (triEnergy_le_RHS_regular).")
    print("  TYPE A E<0 (deg2d/twin) -> extremality program (gap/eff>=1/3).")

    print("\n" + "=" * 92)
    print("SUMMARY")
    print("=" * 92)
    print(f"  E=-Required EXACT => E<0 band = REGIME ii. Coverage: "
          f"regular {cls.get('regular',0)} (proven), TYPE A {cls.get('TYPE A (vertex bottleneck)',0)} (extremality), "
          f"near-complete {cls.get('near-complete irregular',0)}.")


if __name__ == "__main__":
    main()
