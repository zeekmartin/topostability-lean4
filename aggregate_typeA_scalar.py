"""
Scalar TYPE A partition inequality: maxt_port*dir_port + maxt_core*dir_core <= RHS (ordered, dir=2*D).
RHS = 2lam(2degQuad - lam - degLin^2/mE). Measure all quantities; split terms; Fiedler D_port; block D_core.
Run: python aggregate_typeA_scalar.py
"""
import numpy as np
import networkx as nx


def split_ports(d):
    n = len(d); order = np.argsort(d); sd = d[order]
    gaps = [(sd[i + 1] - sd[i], i) for i in range(n - 1)]; gap, idx = max(gaps)
    return set(order[:idx + 1].tolist()) if (gap >= 2 and idx < n - 1) else set()


def analyze(G):
    G = nx.convert_node_labels_to_integers(G); n = G.number_of_nodes()
    if not nx.is_connected(G): return None
    A = nx.to_numpy_array(G); d = A.sum(1); L = np.diag(d) - A; A2 = A @ A
    ev, U = np.linalg.eigh(L); lam = ev[1]; f = U[:, 1]; f = f / np.linalg.norm(f)
    mE = G.number_of_edges(); degQuad = float(d @ (f * f)); degLin = float(d @ f)
    S2m = degLin ** 2 / mE
    required = 2 * lam * (lam + S2m - degQuad)
    if required <= 1e-9: return None
    RHS = 2 * lam * (2 * degQuad - lam - S2m)
    P = split_ports(d); Hset = set(range(n)) - P
    if len(Hset) < 2 or len(P) == 0: return None
    edges = [(i, j) for i in range(n) for j in range(i + 1, n) if A[i, j] > 0]
    Dport = Dcore = 0.0
    for a, b in edges:
        g2 = (f[a] - f[b]) ** 2; inP = (a in P) + (b in P)
        if inP == 0: Dcore += g2
        elif inP == 1: Dport += g2
    maxt_port = max((A2[a, b] for a, b in edges if (a in P) != (b in P)), default=0.0)
    maxt_core = max((A2[a, b] for a, b in edges if a not in P and b not in P), default=0.0)
    portMass = float(sum(d[p] * f[p] ** 2 for p in P))
    portF2 = float(sum(f[p] ** 2 for p in P))
    # core block
    Hl = sorted(Hset); Ah = A[np.ix_(Hl, Hl)]; dh = Ah.sum(1); Lh = np.diag(dh) - Ah
    evh = np.linalg.eigvalsh(Lh); gamma = evh[1] if len(evh) > 1 else 0.0; lmaxH = evh[-1]
    fH = np.array([f[v] for v in Hl]); meanH = fH.mean(); flat = float(((fH - meanH) ** 2).sum())
    src = float(sum((sum(f[u] for u in P if A[v, u] > 0)) ** 2 for v in Hl))
    portTerm = 2 * maxt_port * Dport; coreTerm = 2 * maxt_core * Dcore   # ordered
    block_Dcore = src / (gamma - lam) ** 2 if gamma > lam else float('inf')
    return dict(n=n, lam=lam, degQuad=degQuad, S2m=S2m, RHS=RHS, required=required,
                maxt_port=maxt_port, maxt_core=maxt_core, Dport=Dport, Dcore=Dcore,
                portTerm=portTerm, coreTerm=coreTerm, ratio=(portTerm + coreTerm) / RHS,
                pratio=portTerm / RHS, cratio=coreTerm / RHS,
                portMass=portMass, portF2=portF2, gamma=gamma, lmaxH=lmaxH, flat=flat, src=src,
                block_Dcore=block_Dcore, block_ok=(Dcore <= block_Dcore + 1e-9),
                block_tight=Dcore / block_Dcore if block_Dcore not in (0, float('inf')) else 0.0,
                lmax_Dcore=lmaxH * flat)


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
        for q in [0.2, 0.3, 0.4, 0.6, 0.85]: out.append((f"deg2d{nn}_{q}", d2(nn, q, 7)))
    for N in [30, 50, 80]:
        for dd in [2, 3, 4]: out.append((f"twin{N}_{dd}", twin(N, dd)))
    return out


def main():
    data = [(nm, q) for nm, G in corpus() for q in [analyze(G)] if q is not None]

    print("=" * 100)
    print("TASK 1/2 — measured quantities; split portTerm/coreTerm (ratio to RHS)")
    print("=" * 100)
    print(f"  {'graph':12s} {'ratio':>6} {'pTerm/R':>8} {'cTerm/R':>8} {'mtPort':>6} {'mtCore':>6} "
          f"{'Dport':>7} {'Dcore':>7} {'γ/λ':>6}")
    for nm, q in sorted(data, key=lambda x: -x[1]['ratio'])[:14]:
        print(f"  {nm:12s} {q['ratio']:6.3f} {q['pratio']:8.3f} {q['cratio']:8.3f} {q['maxt_port']:6.0f} "
              f"{q['maxt_core']:6.0f} {q['Dport']:7.4f} {q['Dcore']:7.4f} {q['gamma']/q['lam']:6.1f}")
    worst = max(data, key=lambda x: x[1]['ratio'])
    print(f"\n  WORST ratio {worst[1]['ratio']:.4f} at {worst[0]}: "
          f"portTerm/RHS={worst[1]['pratio']:.3f}, coreTerm/RHS={worst[1]['cratio']:.3f} "
          f"=> {'CORE' if worst[1]['cratio']>worst[1]['pratio'] else 'PORT'} term dominates")

    print("\n" + "=" * 100)
    print("TASK 4 — block flatness: D_core <= src²/(γ-λ)²? and lmaxH·flat? tightness")
    print("=" * 100)
    bok = sum(1 for _, q in data if q['block_ok'])
    print(f"  D_core <= src²/(γ-λ)²: {bok}/{len(data)}")
    print(f"  {'graph':12s} {'Dcore':>8} {'src²/(γ-λ)²':>12} {'lmaxH·flat':>11} {'block tight':>11}")
    for nm, q in sorted(data, key=lambda x: -x[1]['cratio'])[:8]:
        print(f"  {nm:12s} {q['Dcore']:8.4f} {q['block_Dcore']:12.4f} {q['lmax_Dcore']:11.4f} {q['block_tight']:11.4f}")

    print("\n" + "=" * 100)
    print("TASK 5 — sufficient condition: maxt_core*lmaxH*src²/(γ-λ)² + portTerm <= RHS ?")
    print("=" * 100)
    suff = 0; suff_tot = 0
    for nm, q in data:
        if q['gamma'] <= q['lam']: continue
        suff_tot += 1
        coreBound = 2 * q['maxt_core'] * q['lmaxH'] * q['src'] / (q['gamma'] - q['lam']) ** 2
        if q['portTerm'] + coreBound <= q['RHS'] + 1e-9: suff += 1
    print(f"  portTerm + maxt_core·(2·lmaxH·src²/(γ-λ)²) <= RHS : {suff}/{suff_tot}")
    # also test coreTerm directly bounded by lmaxH route
    suff2 = sum(1 for _, q in data if q['gamma'] > q['lam'] and
                q['portTerm'] + 2 * q['maxt_core'] * q['lmax_Dcore'] <= q['RHS'] + 1e-9)
    print(f"  portTerm + maxt_core·(2·lmaxH·flat) <= RHS (uses flat directly): {suff2}/{suff_tot}")

    print("\n" + "=" * 100)
    print("SUMMARY")
    print("=" * 100)
    print(f"  scalar holds {sum(1 for _,q in data if q['ratio']<=1+1e-9)}/{len(data)} (max {worst[1]['ratio']:.3f})")
    print(f"  worst dominated by {'CORE' if worst[1]['cratio']>worst[1]['pratio'] else 'PORT'} term")
    print(f"  block flatness D_core<=src²/(γ-λ)²: {bok}/{len(data)}")


if __name__ == "__main__":
    main()
