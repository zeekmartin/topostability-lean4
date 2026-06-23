"""
Lean bridge for aggregate_triangle_poincare_typeA: T <= 2*lam*degQuad.
Edge split: E_port (>=1 endpoint in ports P), E_core (both in core H), E_bot (rest).
Bounds: T_port <= (delta-1) D_port [triCount<=min-1 on ports]; T_core <= Dmax_H * D_core.
Sufficient condition (a): (delta-1)D_port + Dmax_H * D_core <= 2 lam degQuad.
TASK 0: sparse-core (gamma<=lam) => T/(2lam degQuad) tiny (trivial).
Run: python aggregate_typeA_lean_bridge.py
"""
import numpy as np
import networkx as nx


def split_core_ports(d):
    n = len(d); order = np.argsort(d); sd = d[order]
    gaps = [(sd[i + 1] - sd[i], i) for i in range(n - 1)]
    gap, idx = max(gaps)
    if gap >= 2 and idx < n - 1:
        return set(order[:idx + 1].tolist())
    return set()


def analyze(G):
    G = nx.convert_node_labels_to_integers(G); n = G.number_of_nodes()
    if not nx.is_connected(G): return None
    A = nx.to_numpy_array(G); d = A.sum(1); L = np.diag(d) - A
    ev, U = np.linalg.eigh(L); lam = ev[1]; f = U[:, 1]; f = f / np.linalg.norm(f)
    d_eff = float(d @ (f * f)); A2 = A @ A
    P = split_core_ports(d); Hset = set(range(n)) - P
    if len(Hset) < 2 or len(P) == 0: return None
    edges = [(i, j) for i in range(n) for j in range(i + 1, n) if A[i, j] > 0]
    T_port = T_core = T_bot = D_port = D_core = D_bot = 0.0
    for a, b in edges:
        g2 = (f[a] - f[b]) ** 2; t = A2[a, b]
        inP = (a in P) + (b in P)
        if inP == 0: T_core += t * g2; D_core += g2
        elif inP == 2: T_bot += t * g2; D_bot += g2
        else: T_port += t * g2; D_port += g2
    T = T_port + T_core + T_bot
    RHS = 2 * lam * d_eff
    delta = max((d[p] for p in P), default=0.0)               # max port degree
    Dmax_H = max((d[v] for v in Hset), default=0.0)            # max core degree
    maxt_core = max((A2[a, b] for a, b in edges if a not in P and b not in P), default=0.0)
    portMass = float(sum(d[p] * f[p] ** 2 for p in P))
    # core gap
    Hl = sorted(Hset); Ah = A[np.ix_(Hl, Hl)]; dh = Ah.sum(1); Lh = np.diag(dh) - Ah
    evh = np.linalg.eigvalsh(Lh); gamma = evh[1] if len(evh) > 1 else 0.0
    # conditions
    cond_a = (delta - 1) * D_port + Dmax_H * D_core            # <= RHS ?
    cond_aprime = (delta - 1) * D_port + maxt_core * D_core    # <= RHS ? (tighter, maxt)
    return dict(n=n, lam=lam, gamma=gamma, gamma_le_lam=(gamma <= lam),
                T=T, T_port=T_port, T_core=T_core, T_bot=T_bot, RHS=RHS,
                ratio=T / RHS, delta=delta, Dmax_H=Dmax_H, maxt_core=maxt_core,
                D_port=D_port, D_core=D_core, portMass=portMass,
                cond_a=cond_a / RHS, cond_aprime=cond_aprime / RHS,
                Tport_bound_ok=(T_port <= (delta - 1) * D_port + 1e-9),
                Tcore_bound_ok=(T_core <= Dmax_H * D_core + 1e-9))


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
        for q in [0.03, 0.06, 0.1, 0.2, 0.4, 0.6, 0.85]: out.append((f"deg2d{nn}_{q}", d2(nn, q, 7)))
    for N in [30, 50, 80]:
        for dd in [2, 3, 4]: out.append((f"twin{N}_{dd}", twin(N, dd)))
    return out


def main():
    data = [(nm, q) for nm, G in corpus() for q in [analyze(G)] if q is not None]
    dense = [(nm, q) for nm, q in data if not q['gamma_le_lam']]
    sparse = [(nm, q) for nm, q in data if q['gamma_le_lam']]
    print(f"  {len(data)} TYPE A: {len(dense)} dense-core (γ>λ), {len(sparse)} sparse-core (γ≤λ)")

    print("\n" + "=" * 92)
    print("TASK 0 — sparse-core (γ≤λ): is T/(2λ·degQuad) tiny (trivially closed)?")
    print("=" * 92)
    if sparse:
        mx = max(q['ratio'] for _, q in sparse)
        print(f"  sparse-core max T/RHS = {mx:.5f}  (<=0.01? {mx<=0.01})")
        for nm, q in sorted(sparse, key=lambda x: -x[1]['ratio'])[:6]:
            print(f"    {nm:12s} T/RHS={q['ratio']:.5f} γ/λ={q['gamma']/q['lam']:.2f}")
    else:
        print("  (none in corpus)")

    print("\n" + "=" * 92)
    print("TASK 2/3 — per-class bounds hold? T_port<=(δ-1)D_port; T_core<=Δ_H·D_core")
    print("=" * 92)
    pb = sum(1 for _, q in dense if q['Tport_bound_ok'])
    cb = sum(1 for _, q in dense if q['Tcore_bound_ok'])
    print(f"  T_port <= (δ-1)·D_port : {pb}/{len(dense)}")
    print(f"  T_core <= Δ_H·D_core   : {cb}/{len(dense)}")

    print("\n" + "=" * 92)
    print("TASK 5/6 — sufficient condition on dense-core (γ>λ); ratio of bound to RHS (<=1 proves)")
    print("=" * 92)
    ca = sum(1 for _, q in dense if q['cond_a'] <= 1 + 1e-9)
    cap = sum(1 for _, q in dense if q['cond_aprime'] <= 1 + 1e-9)
    print(f"  (a)  (δ-1)D_port+Δ_H·D_core <= 2λdegQuad : {ca}/{len(dense)}  (max {max(q['cond_a'] for _,q in dense):.3f})")
    print(f"  (a') (δ-1)D_port+maxt·D_core <= 2λdegQuad: {cap}/{len(dense)}  (max {max(q['cond_aprime'] for _,q in dense):.3f})")
    print(f"  {'graph':12s} {'T/RHS':>7} {'cond_a':>8} {'cond_a-prime':>12} {'δ':>4} {'Δ_H':>5} {'maxt':>5}")
    for nm, q in sorted(dense, key=lambda x: -x[1]['cond_a'])[:12]:
        print(f"  {nm:12s} {q['ratio']:7.3f} {q['cond_a']:8.3f} {q['cond_aprime']:12.3f} "
              f"{q['delta']:4.0f} {q['Dmax_H']:5.0f} {q['maxt_core']:5.0f}")

    print("\n" + "=" * 92)
    print("SUMMARY")
    print("=" * 92)
    print(f"  TASK0 sparse-core trivial (T/RHS<=0.01): {sum(1 for _,q in sparse if q['ratio']<=0.01)}/{len(sparse)}")
    print(f"  per-class bounds: T_port {pb}/{len(dense)}, T_core {cb}/{len(dense)}")
    print(f"  cond_a proves {ca}/{len(dense)}, cond_a' proves {cap}/{len(dense)} dense-core cases")


if __name__ == "__main__":
    main()
