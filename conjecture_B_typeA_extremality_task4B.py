"""
TASK 4B: target 3*gap - eff >= 0 (sharp at d=2 twin-port K_N: 3*(2/3)-2=0).

4B.2 quotient closed form: 3*gap(d)-eff(d) = eff(d)*(3 g(d) - 1) >= 0 (TASK1, g>=1/3).
4B.4 the real question: is 3*gap-eff minimized by complete bulk (i.e. >=0 for non-complete H)?
     Test eff monotonicity (resolvent: removing edge raises eff?) and 3*gap-eff under deletion.
Run: python conjecture_B_typeA_extremality_task4B.py
"""
import numpy as np
import networkx as nx


def measure(G, a, b, v0):
    nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}
    A = nx.to_numpy_array(G, nodelist=nodes); dg = A.sum(1); L = np.diag(dg) - A
    ev, U = np.linalg.eigh(L); lam = ev[1]; f = U[:, 1]; f = f / np.linalg.norm(f)
    if f[idx[v0]] < 0: f = -f
    m = G.number_of_edges(); S = float(dg @ f)
    Gs = sum((f[idx[u]] + f[idx[v]]) ** 2 for u, v in G.edges())
    B2 = sum((min(dg[idx[u]], dg[idx[v]]) - 1) * (f[idx[u]] - f[idx[v]]) ** 2 for u, v in G.edges())
    gap = lam * (Gs - S ** 2 / m) - B2
    Gc = G.copy(); Gc.remove_node(v0); Gcn = list(Gc.nodes())
    if not nx.is_connected(Gc): return None
    LH = nx.laplacian_matrix(Gc, nodelist=Gcn).toarray().astype(float)
    mu, phi = np.linalg.eigh(LH); gamma = float(mu[1])
    if gamma - lam <= 1e-9: return None
    inv = 1.0 / (mu[1:] - lam); R = (phi[:, 1:] * inv) @ phi[:, 1:].T
    ia, ib = Gcn.index(a), Gcn.index(b)
    eff = float(R[ia, ia] + R[ib, ib] - 2 * R[ia, ib])
    return dict(lam=lam, gamma=gamma, gap=gap, eff=eff, goe=gap / eff,
                target=3 * gap - eff, fv0sq=float(f[idx[v0]]) ** 2)


def twin(H, a_nb=(0, 1)):
    H = nx.convert_node_labels_to_integers(H); N = H.number_of_nodes()
    G = nx.Graph(H); a, b, v0 = N, N + 1, N + 2
    for u in (a, b):
        for w in a_nb: G.add_edge(u, w)
    G.add_node(v0); G.add_edge(v0, a); G.add_edge(v0, b)
    return G, a, b, v0


def main():
    print("=" * 84)
    print("TASK 4B.2 — quotient closed form: 3*gap(d)-eff(d) = eff(d)*(3 g(d)-1) >= 0")
    print("=" * 84)
    for d in [2, 3, 4, 5]:
        lam = 0.5 * (d + 3 - np.sqrt(d * d - 2 * d + 9))
        w = np.sqrt(d * d - 2 * d + 9)
        g = (3 * d * d + d * w - 6 * d - 9 * w + 27) / (2 * d * d - 4 * d + 18)
        eff = 2 / (d - lam)
        print(f"  d={d}: g={g:.4f} eff={eff:.4f} 3*gap-eff=eff*(3g-1)={eff*(3*g-1):.4f} "
              f"{'(=0 EQUALITY)' if d==2 else '(>0)'}")
    print("  => for complete bulk, 3*gap-eff >= 0 with equality at d=2 (this is TASK1 restated).")

    print("\n" + "=" * 84)
    print("TASK 4B.4a — eff monotonicity: does removing a bulk edge RAISE eff? (vs K_N eff~2)")
    print("=" * 84)
    rng = np.random.default_rng(0)
    print(f"  {'bulk':22s} {'lam':>7} {'eff':>8} {'eff>=2?':>8} {'gap':>8} {'3gap-eff':>9} {'>=0?':>5}")
    for N in [40, 60]:
        for kf in [0.0, 0.05, 0.15, 0.3]:
            H = nx.complete_graph(N); E = list(H.edges())
            for di in rng.choice(len(E), int(kf * len(E)), replace=False):
                e = E[di]
                if 0 in e or 1 in e: continue
                H.remove_edge(*e)
            if not nx.is_connected(H): continue
            G, a, b, v0 = twin(H); r = measure(G, a, b, v0)
            if r and r['fv0sq'] > 0.3:
                print(f"  K{N}-{int(kf*100)}%{'':10s} {r['lam']:7.4f} {r['eff']:8.4f} "
                      f"{str(r['eff']>=2-1e-3):>8} {r['gap']:8.4f} {r['target']:9.4f} "
                      f"{str(r['target']>=-1e-6):>5}")

    print("\n" + "=" * 84)
    print("TASK 4B.4b — MONOTONE deletion: delete bulk edges one-by-one from K_N, track 3*gap-eff")
    print("=" * 84)
    N = 40; H = nx.complete_graph(N)
    nonport = [(u, v) for u, v in H.edges() if 0 not in (u, v) and 1 not in (u, v)]
    rng.shuffle(nonport)
    G, a, b, v0 = twin(H); base = measure(G, a, b, v0)
    print(f"  start K{N}: eff={base['eff']:.4f} gap={base['gap']:.4f} 3gap-eff={base['target']:.4f}")
    targs = [base['target']]; effs = [base['eff']]
    cur = H.copy()
    for k, e in enumerate(nonport[:120]):
        cur.remove_edge(*e)
        if not nx.is_connected(cur): cur.add_edge(*e); continue
        G, a, b, v0 = twin(cur); r = measure(G, a, b, v0)
        if r is None or r['fv0sq'] <= 0.3: continue
        targs.append(r['target']); effs.append(r['eff'])
        if (k + 1) % 20 == 0:
            print(f"  after {k+1} deletions: eff={r['eff']:.4f} 3gap-eff={r['target']:.4f}")
    targs = np.array(targs); effs = np.array(effs)
    # is eff monotone non-decreasing? is 3gap-eff monotone non-decreasing (K_N = min)?
    eff_mono = np.mean(np.diff(effs) >= -1e-6)
    targ_mono = np.mean(np.diff(targs) >= -1e-6)
    print(f"\n  eff: start={effs[0]:.4f} end={effs[-1]:.4f}; fraction steps eff non-decreasing = {eff_mono:.3f}")
    print(f"  3gap-eff: start(K_N)={targs[0]:.4f} min={targs.min():.4f} end={targs[-1]:.4f}; "
          f"fraction steps non-decreasing = {targ_mono:.3f}")
    print(f"  K_N is the MIN of 3gap-eff along deletion path: {targs[0] <= targs.min()+1e-6}")
    print(f"  3gap-eff >= 0 throughout: {all(targs >= -1e-6)}")

    print("\n" + "=" * 84)
    print("TASK 4B.4 verdict — is eff>=2 (resolvent monotonicity) and 3gap-eff minimized at K_N?")
    print("=" * 84)
    print(f"  eff >= eff(K_N): {'YES (resolvent monotonicity holds)' if effs.min() >= effs[0]-1e-3 else 'NO'}")
    print(f"  3gap-eff minimized at complete bulk: "
          f"{'YES' if targs[0] <= targs.min()+1e-6 else 'NO (interior min!)'}")


if __name__ == "__main__":
    main()
