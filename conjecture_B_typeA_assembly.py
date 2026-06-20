"""
TASK 5: assembly. For arbitrary TYPE A G = H + v0 (v0~{a,b}), test whether the completion process
(add interior edges, then port-incident edges) keeps gap/eff >= 1/3 at EVERY step.

Also: at complete bulk K_N, scan port degrees (incl ASYMMETRIC d_a != d_b) and overlap; verify >=1/3.
Run: python conjecture_B_typeA_assembly.py
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
                fv0sq=float(f[idx[v0]]) ** 2)


def base_graph(N, da_nb, db_nb, seed, qbulk=0.5):
    """Bulk gnp(N,qbulk) + ports a~da_nb, b~db_nb (vertex sets), v0~{a,b}."""
    H = nx.gnp_random_graph(N, qbulk, seed=seed)
    if not nx.is_connected(H): return None
    G = nx.Graph(H); a, b, v0 = N, N + 1, N + 2
    for u in da_nb: G.add_edge(a, u)
    for u in db_nb: G.add_edge(b, u)
    G.add_node(v0); G.add_edge(v0, a); G.add_edge(v0, b)
    return G, a, b, v0, N


def main():
    rng = np.random.default_rng(0)

    print("=" * 88)
    print("STEP-BY-STEP COMPLETION: track gap/eff at every edge addition; ever < 1/3 ?")
    print("=" * 88)
    overall_min = 1e9; total_steps = 0; dips = 0
    for trial in range(12):
        N = int(rng.integers(20, 36))
        # random starting TYPE A: ports a,b ~ 2 random bulk vertices
        pa = tuple(rng.choice(N, 2, replace=False)); pb = tuple(rng.choice(N, 2, replace=False))
        res = base_graph(N, pa, pb, int(rng.integers(1e9)), qbulk=float(rng.uniform(0.3, 0.6)))
        if res is None: continue
        G, a, b, v0, N = res
        r0 = measure(G, a, b, v0)
        if r0 is None or r0['fv0sq'] <= 0.3: continue
        traj = [r0['goe']]
        cur = G.copy()
        # Step 1: complete interior (edges among bulk 0..N-1 not present)
        missing_int = [(u, v) for u in range(N) for v in range(u + 1, N) if not cur.has_edge(u, v)]
        rng.shuffle(missing_int)
        for e in missing_int:
            cur.add_edge(*e)
            r = measure(cur, a, b, v0)
            if r and r['fv0sq'] > 0.3:
                traj.append(r['goe'])
        # Step 2: complete port-incident (a/b to all bulk)
        for u in range(N):
            for port in (a, b):
                if not cur.has_edge(port, u):
                    cur.add_edge(port, u)
                    r = measure(cur, a, b, v0)
                    if r and r['fv0sq'] > 0.3:
                        traj.append(r['goe'])
        tmin = min(traj); overall_min = min(overall_min, tmin)
        total_steps += len(traj); dips += sum(1 for g in traj if g < 1 / 3 - 1e-6)
        print(f"  trial {trial:2d}: N={N} start g={traj[0]:.3f} -> end g={traj[-1]:.3f}  "
              f"min over path={tmin:.4f}  {'DIP<1/3!' if tmin < 1/3-1e-6 else 'ok>=1/3'}")
    print(f"\n  overall min gap/eff over all completion paths = {overall_min:.4f}")
    print(f"  steps below 1/3: {dips}/{total_steps}")

    print("\n" + "=" * 88)
    print("COMPLETE BULK K_N: scan port degrees (incl ASYMMETRIC da != db) + overlap; min gap/eff")
    print("=" * 88)
    def kn_ports(N, da_nb, db_nb):
        G = nx.complete_graph(N); a, b, v0 = N, N + 1, N + 2
        for u in da_nb: G.add_edge(a, u)
        for u in db_nb: G.add_edge(b, u)
        G.add_node(v0); G.add_edge(v0, a); G.add_edge(v0, b)
        return measure(G, a, b, v0)
    N = 60; mn = 1e9; arg = None
    print(f"  {'da':>3} {'db':>3} {'overlap':>7} {'gap/eff':>8}")
    for da in [2, 3, 4, 6]:
        for db in [2, 3, 4, 6]:
            if db < da: continue
            for s in [0, min(da, db)]:
                common = list(range(s))
                aonly = list(range(s, da)); bonly = list(range(da, da + db - s))
                r = kn_ports(N, common + aonly, common + bonly)
                if r and r['fv0sq'] > 0.3:
                    if r['goe'] < mn: mn = r['goe']; arg = (da, db, s)
                    if da <= 4 and db <= 4:
                        print(f"  {da:3d} {db:3d} {s:7d} {r['goe']:8.4f}")
    print(f"  MIN over (da,db,overlap) at K60: {mn:.4f} at (da,db,s)={arg}  "
          f"(>=1/3? {mn >= 1/3-1e-6}; twins d=2 s=2 -> 1/3 in limit)")

    print("\n" + "=" * 88)
    print("STEP 1 check — interior completion LOWERS gap/eff (eff fixed)?")
    print("=" * 88)
    # take a sparse-interior TYPE A, complete interior, confirm g decreases monotonically-ish
    res = base_graph(30, (0, 1), (0, 1), 7, qbulk=0.4)
    G, a, b, v0, N = res
    cur = G.copy(); gs = []
    missing = [(u, v) for u in range(N) for v in range(u + 1, N) if not cur.has_edge(u, v)]
    rng.shuffle(missing)
    r = measure(cur, a, b, v0); gs.append(r['goe'])
    for e in missing:
        cur.add_edge(*e); r = measure(cur, a, b, v0)
        if r and r['fv0sq'] > 0.3: gs.append(r['goe'])
    print(f"  twin ports, interior gnp(.4)->K_N: g start={gs[0]:.4f} end={gs[-1]:.4f} "
          f"(end=complete-bulk twin); decreasing fraction={np.mean(np.diff(gs)<=1e-6):.2f}; "
          f"min={min(gs):.4f}")

    print("\n" + "=" * 88)
    print("VERDICT")
    print("=" * 88)
    print(f"  completion paths min gap/eff = {overall_min:.4f} ({'>=1/3, no dip' if overall_min>=1/3-1e-3 else 'DIP'}); "
          f"K_N port-config min = {mn:.4f}. Step 2 preserves gap/eff>=1/3: "
          f"{overall_min>=1/3-1e-3 and mn>=1/3-1e-6}")


if __name__ == "__main__":
    main()
