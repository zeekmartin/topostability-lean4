"""
Analyze the ~6% local Poincare failures: vertices c with energy_c > lam2 * mass_c, where
energy_c = Dirichlet energy of f on G[N(c)] (apex form), mass_c = sum_{v in N(c)} f_v^2.
Aggregate T = sum_c energy_c <= lam2 * fDf = sum_c lam2*mass_c holds 100%; characterize the
per-vertex failures, quantify excess vs surplus, and test hub-flatness / direct bounds.
Run: python conjecture_B_poincare_6pct.py
"""
import numpy as np
import networkx as nx


def apex_data(G):
    nodes = list(G.nodes()); n = len(nodes); idx = {v: i for i, v in enumerate(nodes)}
    L = nx.laplacian_matrix(G, nodelist=nodes).toarray().astype(float)
    d = L.diagonal(); A = np.diag(d) - L
    ev, V = np.linalg.eigh(L); l2 = ev[1]; f = V[:, 1] / np.linalg.norm(V[:, 1])
    # per-apex energy and mass
    rows = []
    for c in range(n):
        Nc = np.flatnonzero(A[c] > 0.5)
        if len(Nc) == 0:
            continue
        mass = float(np.sum(f[Nc] ** 2))
        # Dirichlet energy of f on induced subgraph G[N(c)]
        energy = 0.0
        for ii in range(len(Nc)):
            a = Nc[ii]
            for jj in range(ii + 1, len(Nc)):
                b = Nc[jj]
                if A[a, b] > 0.5:
                    energy += (f[a] - f[b]) ** 2
        fmax2 = float(np.max(f[Nc] ** 2)) if len(Nc) else 0.0
        rows.append(dict(c=c, deg=d[c], fc2=f[c] ** 2, mass=mass, energy=energy,
                         lam_mass=l2 * mass, dc=len(Nc), fmax2=fmax2,
                         excess=energy - l2 * mass))
    return dict(n=n, l2=l2, f=f, d=d, A=A, idx=idx, nodes=nodes, rows=rows)


def carriers(f, p=0.8):
    order = np.argsort(-(f * f)); cum = np.cumsum((f * f)[order])
    k = int(np.searchsorted(cum, p)) + 1
    return set(order[:k].tolist())


# builders
def deg2dense(n, q, s):
    r = np.random.default_rng(s); G = nx.gnp_random_graph(n - 1, q, seed=int(r.integers(0, 2**31)))
    G = nx.relabel_nodes(G, {i: i + 1 for i in range(n - 1)}); G.add_node(0)
    for bb in r.choice(range(1, n), size=2, replace=False):
        G.add_edge(0, int(bb))
    return G


def degk(n, q, k, s):
    r = np.random.default_rng(s); G = nx.gnp_random_graph(n - 1, q, seed=int(r.integers(0, 2**31)))
    G = nx.relabel_nodes(G, {i: i + 1 for i in range(n - 1)}); G.add_node(0)
    for bb in r.choice(range(1, n), size=min(k, n - 1), replace=False):
        G.add_edge(0, int(bb))
    return G


def corpus():
    out = []
    rng = np.random.default_rng(11)
    for _ in range(120):
        out.append(('gnp', nx.gnp_random_graph(int(rng.integers(8, 22)),
                    float(rng.uniform(0.3, 0.7)), seed=int(rng.integers(0, 2**31)))))
    for _ in range(120):
        out.append(('deg2dense', deg2dense(int(rng.integers(20, 70)),
                    float(rng.uniform(0.4, 0.8)), int(rng.integers(0, 2**31)))))
    for _ in range(80):
        out.append(('degk', degk(int(rng.integers(20, 70)), float(rng.uniform(0.4, 0.8)),
                    int(rng.integers(1, 5)), int(rng.integers(0, 2**31)))))
    for _ in range(60):
        out.append(('lollipop', nx.lollipop_graph(int(rng.integers(8, 40)),
                    int(rng.integers(3, 18)))))
    for _ in range(40):
        out.append(('ws', nx.watts_strogatz_graph(int(rng.integers(15, 30)), 4,
                    0.3, seed=int(rng.integers(0, 2**31)))))
    return out


def main():
    print("Building corpus and per-apex Poincare data...")
    allrows = []           # (graph_id, row dict + aux)
    ratios = []            # surplus/excess per graph
    agg_holds = 0; ngr = 0
    fail_deg = []; ok_deg = []; fail_fc2 = []; ok_fc2 = []
    fail_adj_carrier = 0; fail_total = 0
    hubflat_C = []         # excess_c / (d_c * fmax2)  for failing vertices
    for gid, (fam, G) in enumerate(corpus()):
        if G.number_of_nodes() < 4 or not nx.is_connected(G):
            continue
        D = apex_data(G)
        if not D['rows']:
            continue
        ngr += 1
        l2 = D['l2']; f = D['f']; A = D['A']
        C = carriers(f)
        T = sum(r['energy'] for r in D['rows'])
        lamfDf = sum(r['lam_mass'] for r in D['rows'])
        if T <= lamfDf + 1e-9 * max(1.0, lamfDf):
            agg_holds += 1
        F = [r for r in D['rows'] if r['excess'] > 1e-12]
        nonF = [r for r in D['rows'] if r['excess'] <= 1e-12]
        tot_excess = sum(r['excess'] for r in F)
        tot_surplus = sum(-r['excess'] for r in nonF)
        if tot_excess > 1e-12:
            ratios.append(tot_surplus / tot_excess)
        for r in F:
            fail_deg.append(r['deg']); fail_fc2.append(r['fc2']); fail_total += 1
            # adjacent to a carrier?
            Nc = np.flatnonzero(A[r['c']] > 0.5)
            if any(int(u) in C for u in Nc):
                fail_adj_carrier += 1
            if r['dc'] * r['fmax2'] > 1e-15:
                hubflat_C.append(r['excess'] / (r['dc'] * r['fmax2']))
        for r in nonF:
            ok_deg.append(r['deg']); ok_fc2.append(r['fc2'])

    print(f"graphs: {ngr}; aggregate T<=lam2*fDf holds: {agg_holds}/{ngr} "
          f"({100*agg_holds/ngr:.1f}%)")
    nverts = fail_total + len(ok_deg)
    print(f"\n1. FAILING vertices F = {{energy_c > lam2*mass_c}}: {fail_total}/{nverts} "
          f"({100*fail_total/nverts:.1f}%)")

    print("\n2. CHARACTERIZE F:")
    fd = np.array(fail_deg); od = np.array(ok_deg)
    print(f"  degree: F median={np.median(fd):.1f} mean={fd.mean():.1f} | "
          f"not-F median={np.median(od):.1f} mean={od.mean():.1f}")
    ff = np.array(fail_fc2); of = np.array(ok_fc2)
    print(f"  f_c^2:  F median={np.median(ff):.4f} | not-F median={np.median(of):.4f} "
          f"(failing vertices high-f? {'YES' if np.median(ff)>np.median(of) else 'no'})")
    print(f"  adjacent to a carrier: {fail_adj_carrier}/{fail_total} "
          f"({100*fail_adj_carrier/fail_total:.1f}%)")

    print("\n3. EXCESS vs SURPLUS (aggregate cancellation):")
    rr = np.array(ratios)
    print(f"  Total_surplus/Total_excess: min={rr.min():.2f} median={np.median(rr):.2f} "
          f"(>1 for {100*np.mean(rr>1):.1f}%)")
    print(f"  MIN ratio across all graphs = {rr.min():.3f} (must be >1 for aggregate to hold)")

    print("\n4. HUB-FLATNESS bound on excess: excess_c <= C * d_c * f_max_neighbor^2 ?")
    hc = np.array(hubflat_C)
    print(f"  excess_c/(d_c*fmax2): median={np.median(hc):.4f} max={hc.max():.4f} "
          f"p95={np.percentile(hc,95):.4f}")
    print(f"  => universal C ~ {hc.max():.3f} (excess_c <= {hc.max():.3f}*d_c*fmax2 on all F)")


if __name__ == "__main__":
    main()
