"""
TASK 4A.5: identify the rigidity variable. Correlate excess = g - 1/3 with 7 candidates.
Ports: degree-2 twins a,b~{0,1}, v0~{a,b}. Bulk H varied. Genuine TYPE A only.
Run: python conjecture_B_typeA_rigidity_variable.py
"""
import numpy as np
import networkx as nx


def cheeger(H):
    """Crude Cheeger via Fiedler sweep (lower bound proxy)."""
    Hn = list(H.nodes()); N = len(Hn)
    L = nx.laplacian_matrix(H, nodelist=Hn).toarray().astype(float)
    ev, U = np.linalg.eigh(L); f = U[:, 1]
    order = np.argsort(f); best = 1e9
    A = nx.to_numpy_array(H, nodelist=Hn); deg = A.sum(1); vol = deg.sum()
    Sset = set()
    cut = 0.0; volS = 0.0
    for k in range(N - 1):
        v = order[k]; Sset.add(v)
        # update cut and volume incrementally
        cut += deg[v] - 2 * sum(A[v, u] for u in Sset if u != v)
        volS += deg[v]
        denom = min(volS, vol - volS)
        if denom > 0:
            best = min(best, cut / denom)
    return best


def analyze(H, p=(0, 1), q=(0, 1)):
    H = nx.convert_node_labels_to_integers(H); N = H.number_of_nodes()
    if not nx.is_connected(H): return None
    G = nx.Graph(H); a, b, v0 = N, N + 1, N + 2
    G.add_node(a); G.add_node(b)
    for u in p: G.add_edge(a, u)
    for u in q: G.add_edge(b, u)
    G.add_node(v0); G.add_edge(v0, a); G.add_edge(v0, b)
    nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}
    A = nx.to_numpy_array(G, nodelist=nodes); dg = A.sum(1); L = np.diag(dg) - A
    ev, U = np.linalg.eigh(L); lam = ev[1]; f = U[:, 1]; f = f / np.linalg.norm(f)
    if f[idx[v0]] < 0: f = -f
    m = G.number_of_edges(); S = float(dg @ f)
    Gs = sum((f[idx[u]] + f[idx[v]]) ** 2 for u, v in G.edges())
    B2 = sum((min(dg[idx[u]], dg[idx[v]]) - 1) * (f[idx[u]] - f[idx[v]]) ** 2 for u, v in G.edges())
    gap = lam * (Gs - S ** 2 / m) - B2
    # core = G - v0 (contains a,b); resolvent / gamma on the CORE
    Gc = G.copy(); Gc.remove_node(v0); Gcn = list(Gc.nodes())
    if not nx.is_connected(Gc): return None
    LH = nx.laplacian_matrix(Gc, nodelist=Gcn).toarray().astype(float)
    mu, phi = np.linalg.eigh(LH); gamma = float(mu[1]); lam3 = float(mu[2])
    if gamma - lam <= 1e-9: return None
    inv = 1.0 / (mu[1:] - lam); R = (phi[:, 1:] * inv) @ phi[:, 1:].T
    ia, ib = Gcn.index(a), Gcn.index(b)
    eff = float(R[ia, ia] + R[ib, ib] - 2 * R[ia, ib])
    Hn = list(H.nodes())
    fv0 = float(f[idx[v0]])
    if fv0 ** 2 <= 0.3: return None
    g = gap / eff
    # candidate rigidity variables (bulk H)
    dH = LH.diagonal()
    degvar = float(np.var(dH))
    cond = cheeger(H)
    sgr = (lam3 - gamma) / gamma if gamma > 1e-9 else 0.0
    missing = N * (N - 1) // 2 - H.number_of_edges()
    portset = set(p) | set(q)
    local = list(portset) + [w for u in portset for w in H.neighbors(u)]
    local = list(set(local))
    locirr = float(np.var([dH[w] for w in local])) if len(local) > 1 else 0.0
    da = dH[Hn.index(p[0])] if p[0] in Hn else dH[0]   # bulk degree of a port neighbor 0
    # port_degree_deficit: bulk degree of the port-attachment vertices 0,1
    pdd = (N - 1) - np.mean([dH[w] for w in portset])
    # eff_resist_ratio: eff(H)/eff(K_N) where eff(K_N) for twins = 2 (limit) ~ 2/(2-lam)*... use complete ref
    effKN = 2.0 / (2 - 1.0)   # complete-bulk twin reference eff -> 2 (lam=1)
    err = eff / effKN
    return dict(N=N, lam=lam, gamma=gamma, g=g, excess=g - 1 / 3,
                degvar=degvar, cond=cond, sgr=sgr, missing=missing, locirr=locirr,
                pdd=pdd, err=err, eff=eff, gap=gap)


def main():
    rng = np.random.default_rng(0); data = []
    def add(H, p=(0, 1), q=(0, 1)):
        try:
            r = analyze(H, p, q)
            if r: data.append(r)
        except Exception:
            pass
    for N in [30, 45, 60]:
        add(nx.complete_graph(N))
        for kf in [0.03, 0.08, 0.15, 0.25, 0.4]:
            H = nx.complete_graph(N); E = list(H.edges())
            for di in rng.choice(len(E), int(kf * len(E)), replace=False):
                e = E[di]
                if 0 in e or 1 in e: continue
                H.remove_edge(*e)
            add(H)
        for qd in [0.5, 0.7, 0.85]:
            add(nx.gnp_random_graph(N, qd, seed=int(rng.integers(1e9))))
        for r in [int(0.5 * N), N - 6]:
            if (r * N) % 2: r += 1
            if 3 <= r <= N - 1: add(nx.random_regular_graph(r, N, seed=1))
        # adversarial: ports' neighbors 0,1 low degree
        for keep in [4, 8, 14]:
            H = nx.complete_graph(N)
            for u in (0, 1):
                for w in range(2 + keep, N):
                    if H.has_edge(u, w): H.remove_edge(u, w)
            add(H)

    print(f"  {len(data)} TYPE A samples; excess=g-1/3 in "
          f"[{min(d['excess'] for d in data):.4f}, {max(d['excess'] for d in data):.4f}]")
    print("\n" + "=" * 78)
    print("CORRELATION of excess (=g-1/3) with 7 rigidity candidates")
    print("=" * 78)
    ex = np.array([d['excess'] for d in data])
    cands = {
        '1. degree_variance': np.array([d['degvar'] for d in data]),
        '2. conductance(Cheeger)': np.array([d['cond'] for d in data]),
        '3. spectral_gap_ratio': np.array([d['sgr'] for d in data]),
        '4. missing_edges': np.array([d['missing'] for d in data]),
        '5. local_irregularity': np.array([d['locirr'] for d in data]),
        '6. port_degree_deficit': np.array([d['pdd'] for d in data]),
        '7. eff_resist_ratio': np.array([d['err'] for d in data]),
    }
    ranked = sorted(cands.items(), key=lambda kv: -abs(np.corrcoef(kv[1], ex)[0, 1]))
    for nm, x in ranked:
        r = np.corrcoef(x, ex)[0, 1]
        print(f"  corr(excess, {nm:26s}) = {r:+.3f}")
    best_nm, best_x = ranked[0]
    print(f"\n  BEST predictor: {best_nm} (r={np.corrcoef(best_x, ex)[0,1]:+.3f})")

    print("\n" + "=" * 78)
    print("Test g >= 1/3 + c*Phi for best predictor Phi (and combos): is excess >= c*Phi?")
    print("=" * 78)
    # for each candidate, the largest c with excess >= c*Phi for all (i.e. min excess/Phi over Phi>0)
    for nm, x in ranked[:4]:
        mask = x > 1e-9
        if mask.sum() < 3: continue
        ratios = ex[mask] / x[mask]
        c = ratios.min()
        print(f"  Phi={nm:26s}: min(excess/Phi)={c:+.4f}  "
              f"(c>0 => g>=1/3+c*Phi holds: {c > -1e-9})")
    # eff_resist_ratio special: excess vs (err-1) ? larger eff(H) (sparser) => larger excess?
    print("\n  eff_resist_ratio detail (err=eff(H)/2): excess vs err")
    err = cands['7. eff_resist_ratio']
    print(f"    corr(excess, err) = {np.corrcoef(err, ex)[0,1]:+.3f}; "
          f"excess>0 always: {all(ex > -1e-9)}; err range [{err.min():.3f},{err.max():.3f}]")

    print("\n" + "=" * 78)
    print("SUMMARY")
    print("=" * 78)
    print("  Report best Phi; whether excess>=c*Phi gives a provable lower bound; honest if none clean.")


if __name__ == "__main__":
    main()
