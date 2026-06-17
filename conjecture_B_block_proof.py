"""
Attempt to PROVE the block principle: Required>0 => lam2(G[B]) >= c*lam2(G), B=high-degree set.
TRACK A: lam2(G[B]) vs internal density / min-degree bound 2*delta_B - |B| + 2.
TRACK B: lam2(G[B]) vs delta_B, kappa_B, density_B.
TRACK C: rigorous resolvent/Poincare-on-block: (L_B - l2 I) f_B = forcing (boundary), and
         ||f_B - mean||^2 <= ||forcing||^2 / (gamma - l2)^2.
TRACK D: is T monotone in fAf?
Corpus = the 1962 Required>0 graphs (deg2+dense sweep, lollipops, 1949 random, seed 7).
Run: python conjecture_B_block_proof.py
"""
import numpy as np
import networkx as nx


# ---------- core ----------
def analyze(G):
    nodes = list(G.nodes()); n = len(nodes)
    L = nx.laplacian_matrix(G, nodelist=nodes).toarray().astype(float)
    d = L.diagonal(); A = np.diag(d) - L; m = G.number_of_edges()
    ev, V = np.linalg.eigh(L); l2 = ev[1]; f = V[:, 1] / np.linalg.norm(V[:, 1])
    fDf = float((d * f * f).sum()); S = float(d @ f); fAf = float(f @ A @ f)
    A2 = A @ A; W = A * A2
    T = float(f @ (np.diag(W @ np.ones(n)) - W) @ f)
    Required = l2 * (l2 + S * S / m - fDf)
    return dict(G=G, nodes=nodes, idx={v: i for i, v in enumerate(nodes)}, n=n, m=m,
                L=L, d=d, A=A, l2=l2, f=f, fDf=fDf, S=S, fAf=fAf, T=T,
                RHS=l2 * (2 * fDf - l2 - S * S / m), Required=Required)


def block_highdeg(R):
    nodes, d, n = R['nodes'], R['d'], R['n']
    med = float(np.median(d))
    Bn = [nodes[i] for i in range(n) if d[i] >= med]
    H = R['G'].subgraph(Bn)
    comps = list(nx.connected_components(H))
    if not comps:
        return None
    cc = max(comps, key=len)
    if len(cc) < 2:
        return None
    return list(cc)


def block_stats(R, Bn, want_kappa=False):
    G, f, idx, l2 = R['G'], R['f'], R['idx'], R['l2']
    H = G.subgraph(Bn); b = len(Bn)
    LB = nx.laplacian_matrix(H, nodelist=Bn).toarray().astype(float)
    evB = np.linalg.eigvalsh(LB); gamma = evB[1]
    indeg = LB.diagonal()
    delta_B = float(indeg.min()); dens = 2 * H.number_of_edges() / (b * (b - 1))
    # TRACK C: forcing + Poincare
    fB = np.array([f[idx[v]] for v in Bn])
    Bset = set(Bn)
    forcing = np.array([sum(f[idx[u]] - f[idx[v]] for u in G[v] if u not in Bset)
                        for v in Bn])
    resid = float(np.linalg.norm(LB @ fB - l2 * fB - forcing))
    meanfB = fB.mean()
    dev = float(((fB - meanfB) ** 2).sum())
    fnorm = float((forcing ** 2).sum())
    bound = fnorm / (gamma - l2) ** 2 if gamma > l2 else float('inf')
    kappa = None
    if want_kappa and b <= 70:
        try:
            kappa = nx.node_connectivity(H)
        except Exception:
            kappa = None
    return dict(b=b, gamma=gamma, ratio=gamma / l2 if l2 > 1e-12 else None,
                delta_B=delta_B, dens=dens, mindeg_lb=2 * delta_B - b + 2,
                resid=resid, dev=dev, fnorm=fnorm, poincare_bound=bound,
                poincare_ratio=(dev / bound) if bound > 0 and np.isfinite(bound) else None,
                kappa=kappa)


# ---------- builders ----------
def deg2dense(n, q, seed):
    rng = np.random.default_rng(seed)
    G = nx.gnp_random_graph(n - 1, q, seed=int(rng.integers(0, 2**31)))
    G = nx.relabel_nodes(G, {i: i + 1 for i in range(n - 1)}); G.add_node(0)
    for b in rng.choice(range(1, n), size=2, replace=False):
        G.add_edge(0, int(b))
    return G


def degk_block(n, q, k, seed):
    rng = np.random.default_rng(seed)
    G = nx.gnp_random_graph(n - 1, q, seed=int(rng.integers(0, 2**31)))
    G = nx.relabel_nodes(G, {i: i + 1 for i in range(n - 1)}); G.add_node(0)
    for b in rng.choice(range(1, n), size=min(k, n - 1), replace=False):
        G.add_edge(0, int(b))
    return G


def two_cycles(Lc):
    G = nx.cycle_graph(Lc); G2 = nx.relabel_nodes(nx.cycle_graph(Lc),
                                                  {i: i + Lc for i in range(Lc)})
    G = nx.union(G, G2); G.add_edge(0, Lc); return G


def pathend_dense(n, q, plen, seed):
    rng = np.random.default_rng(seed)
    G = nx.gnp_random_graph(n, q, seed=int(rng.integers(0, 2**31)))
    attach = 0; nxt = n
    for _ in range(plen):
        G.add_edge(attach, nxt); attach = nxt; nxt += 1
    return G


def corpus():
    out = []
    for n in (50, 100, 200, 500, 1000):
        out.append(deg2dense(n, 0.65, 100 + n))
    for m in (10, 20, 50):
        for L in (3, 5, 10, 20):
            out.append(nx.lollipop_graph(m, L))
    rng = np.random.default_rng(7)
    for _ in range(900):
        s = int(rng.integers(0, 2**31)); n = int(rng.integers(20, 120))
        out.append(deg2dense(n, float(rng.uniform(0.3, 0.8)), s))
    for _ in range(700):
        s = int(rng.integers(0, 2**31)); n = int(rng.integers(20, 120))
        out.append(degk_block(n, float(rng.uniform(0.3, 0.8)), int(rng.integers(1, 5)), s))
    for _ in range(500):
        out.append(nx.lollipop_graph(int(rng.integers(6, 60)), int(rng.integers(2, 25))))
    for _ in range(500):
        s = int(rng.integers(0, 2**31)); n = int(rng.integers(8, 40))
        out.append(pathend_dense(n, float(rng.uniform(0.3, 0.8)), int(rng.integers(1, 12)), s))
    for _ in range(400):
        out.append(two_cycles(int(rng.integers(5, 40))))
    return out


def main():
    print("Building Required>0 corpus...")
    rows = []
    for G in corpus():
        if G.number_of_nodes() < 4 or not nx.is_connected(G):
            continue
        R = analyze(G)
        if R['Required'] <= 1e-9:
            continue
        Bn = block_highdeg(R)
        if Bn is None:
            rows.append(dict(R=R, bs=None)); continue
        # kappa is expensive: sample on the first ~60 small valid blocks only
        want_k = (len(Bn) <= 30) and (len([r for r in rows if r.get('bs')
                  and r['bs'].get('kappa') is not None]) < 60)
        rows.append(dict(R=R, bs=block_stats(R, Bn, want_kappa=want_k)))
    valid = [r for r in rows if r['bs'] is not None]
    N = len(rows); NV = len(valid)
    print(f"Required>0 graphs: {N}; with a valid high-degree block: {NV}\n")

    print("TARGET CHECK: ratio = lam2(G[B])/lam2(G) for B = {d_v >= median}")
    rr = np.array([r['bs']['ratio'] for r in valid])
    for c in (1.0, 1.5, 2.0, 3.0):
        print(f"  ratio >= {c}: {100*np.mean(rr>=c):5.1f}%")
    print(f"  min ratio = {rr.min():.3f}, median = {np.median(rr):.2f}")
    fail = [r for r in valid if r['bs']['ratio'] < 1.5]
    print(f"  graphs with ratio < 1.5 (target fragile): {len(fail)}")
    for r in fail[:5]:
        R = r['R']; bs = r['bs']
        print(f"     n={R['n']} lam2={R['l2']:.3f} Req={R['Required']:.4f} "
              f"ratio={bs['ratio']:.3f} |B|={bs['b']} dens_B={bs['dens']:.2f}")

    print("\nTRACK A/B: lam2(G[B]) vs internal density & min-degree bound 2*delta_B-|B|+2")
    g = np.array([r['bs']['gamma'] for r in valid])
    lb = np.array([r['bs']['mindeg_lb'] for r in valid])
    dens = np.array([r['bs']['dens'] for r in valid])
    print(f"  mindeg bound gamma >= 2*delta_B-|B|+2 holds: {100*np.mean(g>=lb-1e-9):.1f}%")
    pos = lb > 0
    print(f"  bound positive (delta_B>(|B|-2)/2) on {100*np.mean(pos):.1f}% of blocks")
    if pos.sum():
        l2arr = np.array([r['R']['l2'] for r in valid])
        print(f"  where positive: (2*delta_B-|B|+2) >= lam2(G) on "
              f"{100*np.mean(lb[pos]>=l2arr[pos]):.1f}%, "
              f">= 2*lam2(G) on {100*np.mean(lb[pos]>=2*l2arr[pos]):.1f}%")
    print(f"  corr(density_B, ratio) = {np.corrcoef(dens, rr)[0,1]:.3f}")
    kap = [(r['bs']['kappa'], r['bs']['delta_B'], r['bs']['gamma'])
           for r in valid if r['bs']['kappa'] is not None]
    if kap:
        ka = np.array([k for k, _, _ in kap]); de = np.array([d for _, d, _ in kap])
        ga = np.array([g for _, _, g in kap])
        print(f"  (|B|<=70 sample, n={len(kap)}) gamma>=kappa_B Fiedler-violations: "
              f"{int(np.sum(ga>ka+1e-6))} (Fiedler: lam2<=kappa, so gamma<=kappa expected); "
              f"median kappa_B/delta_B={np.median(ka/np.maximum(de,1)):.2f}")

    print("\nTRACK C: rigorous Poincare-on-block  ||f_B-mean||^2 <= ||forcing||^2/(gamma-l2)^2")
    res = np.array([r['bs']['resid'] for r in valid])
    print(f"  eigen-restriction residual ||(L_B-l2)f_B - forcing||: max={res.max():.2e} "
          f"(should be ~0 => forcing is exact)")
    havg = [r for r in valid if r['bs']['ratio'] > 1.0 and r['bs']['poincare_ratio'] is not None]
    pr = np.array([r['bs']['poincare_ratio'] for r in havg])
    print(f"  among ratio>1 (n={len(havg)}): Poincare bound holds (dev<=bound): "
          f"{100*np.mean(pr<=1+1e-6):.1f}%")
    print(f"     dev/bound: median={np.median(pr):.3f}, max={pr.max():.3f}, "
          f"95%ile={np.percentile(pr,95):.3f}")
    # uniformity implied: ||f_B-mean||^2 / massB  vs 1/(gamma-l2)^2 scale
    print("  => uniformity ||f_B-mean||^2 controlled by ||forcing||^2/(gamma-l2)^2 (O(1/gamma^2))")

    print("\nTRACK D: is T monotone in fAf?")
    Ts = np.array([r['R']['T'] for r in rows])
    fAf = np.array([r['R']['fAf'] for r in rows])
    l2s = np.array([r['R']['l2'] for r in rows])
    print(f"  corr(T, fAf) = {np.corrcoef(Ts, fAf)[0,1]:.3f}; "
          f"corr(T/lam2, fAf) = {np.corrcoef(Ts/l2s, fAf)[0,1]:.3f}")
    print(f"  corr(T, |fAf|) = {np.corrcoef(Ts, np.abs(fAf))[0,1]:.3f}  "
          f"(if no clean monotone link, T is set by triangles x gradient, not fAf)")


if __name__ == "__main__":
    main()
