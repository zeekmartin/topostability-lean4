"""
Conjecture B v4 — localized attack on the LOCK (C4'').

  W := Σ_{ab}(min(d_a,d_b)-δ)(f_a-f_b)²   ≤   λ₂(fᵀDf - λ₂ + 1 - S²/m) =: R''

f = unit Fiedler (L_G f = λ₂f, f⟂1), δ=min deg, S=Σ d_v f_v, m=|E|.

Tests three structural approaches to the anticorrelation:
  A1  edge weight (min-deg) vs gradient anticorrelation; partition E_hub/E_cut.
  A2  local eigenequation: D_a := Σ_{b~a}(f_a-f_b)² = (2λ₂-d_a)f_a² + (Af²)_a;
      'flat at hubs' = corr(deg, f²) and corr(deg, local gradient) < 0;
      exact decomposition W = Σ_v (d_v-δ)·D_v^+  (D_v^+ = energy to STRICTLY
      higher-degree neighbours).
  A3  nodal domains V+={f>0}, V-={f<0}: are cut (sign-crossing) edges low
      min-degree (small weight) but high gradient? measure W-share of cut edges.
Plus candidate closing bounds for W.

Run:  python conjecture_B_proof_v4_explore.py
"""
import numpy as np
import networkx as nx
import counterexample_search as ce

TOL = 1e-9


def pear(x, y):
    x = np.asarray(x, float); y = np.asarray(y, float)
    if len(x) < 3 or np.std(x) < 1e-12 or np.std(y) < 1e-12:
        return np.nan
    return float(np.corrcoef(x, y)[0, 1])


def analyse(G):
    nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}
    edges = list(G.edges()); n, m = len(nodes), len(edges)
    L = nx.laplacian_matrix(G, nodelist=nodes).toarray().astype(float)
    D = np.diag(L.diagonal()); A = D - L; d = L.diagonal().copy()
    T = ce.triangle_graph(G)
    if T.number_of_nodes() < 2 or not nx.is_connected(T):
        return None
    l2T = ce.lambda2(T)
    if l2T <= TOL:
        return None
    ev, V = np.linalg.eigh(L); l2 = float(ev[1]); f = V[:, 1] / np.linalg.norm(V[:, 1])
    delta = float(d.min()); Delta = float(d.max())
    S = float(d @ f); fDf = float((d * f * f).sum())
    Rpp = l2 * (fDf - l2 + 1.0 - S * S / m)
    f2 = f * f

    # per-edge weight & gradient
    w_e = []; g_e = []; minc = []; cut = []
    W = 0.0
    for u, v in edges:
        i, j = idx[u], idx[v]
        w = min(d[i], d[j]) - delta; g = (f[i] - f[j]) ** 2
        w_e.append(w); g_e.append(g); minc.append(min(d[i], d[j]))
        cut.append(f[i] * f[j] < 0)        # sign-crossing edge
        W += w * g
    w_e = np.array(w_e); g_e = np.array(g_e); cut = np.array(cut)

    # --- A1: anticorrelation + gradient-quartile share of W ---
    anti = pear(w_e, g_e)
    # share of W from the top-gradient-quartile edges (expect small if anticorr)
    if m >= 4:
        thr = np.quantile(g_e, 0.75)
        hi = g_e >= thr
        W_higrad = float((w_e[hi] * g_e[hi]).sum())
        share_higrad = W_higrad / W if W > 1e-12 else np.nan
    else:
        share_higrad = np.nan

    # --- A2: local eigenequation ---
    Af2 = A @ f2
    D_local = (2 * l2 - d) * f2 + Af2          # D_a = Σ_{b~a}(f_a-f_b)^2
    D_direct = np.array([sum((f[idx[u]] - f[idx[b]]) ** 2 for b in G[u]) for u in nodes])
    locid_err = float(np.max(np.abs(D_local - D_direct)))
    # flat-at-hubs correlations (over vertices)
    cf2 = pear(d, f2)                          # high deg -> small f^2 ? (expect <0)
    cDloc = pear(d, D_direct)                  # high deg -> small local energy ?
    cDper = pear(d, D_direct / d)              # per-edge avg gradient at v vs deg
    # exact decomposition W = Σ_v (d_v-δ) D_v^+  (energy to strictly-higher nbrs; ties split half)
    Wdecomp = 0.0
    for u in nodes:
        i = idx[u]
        s = 0.0
        for b in G[u]:
            j = idx[b]
            if d[j] > d[i]:
                s += (f[i] - f[j]) ** 2
            elif d[j] == d[i]:
                s += 0.5 * (f[i] - f[j]) ** 2
        Wdecomp += (d[i] - delta) * s
    Wdecomp_err = abs(Wdecomp - W)

    # --- A3: nodal domains ---
    if cut.any() and (~cut).any():
        mincut = float(np.mean(np.array(minc)[cut]))
        minint = float(np.mean(np.array(minc)[~cut]))
        gcut = float(np.mean(g_e[cut])); gint = float(np.mean(g_e[~cut]))
        W_cut = float((w_e[cut] * g_e[cut]).sum()); share_cut = W_cut / W if W > 1e-12 else np.nan
    else:
        mincut = minint = gcut = gint = share_cut = np.nan
    nndom = "2" if (cut.any()) else "1?"

    # --- candidate closing bounds for W (W <= ... <= R'') ---
    cand1 = W <= l2 * (fDf - delta) + 1e-7          # W <= λ₂(fᵀDf-δ)
    cand1_closes = l2 * (fDf - delta) <= Rpp + 1e-7  # and that <= R'' ?
    # half-of-loose bound: Σ(d_v-δ)D_v = 2λ₂(fDf-δ)+E_disc ; W is the '+restricted' part
    SdD = float(((d - delta) * D_direct).sum())
    Wfrac_of_SdD = W / SdD if SdD > 1e-12 else np.nan   # expect ~0.3-0.5 (restriction+anticorr)

    return dict(n=n, m=m, delta=delta, Delta=Delta, l2=l2, Q=l2 / l2T,
                W=W, Rpp=Rpp, target=(W <= Rpp + 1e-7),
                anti=anti, share_higrad=share_higrad,
                locid_err=locid_err, cf2=cf2, cDloc=cDloc, cDper=cDper,
                Wdecomp_err=Wdecomp_err,
                mincut=mincut, minint=minint, gcut=gcut, gint=gint, share_cut=share_cut,
                cand1=cand1, cand1_closes=cand1_closes, Wfrac_of_SdD=Wfrac_of_SdD,
                regular=(Delta == delta))


def tight_graphs():
    out = []
    def add(nm, G):
        if G.number_of_nodes() >= 3 and nx.is_connected(G): out.append((nm, G))
    for n in range(6, 11):
        K = nx.complete_graph(n); E = list(K.edges())
        for k in (1, 2, 3):
            G = nx.Graph(); G.add_nodes_from(range(n)); G.add_edges_from(E[k:]); add(f"K{n}-{k}e", G)
        G = nx.complete_graph(n)
        for j in range(2, n): G.remove_edge(0, j)
        add(f"K{n}-star", G)
    for parts in ([4,3],[5,3],[4,4,1],[5,2,2],[3,3,2],[6,3],[4,3,2],[5,4]):
        add(f"Km{parts}", nx.complete_multipartite_graph(*parts))
    for n in (7,8,9):
        G=nx.complete_graph(n-1); G.add_edge(n-1,0); add(f"K{n-1}+p",G)
        G2=nx.complete_graph(n-1); G2.add_edges_from([(n-1,0),(n-1,1)]); add(f"K{n-1}+2",G2)
    rng=np.random.default_rng(7); seen=set(); cand=[]
    for _ in range(4000):
        n=int(rng.integers(7,11)); p=float(rng.uniform(0.6,0.95))
        G=nx.gnp_random_graph(n,p,seed=int(rng.integers(0,2**31)))
        if not nx.is_connected(G) or ce.is_regular(G): continue
        T=ce.triangle_graph(G)
        if T.number_of_nodes()<2 or not nx.is_connected(T): continue
        l2T=ce.lambda2(T)
        if l2T<=TOL: continue
        Qv=ce.lambda2(G)/l2T
        key=(n,G.number_of_edges(),nx.weisfeiler_lehman_graph_hash(G,iterations=3))
        if key in seen: continue
        seen.add(key); cand.append((Qv,G))
    cand.sort(key=lambda x:x[0])
    for i,(Qv,G) in enumerate(cand[:30]): add(f"rt{i}",G)
    return out


def broad_graphs(target=1800):
    out=[]; rng=np.random.default_rng(2024); seen=set()
    for n in range(6,13):
        K=nx.complete_graph(n); E=list(K.edges())
        for k in range(1,10):
            G=nx.Graph(); G.add_nodes_from(range(n)); G.add_edges_from(E[k:]); out.append((f"K{n}-{k}",G))
    while len(out)<target:
        n=int(rng.integers(6,14)); p=float(rng.uniform(0.45,0.97))
        G=nx.gnp_random_graph(n,p,seed=int(rng.integers(0,2**31)))
        if not nx.is_connected(G): continue
        key=(n,G.number_of_edges(),nx.weisfeiler_lehman_graph_hash(G,iterations=2))
        if key in seen: continue
        seen.add(key); out.append((f"r{n}",G))
    return out


def agg(rows, label):
    def mean(k):
        vals=[r[k] for r in rows if r[k]==r[k]]  # drop nan
        return float(np.mean(vals)) if vals else float('nan')
    def frac(k): return sum(1 for r in rows if r[k]) / len(rows)
    N=len(rows)
    print(f"\n=== {label}: {N} graphs ===")
    print(f"[target] W<=R''                         : {sum(1 for r in rows if r['target'])}/{N}")
    print(f"[A2] local identity max err             : {max(r['locid_err'] for r in rows):.2e}")
    print(f"[A2] W = Σ(d_v-δ)D_v^+ decomp max err    : {max(r['Wdecomp_err'] for r in rows):.2e}")
    print(f"[A1] anticorr(weight,gradient) mean      : {mean('anti'):+.3f}  "
          f"(frac<0: {sum(1 for r in rows if r['anti']==r['anti'] and r['anti']<0)/N:.2f})")
    print(f"[A1] W-share from top-gradient quartile  : {mean('share_higrad'):.3f}")
    print(f"[A2] corr(deg, f^2)   mean (flat-at-hubs): {mean('cf2'):+.3f}")
    print(f"[A2] corr(deg, D_v)   mean               : {mean('cDloc'):+.3f}")
    print(f"[A2] corr(deg, D_v/deg) mean             : {mean('cDper'):+.3f}")
    print(f"[A3] mean min-deg: cut={mean('mincut'):.2f} internal={mean('minint'):.2f}")
    print(f"[A3] mean gradient: cut={mean('gcut'):.4f} internal={mean('gint'):.4f}")
    print(f"[A3] W-share from sign-cut edges         : {mean('share_cut'):.3f}")
    print(f"[cand] W<=λ₂(fDf-δ)                       : {frac('cand1'):.2f}  "
          f"and that<=R'': {frac('cand1_closes'):.2f}")
    print(f"[cand] W / Σ(d_v-δ)D_v  mean             : {mean('Wfrac_of_SdD'):.3f}")


def main():
    tight=[x for x in (analyse(G) for _,G in tight_graphs()) if x]
    broad=[x for x in (analyse(G) for _,G in broad_graphs()) if x]
    agg(tight, "tightest irregular")
    agg(broad, "broad sweep")
    main.tight=tight; main.broad=broad


if __name__=="__main__":
    main()
