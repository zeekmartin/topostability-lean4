"""
Conjecture B — FACTORIZATION of the open core (C4).

(C4)   sum_{ab} |d_a-d_b| f_h (f_l - f_h)  <=  l2 (delta - l2 + 1 - S^2/m)
where f = unit Fiedler, h/l = higher/lower-degree endpoints, S = sum d_v f_v.

KEY EXACT IDENTITY (Lemma D, eigenequation L_G f = l2 f), verified ~1e-14:

  LHS(C4) = W - l2 (fDf - delta),   W := sum_{ab} (min(d_a,d_b) - delta) (f_a-f_b)^2

(W is a NONNEGATIVE degree-weighted Dirichlet form; weight = min-endpoint-degree
minus delta.)  Hence (C4) is EQUIVALENT to the clean form

  (C4'')   W  <=  l2 (fDf - l2 + 1 - S^2/m)  =: R''.

This script tests the candidate decomposition lemmas A..H, measures slack
(tightness), assesses universality on tight + broad graph sets, and identifies
which lemma is the LOCK and which chain closes (C4'').

Run:  python conjecture_B_decomposition_explore.py
"""
import numpy as np
import networkx as nx
import counterexample_search as ce

TOL = 1e-9


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
    S = float(d @ f); fDf = float((d * f * f).sum()); fAf = float(f @ A @ f)
    lamA = float(np.linalg.eigvalsh(A)[-1])
    dbar = 2.0 * m / n; sig2 = float(np.mean((d - dbar) ** 2))

    # core sums
    LHS = 0.0; W = 0.0; E_grad = 0.0; cs_a = 0.0; G_sq = 0.0; mustar = 0.0
    for u, v in edges:
        i, j = idx[u], idx[v]
        gap = abs(d[i] - d[j]); dl = min(d[i], d[j]); w = dl - delta
        h, lo = (i, j) if d[i] >= d[j] else (j, i)
        LHS += gap * f[h] * (f[lo] - f[h])
        W += w * (f[i] - f[j]) ** 2
        E_grad += gap * (f[i] - f[j]) ** 2
        cs_a += gap * f[h] ** 2
        G_sq += gap * f[lo] ** 2                  # for Lemma G (complete-square)
        mustar = max(mustar, w)

    R_C4 = l2 * (delta - l2 + 1.0 - S * S / m)
    Rpp = l2 * (fDf - l2 + 1.0 - S * S / m)       # R'' (= RHS of DEG')

    # additive overlap (Lemma C)
    Bmat = np.zeros((n, m))
    for e, (u, v) in enumerate(edges):
        Bmat[idx[u], e] = 1.0; Bmat[idx[v], e] = 1.0
    LT = nx.laplacian_matrix(T).toarray().astype(float)
    psiT = np.linalg.eigh(LT)[1][:, 1]
    P_U = Bmat.T @ np.linalg.pinv(Bmat @ Bmat.T) @ Bmat   # proj onto range(B^T)
    overlap2 = float(np.linalg.norm(P_U @ psiT) ** 2)

    return dict(
        n=n, m=m, delta=delta, Delta=Delta, l2=l2, l2T=l2T, Q=l2 / l2T,
        S=S, fDf=fDf, fAf=fAf, lamA=lamA, sig2=sig2,
        LHS=LHS, W=W, E_grad=E_grad, cs_a=cs_a, G_sq=G_sq, mustar=mustar,
        R_C4=R_C4, Rpp=Rpp, overlap2=overlap2,
        D2_err=abs(LHS - (W - l2 * (fDf - delta))),
        regular=(Delta == delta),
    )


def tight_graphs():
    out = []
    def add(nm, G):
        if G.number_of_nodes() >= 3 and nx.is_connected(G):
            out.append((nm, G))
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


def broad_graphs(target=2500):
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


def lemmas(r):
    """Return dict of (name -> (holds, slack)) for each candidate lemma/chain.
    slack = RHS - LHS (>=0 means holds); also tightness ratio where useful."""
    l2,delta,Delta=r["l2"],r["delta"],r["Delta"]; m=r["m"]; S=r["S"]
    fDf=r["fDf"]; W=r["W"]; Eg=r["E_grad"]; Rpp=r["Rpp"]; R_C4=r["R_C4"]
    out={}
    # the target, both forms (must agree)
    out["C4 (LHS<=R_C4)"]=(r["LHS"]<=R_C4+1e-7, R_C4-r["LHS"])
    out["C4'' (W<=R'')"]=(W<=Rpp+1e-7, Rpp-W)
    # ---- candidate UPPER bounds on W ----
    # A: W <= (Delta-delta)*l2   (crude max weight)
    A_ub=(Delta-delta)*l2
    out["A: W<=(D-d)l2"]=(W<=A_ub+1e-7, A_ub-W)
    # A-chain: (Delta-delta)*l2 <= R''  (i.e. closes C4'')
    out["A-chain: (D-d)<=fDf-l2+1-S2/m"]=((Delta-delta)<=fDf-l2+1-S*S/m+1e-7,
                                          (fDf-l2+1-S*S/m)-(Delta-delta))
    # H: W <= mustar*l2  (refined max edge-min-degree weight)
    H_ub=r["mustar"]*l2
    out["H: W<=mu*.l2"]=(W<=H_ub+1e-7, H_ub-W)
    # H-chain: mustar <= fDf-l2+1-S2/m  (closes C4'')
    out["H-chain: mu*<=fDf-l2+1-S2/m"]=(r["mustar"]<=fDf-l2+1-S*S/m+1e-7,
                                        (fDf-l2+1-S*S/m)-r["mustar"])
    # ---- RHS lower-bound / correction lemmas ----
    # B: S^2 <= n*sig2  (Cauchy-Schwarz; n*sig2 = sum (d-dbar)^2)
    nsig=r["n"]*r["sig2"]
    out["B: S^2<=n·sig2"]=(S*S<=nsig+1e-7, nsig-S*S)
    # F: S^2/m <= fDf - delta  (enables dropping S^2/m via fDf>=delta+S^2/m)
    out["F: S^2/m<=fDf-delta"]=(S*S/m<=fDf-delta+1e-7, (fDf-delta)-S*S/m)
    # E: +1 essential? test W <= l2(fDf-l2-S2/m) (drop +1) -> expect FAIL
    out["E: W<=l2(fDf-l2-S2/m) [no +1]"]=(W<=l2*(fDf-l2-S*S/m)+1e-7,
                                          l2*(fDf-l2-S*S/m)-W)
    # G: LHS <= (1/4) sum|d_a-d_b| f_l^2  (complete-square per edge)
    out["G: LHS<=(1/4)sum|dd|f_l^2"]=(r["LHS"]<=0.25*r["G_sq"]+1e-7, 0.25*r["G_sq"]-r["LHS"])
    return out


def main():
    tight=[x for x in (analyse(G) for _,G in tight_graphs()) if x]
    broad=[x for x in (analyse(G) for _,G in broad_graphs()) if x]
    print(f"tight={len(tight)} broad={len(broad)}")
    print(f"D2 identity max err: tight {max(r['D2_err'] for r in tight):.2e}  "
          f"broad {max(r['D2_err'] for r in broad):.2e}")

    names=list(lemmas(tight[0]).keys())
    print(f"\n{'lemma / chain':36s} {'tight pass':>11s} {'broad pass':>11s} "
          f"{'min slack(broad)':>16s} {'median tight slack':>18s}")
    rows={'tight':tight,'broad':broad}
    lock=None
    for nm in names:
        t_pass=sum(1 for r in tight if lemmas(r)[nm][0]); t_n=len(tight)
        b_pass=sum(1 for r in broad if lemmas(r)[nm][0]); b_n=len(broad)
        b_minslack=min(lemmas(r)[nm][1] for r in broad)
        t_slacks=sorted(lemmas(r)[nm][1] for r in tight)
        t_med=t_slacks[len(t_slacks)//2]
        print(f"{nm:36s} {t_pass:>5d}/{t_n:<5d} {b_pass:>5d}/{b_n:<5d} "
              f"{b_minslack:>16.4f} {t_med:>18.4f}")

    # tightness of the target C4'' (how close W to R'')
    ratios=sorted((r["W"]/r["Rpp"] if r["Rpp"]>1e-9 else 0.0) for r in tight if r["W"]>1e-9)
    print(f"\nC4'' tightness W/R'' (tight graphs): max={ratios[-1]:.4f} "
          f"median={ratios[len(ratios)//2]:.4f}")
    # additive overlap (Lemma C)
    ov=sorted(r["overlap2"] for r in tight)
    print(f"Lemma C additive overlap ||P_U psi_T||^2: min={ov[0]:.4f} (tight)")
    # ANTICORRELATION diagnostic: how much smaller is W than the crude (D-d)l2 bound?
    gain=sorted(r["W"]/((r["Delta"]-r["delta"])*r["l2"]) for r in broad
                if (r["Delta"]-r["delta"])>0 and r["l2"]>1e-9)
    print(f"\nLOCK diagnostic: W / ((D-d)*l2)  (1=crude tight, <<1=anticorrelation)")
    print(f"  broad: min={gain[0]:.4f} median={gain[len(gain)//2]:.4f} max={gain[-1]:.4f}")
    # the one broad failure of C4'' (if any)
    fails=[r for r in broad if not (r["W"]<=r["Rpp"]+1e-7)]
    if fails:
        r=fails[0]
        print(f"\nC4'' broad failures: {len(fails)}; worst slack={min(r['Rpp']-r['W'] for r in fails):.5f} "
              f"(n={r['n']} Q={r['Q']:.3f} regular={r['regular']}) -- check if numerical/bipartite")
    main.tight=tight; main.broad=broad


if __name__=="__main__":
    main()
