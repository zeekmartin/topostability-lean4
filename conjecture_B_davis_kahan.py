"""
Davis-Kahan approach to close B:  f^T M f >= 0,  M = λ₂Q - L_t.
Mechanism: M's negative eigenvectors v_j are HIGH-FREQUENCY (high L-energy); the
Fiedler f=u_2 is the lowest mode, so ⟨u_2,v_j⟩ is small. DK makes this quantitative
via M ≈ M₀ = function of L.

Resolvent/DK identity (exact):  (ν_2 - μ_j)⟨u_2,v_j⟩ = -⟨u_2, P v_j⟩,  P=M-M₀,
ν_2 = M₀-eigenvalue at u_2.  ⇒ |⟨u_2,v_j⟩| ≤ ||P|| / |ν_2 - μ_j|.

TASK1: decompose neg v_j in L-eigenbasis (high/low-freq mass, |c_2|²).
TASK2: regular L_t=(d-1)L? build M₀=2d̄λ₂ I-(λ₂+d̄-1)L, ||P||, DK gap.
TASK3: closure: Σ|μ_j|·DK_bound(j) < pos_part ?
Run:  python conjecture_B_davis_kahan.py
"""
import numpy as np
import networkx as nx
import counterexample_search as ce


def tri_laplacian(G, nodes, idx):
    n = len(nodes); Lt = np.zeros((n, n))
    for u, v in G.edges():
        i, j = idx[u], idx[v]; t = len(set(G[u]) & set(G[v]))
        Lt[i, j] -= t; Lt[j, i] -= t; Lt[i, i] += t; Lt[j, j] += t
    return Lt


def corpus(maxn=9):
    seen = {}
    for tag, exh, G in ce._gen_graphs_hier(maxn):
        if G.number_of_nodes() < 3 or not nx.is_connected(G):
            continue
        T = ce.triangle_graph(G)
        if T.number_of_nodes() < 2 or not nx.is_connected(T):
            continue
        key = (G.number_of_nodes(), G.number_of_edges(),
               nx.weisfeiler_lehman_graph_hash(G, iterations=3))
        if key not in seen:
            seen[key] = G.copy()
    return list(seen.values())


def main():
    graphs = [G for G in corpus(9) if nx.is_connected(G)]
    print(f"corpus: {len(graphs)} connected distinct graphs")

    # ===== TASK 2 (regular identity first) =====
    print("\n===== TASK 2: is L_t = (d-1)L for regular graphs? =====")
    reg_ok = 0; reg_tot = 0; reg_resid = []
    for G in graphs:
        nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}; n = len(nodes)
        d = np.array([G.degree(u) for u in nodes], float)
        if d.std() > 1e-9:
            continue
        reg_tot += 1
        L = nx.laplacian_matrix(G, nodelist=nodes).toarray().astype(float)
        Lt = tri_laplacian(G, nodes, idx)
        dd = d[0]
        resid = np.linalg.norm(Lt - (dd - 1) * L)
        reg_resid.append(resid / max(np.linalg.norm(Lt), 1e-9))
        if resid < 1e-7:
            reg_ok += 1
    reg_resid = np.array(reg_resid)
    print(f"  regular graphs: {reg_tot};  L_t=(d-1)L EXACTLY on {reg_ok}/{reg_tot}")
    print(f"  relative residual ||L_t-(d-1)L||/||L_t||: median={np.median(reg_resid):.3f} "
          f"max={reg_resid.max():.3f}  => holds only for complete graphs (clique nbhds)")

    # ===== TASK 1 + 2(irregular M₀,P) + 3 =====
    sample = graphs[:1500]
    hf_all = []; c2_all = []; mu_all = []
    Pnorms = []; dk_close = 0; dk_tot = 0
    neg_act = []; pos_act = []; neg_dk = []
    for G in sample:
        nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}; n = len(nodes)
        L = nx.laplacian_matrix(G, nodelist=nodes).toarray().astype(float)
        d = L.diagonal(); A = np.diag(d) - L; dbar = d.mean()
        ev, V = np.linalg.eigh(L); l2 = ev[1]
        if l2 < 1e-6:
            continue
        u2 = V[:, 1] / np.linalg.norm(V[:, 1])
        Q = np.diag(d) + A; Lt = tri_laplacian(G, nodes, idx); M = l2 * Q - Lt
        ones = np.ones(n); P0 = np.eye(n) - np.outer(ones, ones) / n
        w, U = np.linalg.eigh(P0 @ M @ P0); drop = int(np.argmax(np.abs(U.T @ ones)))
        medlam = np.median(ev)
        # regular-approx M₀ = 2 d̄ λ₂ I - (λ₂+d̄-1) L  (function of L; eigvecs=u_k)
        a0 = 2 * dbar * l2; b0 = (l2 + dbar - 1)
        nu = a0 - b0 * ev                         # M₀ eigenvalues at u_k
        nu2 = nu[1]                               # at u_2
        Pmat = M - (a0 * np.eye(n) - b0 * L)      # perturbation
        Pn = np.linalg.norm(P0 @ Pmat @ P0, 2)    # spectral norm on 1⊥
        Pnorms.append(Pn)
        neg = 0.0; pos = 0.0; ndk = 0.0
        for j in range(n):
            if j == drop:
                continue
            mu = w[j]; vj = U[:, j]
            c = V.T @ vj                          # coords in L-eigenbasis
            if mu < -1e-9:
                hf = float((c[ev > medlam] ** 2).sum())
                hf_all.append(hf); c2_all.append(float(c[1] ** 2)); mu_all.append(mu)
                ov2 = float(c[1] ** 2)            # |⟨u_2,v_j⟩|² (=|⟨f,v_j⟩|²)
                dkb = min(1.0, Pn ** 2 / (nu2 - mu) ** 2)   # DK bound on ov2
                neg += (-mu) * ov2; ndk += (-mu) * dkb
            elif mu > 1e-9:
                pos += mu * float((u2 @ vj) ** 2)
        neg_act.append(neg); pos_act.append(pos); neg_dk.append(ndk)
        dk_tot += 1
        if ndk <= pos + 1e-9:
            dk_close += 1
    hf_all = np.array(hf_all); c2_all = np.array(c2_all); mu_all = np.array(mu_all)
    Pnorms = np.array(Pnorms)
    neg_act = np.array(neg_act); pos_act = np.array(pos_act); neg_dk = np.array(neg_dk)

    print("\n===== TASK 1: negative v_j in L's eigenbasis =====")
    print(f"  high-freq mass (λ_k>median): mean={hf_all.mean():.3f} median={np.median(hf_all):.3f} "
          f"min={hf_all.min():.3f}  (>0.5 on {100*np.mean(hf_all>0.5):.0f}%)")
    print(f"  |c_2|²=|⟨u_2,v_j⟩|²: max={c2_all.max():.4f} median={np.median(c2_all):.5f} "
          f"mean={c2_all.mean():.5f}")
    print(f"  corr(μ_j, |c_2|²)={np.corrcoef(mu_all,c2_all)[0,1]:+.3f} "
          f"(μ more negative ⇒ {'less' if np.corrcoef(mu_all,c2_all)[0,1]>0 else 'more'} u_2-overlap)")

    print("\n===== TASK 2: perturbation from regular approximation =====")
    print(f"  ||P|| (=||M-M₀|| on 1⊥): median={np.median(Pnorms):.3f} max={Pnorms.max():.3f}")

    print("\n===== TASK 3: Davis-Kahan closure test =====")
    print(f"  DK-predicted neg_part ≤ actual pos_part on {dk_close}/{dk_tot} graphs")
    ratio = neg_dk / np.maximum(pos_act, 1e-9)
    print(f"  DK_neg/pos ratio: median={np.median(ratio):.3f} max={ratio.max():.3f} "
          f"({'CLOSES' if ratio.max()<=1+1e-6 else 'too lossy'})")
    print(f"  actual neg/pos ratio: median={np.median(neg_act/np.maximum(pos_act,1e-9)):.4f} "
          f"max={(neg_act/np.maximum(pos_act,1e-9)).max():.4f}")
    print(f"  => DK far too loose: ||P||≈{np.median(Pnorms):.0f} ≫ eigengap, so the bound is "
          f"~vacuous, while actual median |c_2|²={np.median(c2_all):.5f} is tiny.")


if __name__ == "__main__":
    main()
