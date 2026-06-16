"""
The two hub lemmas that would close Conjecture B via negative-cone avoidance.

LEMMA 2 (hub-flatness): from Lf=λ₂f, (Af)_v=(d_v-λ₂)f_v, C-S ⇒
    f_v² ≤ d_v·Σ_{u~v}f_u²/(d_v-λ₂)²  ≤  d_v/(d_v-λ₂)²   (steps 1-4)
LEMMA 1 (hub-localization of M=λ₂Q-L_t negative eigvecs)            (steps 5-6)
CLOSURE: negative_part = Σ_{μ_j<0}|μ_j||⟨f,v_j⟩|² ≤ positive_part   (step 8)
Run:  python conjecture_B_hub_lemmas.py
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
    graphs = corpus(9)
    print(f"corpus: {len(graphs)} distinct graphs")

    # ===================== LEMMA 2 =====================
    print("\n===== LEMMA 2 (hub-flatness): f_v² ≤ d_v/(d_v-λ₂)² =====")
    viol = 0; nvert = 0; tight = []; hub_viol = 0; hub_n = 0
    nbr_ratio = []  # Σ_{u~v}f_u²  vs 1/d_v, λ₂/d_v
    for G in graphs:
        nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}; n = len(nodes)
        L = nx.laplacian_matrix(G, nodelist=nodes).toarray().astype(float)
        d = L.diagonal(); ev, V = np.linalg.eigh(L); l2 = ev[1]
        if l2 < 1e-6:
            continue
        f = V[:, 1] / np.linalg.norm(V[:, 1])
        for v in range(n):
            dv = d[v]
            if abs(dv - l2) < 1e-6:
                continue
            nvert += 1
            bound = dv / (dv - l2) ** 2
            if f[v] ** 2 > bound + 1e-9:
                viol += 1
            tight.append(f[v] ** 2 / bound)
            nbrsq = sum(f[idx[u]] ** 2 for u in G[v])
            nbr_ratio.append((nbrsq, dv, l2))
            if dv >= 2 * l2:                     # hub
                hub_n += 1
                if f[v] ** 2 > 4.0 / dv + 1e-9:
                    hub_viol += 1
    tight = np.array(tight)
    print(f"  [1] f_v² ≤ d_v/(d_v-λ₂)²: violations {viol}/{nvert};  "
          f"tightness f_v²/bound: max={tight.max():.4f} median={np.median(tight):.5f}")
    print(f"      hub bound (d_v≥2λ₂ ⇒ f_v²≤4/d_v): violations {hub_viol}/{hub_n}")
    # [2] sharper neighbor-sum
    nr = np.array(nbr_ratio)
    print(f"  [2] Σ_{{u~v}}f_u²: max={nr[:,0].max():.4f} median={np.median(nr[:,0]):.5f} "
          f"(crude bound used =1). vs 1/d_v: Σf_u²·d_v median={np.median(nr[:,0]*nr[:,1]):.4f}")

    # [3] hub-mass bound for τ=2λ₂
    print("  [3] hub-mass  Σ_{d_v≥2λ₂} f_v²  vs bound Σ d_v/(d_v-λ₂)²:")
    hm_act = []; hm_bnd = []
    for G in graphs:
        nodes = list(G.nodes()); n = len(nodes)
        L = nx.laplacian_matrix(G, nodelist=nodes).toarray().astype(float)
        d = L.diagonal(); ev, V = np.linalg.eigh(L); l2 = ev[1]
        if l2 < 1e-6:
            continue
        f = V[:, 1] / np.linalg.norm(V[:, 1])
        hubs = [v for v in range(n) if d[v] >= 2 * l2 and abs(d[v] - l2) > 1e-6]
        if not hubs:
            continue
        hm_act.append(sum(f[v] ** 2 for v in hubs))
        hm_bnd.append(sum(d[v] / (d[v] - l2) ** 2 for v in hubs))
    hm_act = np.array(hm_act); hm_bnd = np.array(hm_bnd)
    ok = int(np.sum(hm_act <= hm_bnd + 1e-9))
    print(f"      graphs with hubs: {len(hm_act)};  bound holds {ok}/{len(hm_act)};  "
          f"actual hub-mass median={np.median(hm_act):.4f} max={hm_act.max():.4f}; "
          f"bound median={np.median(hm_bnd):.4f}")

    # ===================== LEMMA 1 + CLOSURE =====================
    print("\n===== LEMMA 1 (hub-localization of M=λ₂Q-L_t negative eigvecs) =====")
    sample = [G for G in graphs if nx.is_connected(G)][:1500]
    dwmass_min = 1e9; hubfrac_min = 1e9; nneg_total = 0
    neg_parts = []; pos_parts = []; bound_parts = []
    fMf_min = 1e9
    for G in sample:
        nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}; n = len(nodes)
        L = nx.laplacian_matrix(G, nodelist=nodes).toarray().astype(float)
        d = L.diagonal(); A = np.diag(d) - L
        ev, V = np.linalg.eigh(L); l2 = ev[1]
        if l2 < 1e-6:
            continue
        f = V[:, 1] / np.linalg.norm(V[:, 1])
        Q = np.diag(d) + A; Lt = tri_laplacian(G, nodes, idx); M = l2 * Q - Lt
        ones = np.ones(n); P = np.eye(n) - np.outer(ones, ones) / n
        w, U = np.linalg.eigh(P @ M @ P); drop = int(np.argmax(np.abs(U.T @ ones)))
        med = np.median(d); dbar = d.mean()
        tau = 2 * l2
        hubmass_f = sum(f[v] ** 2 for v in range(n) if d[v] >= tau and abs(d[v] - l2) > 1e-6)
        neg = 0.0; pos = 0.0; bnd = 0.0; maxmu = 0.0
        for j in range(n):
            if j == drop:
                continue
            mu = w[j]; vj = U[:, j]; ov = float(f @ vj)
            if mu < -1e-9:
                nneg_total += 1
                dwm = float((d * vj * vj).sum()) / dbar            # >1 ⇒ hub-concentrated
                hubf = float(sum(vj[v] ** 2 for v in range(n) if d[v] >= med))
                dwmass_min = min(dwmass_min, dwm); hubfrac_min = min(hubfrac_min, hubf)
                neg += (-mu) * ov * ov; maxmu = max(maxmu, -mu)
                # lemma-based bound on ⟨f,vj⟩²: split hub/rest, C-S each
                hubloc = float(sum(vj[v] ** 2 for v in range(n) if d[v] >= tau and abs(d[v] - l2) > 1e-6))
                ovb = (np.sqrt(max(hubmass_f * hubloc, 0)) + np.sqrt(max(1 - hubloc, 0))) ** 2
                bnd += (-mu) * ovb
            elif mu > 1e-9:
                pos += mu * ov * ov
        neg_parts.append(neg); pos_parts.append(pos); bound_parts.append(bnd)
        fMf_min = min(fMf_min, pos - neg)
    neg_parts = np.array(neg_parts); pos_parts = np.array(pos_parts); bound_parts = np.array(bound_parts)
    print(f"  [5] deg-weighted mass Σd_v v_v²/d̄ of NEG eigvecs: min across corpus={dwmass_min:.3f} "
          f"(>1 ⇒ hub-concentrated)")
    print(f"  [6] fraction of NEG-eigvec mass on d_v≥median: min={hubfrac_min:.3f} "
          f"(>0.5 ⇒ majority on hubs); #neg eigvecs={nneg_total}")
    print("\n===== CLOSURE TEST (step 8) =====")
    print(f"  actual: neg_part ≤ pos_part on {int(np.sum(neg_parts<=pos_parts+1e-9))}/{len(neg_parts)} "
          f"(= B holds); min(fMf)={fMf_min:.4f}")
    print(f"  lemma-bound on neg_part ≤ pos_part on {int(np.sum(bound_parts<=pos_parts+1e-9))}/{len(bound_parts)} "
          f"(does the MECHANISM close B quantitatively?)")
    ratio = bound_parts / np.maximum(pos_parts, 1e-9)
    print(f"  bound/pos ratio: median={np.median(ratio):.3f} max={ratio.max():.3f} "
          f"({'CLOSES (bound<pos)' if ratio.max()<=1+1e-6 else 'too lossy on some graphs'})")
    print(f"  neg/pos ratio (actual): median={np.median(neg_parts/np.maximum(pos_parts,1e-9)):.3f} "
          f"max={(neg_parts/np.maximum(pos_parts,1e-9)).max():.3f}")


if __name__ == "__main__":
    main()
