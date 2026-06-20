"""
Stress-test the TYPE A scalar bound  c(q) >= 7.3 * gamma/Delta   (gap = c(q)*n/m).

Adversarial cores H designed to minimize c(q)/(gamma/Delta):
  - two dense blobs weakly connected (attach same blob / across the bottleneck)
  - expander + dangling dense appendage
  - highly irregular core (complete bipartite, windmill)
  - two high-degree attachment vertices
  - attachments at the H-Fiedler bottleneck (argmax |psi2(H)|)

Reports c(q)/(gamma/Delta), plus diagnostics: lam2(G)/gamma (is v0 the bottleneck?),
f_v0^2 (Fiedler localization), R_aa (resolvent diag at attachment), psi2 alignment.
Run: python conjecture_B_typeA_scalar_bound_stresstest.py
"""
import numpy as np
import networkx as nx


def attach_at(H, a, b):
    H = nx.convert_node_labels_to_integers(H)
    nH = H.number_of_nodes()
    G = nx.Graph(H); G.add_node(nH); G.add_edge(nH, a); G.add_edge(nH, b)
    return G, nH, a, b


def analyze(H, a, b, label):
    Hc = nx.convert_node_labels_to_integers(H)
    nH = Hc.number_of_nodes()
    AH = nx.to_numpy_array(Hc, nodelist=list(range(nH))); dH = AH.sum(1)
    LH = np.diag(dH) - AH
    evH, UH = np.linalg.eigh(LH); gamma = float(evH[1]); psi2 = UH[:, 1]
    G, v0lbl, a, b = attach_at(Hc, a, b)
    nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}; n = len(nodes)
    A = nx.to_numpy_array(G, nodelist=nodes); d = A.sum(1); L = np.diag(d) - A
    ev, U = np.linalg.eigh(L); lam = ev[1]; f = U[:, 1]; f = f / np.linalg.norm(f)
    v0 = idx[v0lbl]
    if f[v0] < 0:
        f = -f
    m = G.number_of_edges(); S = float(d @ f)
    x = float(f[v0])
    Gsum = sum((f[idx[u]] + f[idx[v]]) ** 2 for u, v in G.edges())
    B2 = sum((min(d[idx[u]], d[idx[v]]) - 1) * (f[idx[u]] - f[idx[v]]) ** 2 for u, v in G.edges())
    gap = lam * (Gsum - S ** 2 / m) - B2
    c_q = gap * m / n
    Delta = float(dH.max()); delta = float(dH.min())
    # resolvent diag at attachments
    R = np.zeros((nH, nH))
    for k in range(1, nH):
        R += np.outer(UH[:, k], UH[:, k]) / (evH[k] - lam)
    Raa = R[idx_in_core(a, nH)], R  # placeholder
    Raa = R[a, a]
    align_a = abs(psi2[a]) * np.sqrt(nH)   # ~1 if typical, >>1 if a sits on bottleneck
    align_b = abs(psi2[b]) * np.sqrt(nH)
    ratio = c_q / (gamma / Delta) if gamma > 1e-9 else np.nan
    return dict(label=label, n=n, m=m, nH=nH, lam=lam, gamma=gamma, Delta=Delta, delta=delta,
                gap=gap, c_q=c_q, ratio=ratio, lam_over_gamma=lam / max(gamma, 1e-9),
                fv02=x * x, Raa=Raa, gRaa=gamma * Raa, align=max(align_a, align_b),
                da=float(d[a]), db=float(d[b]), Dmax=Delta, dmin=delta)


def idx_in_core(a, nH):
    return a


def two_blobs(k, nbridge, seed=0):
    G = nx.Graph()
    G.add_edges_from((i, j) for i in range(k) for j in range(i + 1, k))
    G.add_edges_from((k + i, k + j) for i in range(k) for j in range(i + 1, k))
    rng = np.random.default_rng(seed)
    for _ in range(nbridge):
        G.add_edge(int(rng.integers(0, k)), int(k + rng.integers(0, k)))
    return G


def expander_appendage(n_exp, deg, k_app, seed=0):
    E = nx.random_regular_graph(deg, n_exp, seed=seed)
    E = nx.convert_node_labels_to_integers(E)
    App = nx.complete_graph(k_app)
    G = nx.disjoint_union(E, App)
    G.add_edge(0, n_exp)            # attach appendage to expander vertex 0
    return G


def windmill(blades, k):
    # `blades` copies of K_k all sharing one hub vertex -> highly irregular
    G = nx.Graph(); hub = 0; nid = 1
    for _ in range(blades):
        verts = [hub] + list(range(nid, nid + k - 1)); nid += k - 1
        G.add_edges_from((verts[i], verts[j]) for i in range(len(verts)) for j in range(i + 1, len(verts)))
    return G


def bottleneck_pair(H):
    Hc = nx.convert_node_labels_to_integers(H)
    nH = Hc.number_of_nodes()
    L = nx.laplacian_matrix(Hc, nodelist=list(range(nH))).toarray().astype(float)
    _, U = np.linalg.eigh(L); psi2 = U[:, 1]
    order = np.argsort(-np.abs(psi2))
    return int(order[0]), int(order[1])


def hi_degree_pair(H):
    Hc = nx.convert_node_labels_to_integers(H)
    deg = dict(Hc.degree()); order = sorted(deg, key=lambda u: -deg[u])
    return order[0], order[1]


def families():
    out = []
    # baselines
    for nH in [60, 120]:
        out.append((nx.gnp_random_graph(nH, 0.5, seed=1), 0, 1, f"gnp{nH}_.5 typical"))
        out.append((nx.random_regular_graph(max(3, nH//4), nH, seed=1), 0, 1, f"rr{nH} typical"))
    # 1. two weakly-connected blobs
    for k, br in [(20, 1), (20, 2), (30, 1), (30, 3)]:
        H = two_blobs(k, br)
        out.append((H, 0, 1, f"2blob(k{k},br{br}) same"))
        out.append((H, 0, k, f"2blob(k{k},br{br}) across"))
        ba, bb = bottleneck_pair(H)
        out.append((H, ba, bb, f"2blob(k{k},br{br}) bottleneck"))
    # 2. expander + dense appendage
    for ne, dg, ka in [(60, 8, 12), (100, 10, 20)]:
        H = expander_appendage(ne, dg, ka)
        out.append((H, 0, 1, f"exp{ne}+app{ka} on-exp"))
        out.append((H, ne, ne + 1, f"exp{ne}+app{ka} on-app"))
        ba, bb = bottleneck_pair(H)
        out.append((H, ba, bb, f"exp{ne}+app{ka} bottleneck"))
    # 3. highly irregular
    for blades, k in [(6, 8), (10, 6)]:
        H = windmill(blades, k)
        out.append((H, hi_degree_pair(H)[0], hi_degree_pair(H)[1], f"windmill({blades},{k}) hubs"))
        ba, bb = bottleneck_pair(H)
        out.append((H, ba, bb, f"windmill({blades},{k}) bottleneck"))
    out.append((nx.complete_bipartite_graph(8, 40), 0, 1, "K_8,40 (irregular) sameside"))
    out.append((nx.complete_bipartite_graph(8, 40), 0, 8, "K_8,40 across"))
    # 4. two high-degree attachments on gnp
    for nH in [80]:
        H = nx.gnp_random_graph(nH, 0.4, seed=2)
        a, b = hi_degree_pair(H)
        out.append((H, a, b, f"gnp{nH}_.4 hi-deg attach"))
        ba, bb = bottleneck_pair(H)
        out.append((H, ba, bb, f"gnp{nH}_.4 bottleneck attach"))
    return out


def main():
    rows = []
    for H, a, b, lab in families():
        Hc = nx.convert_node_labels_to_integers(H)
        if not nx.is_connected(Hc) or Hc.number_of_nodes() < 6:
            continue
        try:
            rows.append(analyze(Hc, a, b, lab))
        except Exception as e:
            print("skip", lab, e)

    print("=" * 116)
    print("STRESS TEST  c(q) >= 7.3 gamma/Delta   (ratio = c(q)/(gamma/Delta))")
    print("=" * 116)
    print(f"  {'core/attach':32s} {'gap':>9} {'c(q)':>7} {'γ/Δ':>6} {'ratio':>7} "
          f"{'λ2/γ':>7} {'fv0²':>6} {'γ·Raa':>7} {'align':>6} {'BELOW7.3':>8}")
    for q in sorted(rows, key=lambda z: z['ratio']):
        flag = "*** " if q['ratio'] < 7.3 else ""
        print(f"  {q['label']:32s} {q['gap']:9.5f} {q['c_q']:7.2f} {q['gamma']/q['Delta']:6.3f} "
              f"{q['ratio']:7.2f} {q['lam_over_gamma']:7.3f} {q['fv02']:6.3f} {q['gRaa']:7.2f} "
              f"{q['align']:6.2f} {flag:>8}")

    print("\n" + "=" * 116)
    print("ANALYSIS")
    print("=" * 116)
    ratios = np.array([q['ratio'] for q in rows])
    print(f"  min ratio c(q)/(γ/Δ) = {ratios.min():.3f}   (claim: >= 7.3)")
    below = [q for q in rows if q['ratio'] < 7.3]
    print(f"  families BELOW 7.3: {len(below)}/{len(rows)}")
    for q in below:
        print(f"     {q['label']:32s} ratio={q['ratio']:.2f}  λ2/γ={q['lam_over_gamma']:.3f} "
              f"fv0²={q['fv02']:.3f} γ·Raa={q['gRaa']:.2f} align={q['align']:.2f}")
    # is v0 the bottleneck? (TYPE A requires lam2(G) << gamma, fv0^2 large)
    typeA = [q for q in rows if q['lam_over_gamma'] < 0.5 and q['fv02'] > 0.3]
    if typeA:
        rA = np.array([q['ratio'] for q in typeA])
        print(f"\n  Restrict to genuine TYPE A (λ2/γ<0.5 AND fv0²>0.3): {len(typeA)} families, "
              f"min ratio = {rA.min():.3f}")
    # refined bound: c(q) >= c0 * (gamma/Delta) / (gamma*Raa) ?  test
    print("\n  refined regularizer test  c(q)·(γ·Raa)/(γ/Δ) [= c(q)·Δ·Raa]:")
    reg = np.array([q['c_q'] * q['gRaa'] / (q['gamma'] / q['Delta']) for q in rows])
    print(f"     min={reg.min():.2f} median={np.median(reg):.2f} max={reg.max():.2f}")


if __name__ == "__main__":
    main()
