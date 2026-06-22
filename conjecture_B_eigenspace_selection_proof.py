"""
Prove/probe the eigenspace-selection lemma: hTconn => exists f in E_{lam2}, gap(f)>=0.
gap(f)=f^T M f - lam^2, M=lam(2D-dd^T/m)-L_t. Restriction M_gap=E^T M E.
- TASK3: test TRACE condition trace(M_gap) >= mult*lam^2 (avg gap>=0) => max gap>=0 (existential).
- TASK4: witness = top eigenvector of M_gap.
- TASK5: does witness's gradient/lift correspond to T(G)'s Fiedler? Rayleigh_{T(G)}(lift) vs lam2(T(G)).
Run: python conjecture_B_eigenspace_selection_proof.py
"""
import numpy as np
import networkx as nx


def triangle_graph(G):
    E = list(G.edges()); TG = nx.Graph(); TG.add_nodes_from(range(len(E)))
    for a in range(len(E)):
        for b in range(a + 1, len(E)):
            s1 = set(E[a]); s2 = set(E[b]); common = s1 & s2
            if len(common) == 1:
                x = common.pop(); p = (s1 - {x}).pop(); q = (s2 - {x}).pop()
                if G.has_edge(p, q): TG.add_edge(a, b)
    return TG, E


def analyze(G):
    G = nx.convert_node_labels_to_integers(G); n = G.number_of_nodes()
    A = nx.to_numpy_array(G); d = A.sum(1); L = np.diag(d) - A
    ev, U = np.linalg.eigh(L); lam = ev[1]
    Eidx = [k for k in range(n) if abs(ev[k] - lam) < 1e-7]
    E = U[:, Eidx]; mult = len(Eidx)
    m = G.number_of_edges(); A2 = A @ A
    Lt = np.zeros((n, n))
    for i in range(n):
        for j in range(n):
            if A[i, j] > 0: Lt[i, j] = -A2[i, j]
    for i in range(n): Lt[i, i] = -sum(Lt[i, j] for j in range(n) if j != i)
    M = lam * (2 * np.diag(d) - np.outer(d, d) / m) - Lt
    Mr = E.T @ M @ E
    evr = np.linalg.eigvalsh(Mr)
    maxgap = evr.max() - lam ** 2
    avggap = float(np.trace(Mr)) / mult - lam ** 2
    # witness = top eigenvector of Mr -> f in E
    w, V = np.linalg.eigh(Mr); c = V[:, -1]; fwit = E @ c; fwit = fwit / np.linalg.norm(fwit)
    # T(G) correspondence: lift gradient of witness onto edges, compare to T(G) Fiedler
    TG, Elist = triangle_graph(G)
    tg_ok = TG.number_of_nodes() > 1 and nx.is_connected(TG)
    corr = None; ray = None; lam2TG = None
    if tg_ok:
        LT = nx.laplacian_matrix(TG, nodelist=range(len(Elist))).toarray().astype(float)
        evt, Ut = np.linalg.eigh(LT); lam2TG = evt[1]; gfied = Ut[:, 1]
        S = float(d @ fwit)
        hlift = np.array([fwit[a] - fwit[b] for (a, b) in Elist])  # gradient g_e (= B^T f)
        hlift = hlift - hlift.mean()  # project off 1 (the -(S/m)1 piece ~ centering)
        if np.linalg.norm(hlift) > 1e-9:
            corr = abs(float(hlift @ gfied) / (np.linalg.norm(hlift) * np.linalg.norm(gfied)))
            ray = float(hlift @ LT @ hlift) / float(hlift @ hlift)
    return dict(n=n, lam=lam, mult=mult, maxgap=maxgap, avggap=avggap, tg_ok=tg_ok,
                corr=corr, ray=ray, lam2TG=lam2TG, lam2G=lam)


def corpus():
    out = []
    def deg2dense(nn, q=0.6, s=1):
        H = nx.gnp_random_graph(nn - 1, q, seed=s); H.add_node(nn - 1)
        H.add_edge(nn - 1, 0); H.add_edge(nn - 1, 1); return H
    out += [("gnp20_.5", nx.gnp_random_graph(20, 0.5, seed=1)),
            ("gnp25_.45", nx.gnp_random_graph(25, 0.45, seed=4)),
            ("gnp20_.6", nx.gnp_random_graph(20, 0.6, seed=3)),
            ("deg2dense40", deg2dense(40)), ("deg2dense60", deg2dense(60)),
            ("rr20_6", nx.random_regular_graph(6, 20, seed=1)),
            ("rr16_5", nx.random_regular_graph(5, 16, seed=2)),
            ("K12", nx.complete_graph(12)), ("K20", nx.complete_graph(20)),
            ("cocktail2x5", nx.complete_multipartite_graph(*([2] * 5))),
            ("Kmult333", nx.complete_multipartite_graph(3, 3, 3)),
            ("wheel12", nx.wheel_graph(12)), ("oct", nx.octahedral_graph())]
    return [(nm, G) for nm, G in out if nx.is_connected(G)]


def main():
    print("=" * 96)
    print("TASK 3 — TRACE route: avg gap = trace(M_gap)/mult - lam^2 >= 0 ⟹ max gap>=0. Test under hTconn.")
    print("=" * 96)
    print(f"  {'graph':14s} {'n':>4} {'mult':>5} {'avg gap':>10} {'max gap':>10} {'TGconn':>7} "
          f"{'avg>=0?':>8}")
    rows = []
    for nm, G in corpus():
        q = analyze(G); rows.append((nm, q))
        print(f"  {nm:14s} {q['n']:4d} {q['mult']:5d} {q['avggap']:10.4f} {q['maxgap']:10.4f} "
              f"{str(q['tg_ok']):>7} {str(q['avggap']>=-1e-7):>8}")
    tgc = [(nm, q) for nm, q in rows if q['tg_ok']]
    avg_ok = sum(1 for _, q in tgc if q['avggap'] >= -1e-7)
    print(f"\n  TG-connected: avg gap >= 0 in {avg_ok}/{len(tgc)}  "
          f"({'TRACE route works' if avg_ok==len(tgc) else 'avg<0 sometimes -> trace route too weak'})")

    print("\n" + "=" * 96)
    print("TASK 5 — witness (top M_gap eigenvector) lift vs T(G) Fiedler: |cos|, Rayleigh_{T(G)} vs λ₂(T(G))")
    print("=" * 96)
    print(f"  {'graph':14s} {'|cos(lift,g*)|':>14} {'Ray_TG(lift)':>13} {'λ₂(T(G))':>10} {'λ₂(G)':>9} "
          f"{'Ray<=λ₂G?':>10}")
    for nm, q in tgc:
        if q['corr'] is None: continue
        print(f"  {nm:14s} {q['corr']:14.4f} {q['ray']:13.4f} {q['lam2TG']:10.4f} {q['lam2G']:9.4f} "
              f"{str(q['ray']<=q['lam2G']+1e-6):>10}")
    print("  (witness lift = B^T f centered; if Ray_TG(lift) <= λ₂(G) then the lift CERTIFIES")
    print("   λ₂(T(G)) <= λ₂(G) [Courant-Fischer]. |cos| high => witness lift ~ T(G) Fiedler.)")

    print("\n" + "=" * 96)
    print("SUMMARY")
    print("=" * 96)
    print(f"  TRACE route (avg gap>=0) under hTconn: {avg_ok}/{len(tgc)}.")
    print("  witness=top M_gap eigvec; its centered gradient lift Rayleigh on T(G) vs λ₂(G) above.")


if __name__ == "__main__":
    main()
