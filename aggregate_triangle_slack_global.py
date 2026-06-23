"""
Global slack for aggregate Poincare: Slack = 2lam*degQuad - T >= 0.
T_unord = f^T L_t f, L_t = diag(rowsum(A2 o A)) - (A2 o A) (triangle Laplacian, A2=A@A).
Lean T_ord = 2*T_unord, degQuad=f^T D f => Slack_ord = 2 f^T Q f, Q = lam*D - L_t.
Q1: is Q = lam2*D - L_t PSD globally? on 1-perp? on E_{lam2}? Fiedler slack = f^T Q f.
Run: python aggregate_triangle_slack_global.py
"""
import numpy as np
import networkx as nx


def analyze(G):
    G = nx.convert_node_labels_to_integers(G); n = G.number_of_nodes()
    if not nx.is_connected(G): return None
    A = nx.to_numpy_array(G); d = A.sum(1); L = np.diag(d) - A
    ev, U = np.linalg.eigh(L); lam = ev[1]; f = U[:, 1]; f = f / np.linalg.norm(f)
    A2 = A @ A
    Wt = A2 * A                      # Hadamard: (A^2)_ab on edges (= t_e), 0 else
    Lt = np.diag(Wt.sum(1)) - Wt     # triangle Laplacian
    D = np.diag(d)
    Q = lam * D - Lt                 # Slack_ord = 2 f^T Q f
    # verify f^T Lt f = T_unord
    edges = [(i, j) for i in range(n) for j in range(i + 1, n) if A[i, j] > 0]
    T_un = sum(A2[a, b] * (f[a] - f[b]) ** 2 for a, b in edges)
    id_Lt = abs(float(f @ Lt @ f) - T_un)
    RHS_half = lam * float(d @ (f * f))           # = lam*degQuad ; Slack_half = f^T Q f
    slack_f = float(f @ Q @ f)
    # eigenvalues of Q (global) and on 1-perp
    evQ = np.linalg.eigvalsh(Q)
    P = np.eye(n) - np.ones((n, n)) / n
    evQ1 = np.sort(np.linalg.eigvalsh(P @ Q @ P))
    minQ = evQ[0]; minQ1 = evQ1[1]    # 1-perp: drop the projection-kernel ~0
    # E_{lam2} eigenspace: min of f^T Q f over unit vectors in eigenspace
    Ei = [k for k in range(n) if abs(ev[k] - lam) < 1e-6]
    Qr = U[:, Ei].T @ Q @ U[:, Ei]
    minEig_eigsp = float(np.linalg.eigvalsh(Qr)[0]) if len(Ei) >= 1 else 0.0
    return dict(n=n, lam=lam, id_Lt=id_Lt, slack_f=slack_f, RHS_half=RHS_half,
                slack_ratio=slack_f / RHS_half if RHS_half > 0 else 9.9,
                minQ=minQ, minQ_over_lam=minQ / lam if lam > 0 else 0.0,
                minQ1=minQ1, mult=len(Ei), minEig_eigsp=minEig_eigsp,
                regular=(d.max() == d.min()))


def corpus():
    out = []; rng = np.random.default_rng(0)
    def d2(nn, q, s):
        H = nx.gnp_random_graph(nn - 1, q, seed=s); H.add_node(nn - 1); H.add_edge(nn - 1, 0); H.add_edge(nn - 1, 1); return H
    def twin(N, dd):
        K = nx.complete_graph(N); a, b = N, N + 1
        for x in (a, b):
            for w in range(dd): K.add_edge(x, w)
        K.add_node(N + 2); K.add_edge(N + 2, a); K.add_edge(N + 2, b); return K
    def star(kc, ks):
        Gr = nx.complete_graph(kc)
        for i in range(ks): Gr.add_edge(0, kc + i)
        return Gr
    for nn in [40, 60, 80]:
        for q in [0.02, 0.05, 0.1, 0.2, 0.4, 0.7, 0.95]: out.append((f"deg2d{nn}_{q}", "TYPEA", d2(nn, q, 7)))
    for N in [30, 60]:
        for dd in [2, 3]: out.append((f"twin{N}_{dd}", "TYPEA", twin(N, dd)))
    for kc, ks in [(10, 6), (12, 8)]: out.append((f"star{kc}_{ks}", "CLIQUESTAR", star(kc, ks)))
    for k, l in [(10, 10), (15, 12)]: out.append((f"lolli{k}_{l}", "TYPEB", nx.lollipop_graph(k, l)))
    for k, l in [(8, 8)]: out.append((f"barb{k}_{l}", "TYPEB", nx.barbell_graph(k, l)))
    for nn in [25, 40]:
        for q in [0.3, 0.5, 0.7]: out.append((f"gnp{nn}_{q}", "RANDOM", nx.gnp_random_graph(nn, q, seed=int(rng.integers(1e9)))))
    for nn in [20, 40]:
        for r in [4, nn // 2]:
            if 3 <= r < nn and (r * nn) % 2 == 0: out.append((f"rr{nn}_{r}", "REGULAR", nx.random_regular_graph(r, nn, seed=1)))
    out.append(("cocktail6", "MULTIPART", nx.complete_multipartite_graph(*([2] * 6))))
    out.append(("Kmp444", "MULTIPART", nx.complete_multipartite_graph(4, 4, 4)))
    out.append(("Kmp225", "MULTIPART", nx.complete_multipartite_graph(2, 2, 5)))
    for nn in [10, 20, 30, 50]: out.append((f"K{nn}", "REGULAR", nx.complete_graph(nn)))
    return out


def main():
    data = [(nm, cl, q) for nm, cl, G in corpus() for q in [analyze(G)] if q is not None]
    print(f"  {len(data)} graphs; Lt identity max err {max(q['id_Lt'] for _,_,q in data):.1e}")
    print(f"  Fiedler slack>=0 (aggregate): {sum(1 for _,_,q in data if q['slack_f']>=-1e-7)}/{len(data)}")

    print("\n" + "=" * 92)
    print("TASK 2 — is Q = λ₂D - L_t PSD? global min eig; on 1-perp; on E_{λ₂}")
    print("=" * 92)
    gpsd = sum(1 for _, _, q in data if q['minQ'] >= -1e-7)
    p1 = sum(1 for _, _, q in data if q['minQ1'] >= -1e-7)
    esp = sum(1 for _, _, q in data if q['minEig_eigsp'] >= -1e-7)
    print(f"  Q PSD globally (min eig>=0):   {gpsd}/{len(data)}  (min over corpus {min(q['minQ'] for _,_,q in data):.3f})")
    print(f"  Q PSD on 1-perp:               {p1}/{len(data)}  (min {min(q['minQ1'] for _,_,q in data):.3f})")
    print(f"  Q PSD on E_{{λ₂}} eigenspace:    {esp}/{len(data)}  (min {min(q['minEig_eigsp'] for _,_,q in data):.3f})")

    print("\n" + "=" * 92)
    print("TASK 4 — minimum Slack/RHS; eigenstructure of near-extremals")
    print("=" * 92)
    print(f"  {'graph':12s} {'class':>11} {'slack/RHS':>10} {'minQ/λ':>8} {'minQ|1perp':>11} {'mult':>5}")
    for nm, cl, q in sorted(data, key=lambda x: x[2]['slack_ratio'])[:14]:
        print(f"  {nm:12s} {cl:>11} {q['slack_ratio']:10.4f} {q['minQ_over_lam']:8.3f} {q['minQ1']:11.4f} {q['mult']:5d}")

    print("\n" + "=" * 92)
    print("TASK 3 — K_n decomposition: Slack_half = f^T Q f; K_n slack = λ (RHS/(n-1))")
    print("=" * 92)
    for nm in ["K10", "K20", "K50", "cocktail6", "Kmp444"]:
        q = dict((n_, qq) for n_, _, qq in data).get(nm)
        if q: print(f"  {nm:10s} slack/RHS={q['slack_ratio']:.4f}  minQ/λ={q['minQ_over_lam']:.3f}  "
                    f"pred 1/(n-1)={1/(q['n']-1):.4f}")

    print("\n" + "=" * 92)
    print("SUMMARY")
    print("=" * 92)
    print(f"  Q=λ₂D-L_t: PSD global {gpsd}/{len(data)}, on 1-perp {p1}/{len(data)}, on E_λ₂ {esp}/{len(data)}")
    if gpsd == len(data):
        print("  => Q PSD GLOBALLY => aggregate T<=2λdegQuad for ALL f (matrix proof!).")
    elif p1 == len(data):
        print("  => Q PSD on 1-perp (Fiedler in 1-perp) => aggregate proven via Q|1perp >=0.")
    else:
        print("  => Q indefinite; aggregate is Fiedler-eigenspace-specific (check E_λ₂ column).")


if __name__ == "__main__":
    main()
