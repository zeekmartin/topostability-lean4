"""
Attack on B2':  W1 = Σ_{ab∈E}(min(d_a,d_b)-1)(f_a-f_b)² ≤ λ₂(fᵀ(D+A)f - S²/m).
f unit Fiedler, S=Σd_v f_v, m=|E|.  R'' := λ₂(fᵀDf - λ₂ + 1 - S²/m).
E_grad = Σ|d_a-d_b|(f_a-f_b)²,  E_disc = Σ_v f_v² disc(v), disc(v)=Σ_{b~v}(d_b-d_v).

APPROACH 1: verify  RHS - W1 = R'' + ½E_grad - ½E_disc  (eigen-eq algebra), assess sign struct.
APPROACH 2: symmetric relaxation LHS_sym=Σ((d_a+d_b)/2-1)(f_a-f_b)²; test LHS_sym ≤ RHS.
            asymmetric = 2·sym. (min-1 = sym - ½E_grad: is the |Δd| term essential?)
APPROACH 3: SOS — quadratic form structure on the Fiedler eigenspace (small graphs).
Run:  python conjecture_B2prime_attack.py
"""
import numpy as np
import networkx as nx
import counterexample_search as ce

TOL = 1e-9


def pieces(G, f=None):
    nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}
    edges = list(G.edges()); n, m = len(nodes), len(edges)
    L = nx.laplacian_matrix(G, nodelist=nodes).toarray().astype(float)
    d = L.diagonal().copy(); A = np.diag(d) - L
    ev, V = np.linalg.eigh(L); l2 = float(ev[1])
    if f is None:
        f = V[:, 1] / np.linalg.norm(V[:, 1])
    fDf = float((d * f * f).sum()); fD2f = float((d * d * f * f).sum())
    S = float(d @ f); fQf = 2 * fDf - l2
    disc = (A @ d) - d * d
    Edisc = float((f * f) @ disc)
    W1 = 0.0; Egrad = 0.0; LHSsym = 0.0; fLtf = 0.0
    for u, v in edges:
        i, j = idx[u], idx[v]; g = (f[i] - f[j]) ** 2
        W1 += (min(d[i], d[j]) - 1) * g
        Egrad += abs(d[i] - d[j]) * g
        LHSsym += ((d[i] + d[j]) / 2 - 1) * g
        fLtf += len(set(G[u]) & set(G[v])) * g
    RHS = l2 * (fQf - S * S / m)
    Rpp = l2 * (fDf - l2 + 1 - S * S / m)
    return dict(n=n, m=m, l2=l2, fDf=fDf, fD2f=fD2f, S=S, fQf=fQf,
                W1=W1, Egrad=Egrad, Edisc=Edisc, LHSsym=LHSsym, fLtf=fLtf,
                RHS=RHS, Rpp=Rpp)


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


def hard_families():
    out = []; rng = np.random.default_rng(7)
    for _ in range(150):
        n = int(rng.integers(20, 36)); q = float(rng.uniform(0.55, 0.72))
        Gb = nx.gnp_random_graph(n - 1, q, seed=int(rng.integers(0, 2**31)))
        Gb = nx.relabel_nodes(Gb, {i: i + 1 for i in range(n - 1)}); Gb.add_node(0)
        for b in rng.choice(range(1, n), size=2, replace=False):
            Gb.add_edge(0, int(b))
        out.append(Gb)
    for _ in range(100):
        n = int(rng.integers(15, 40)); k = int(rng.integers(4, min(14, n - 1)))
        out.append(nx.watts_strogatz_graph(n, k + (k % 2), float(rng.uniform(0.05, 0.5)),
                                            seed=int(rng.integers(0, 2**31))))
    for n in (20, 40, 80):
        G = nx.complete_graph(n); G.remove_edge(0, 1); out.append(G)
    return [G for G in out if nx.is_connected(G)]


def main():
    graphs = corpus(9)
    rows = [pieces(G) for G in graphs]
    rows = [r for r in rows if r["l2"] > 1e-6]
    N = len(rows)
    hard = [pieces(G) for G in hard_families()]
    hard = [r for r in hard if r["l2"] > 1e-6]
    print(f"corpus distinct: {N};  hard families: {len(hard)}")

    # --- sanity: W1 = LHSsym - ½ E_grad ? ---
    e1 = max(abs(r["W1"] - (r["LHSsym"] - 0.5 * r["Egrad"])) for r in rows)
    print(f"\n[id] W1 = LHS_sym - ½E_grad : max err {e1:.2e}")

    # --- APPROACH 1: RHS - W1 = R'' + ½E_grad - ½E_disc ? (pin the E_disc sign) ---
    e_plus = max(abs((r["RHS"] - r["W1"]) - (r["Rpp"] + 0.5 * r["Egrad"] - 0.5 * r["Edisc"])) for r in rows)
    e_minus = max(abs((r["RHS"] - r["W1"]) - (r["Rpp"] + 0.5 * r["Egrad"] + 0.5 * r["Edisc"])) for r in rows)
    sgn = "-½E_disc" if e_plus < e_minus else "+½E_disc"
    print(f"[APPROACH 1] RHS - W1 = R'' + ½E_grad {sgn} : max err {min(e_plus,e_minus):.2e}")
    print(f"   ⇒ B2' ⟺ ({'½E_disc' if e_plus<e_minus else '-½E_disc'}) - ½E_grad ≤ R''")
    # also: Σ(d_a+d_b)(f_a-f_b)² = 2λ₂fDf ± E_disc ?
    P = np.array([2*r["LHSsym"] + 2*r["m"]*0 for r in rows])  # P = Σ(d_a+d_b)(.)² = 2(LHSsym + λ₂)
    eP_plus = max(abs((2*(r["LHSsym"]) + 2*r["l2"]) - (2*r["l2"]*r["fDf"] + r["Edisc"])) for r in rows)
    eP_minus = max(abs((2*(r["LHSsym"]) + 2*r["l2"]) - (2*r["l2"]*r["fDf"] - r["Edisc"])) for r in rows)
    print(f"   Σ(d_a+d_b)(Δf)² = 2λ₂fᵀDf {'+E_disc' if eP_plus<eP_minus else '-E_disc'} : "
          f"max err {min(eP_plus,eP_minus):.2e}")

    # --- APPROACH 2: symmetric / asymmetric relaxation ---
    print("\n[APPROACH 2] relaxations (does relaxed-LHS ≤ RHS ?):")
    for label, rs in [("corpus", rows), ("hard", hard)]:
        sym = np.array([r["LHSsym"] / r["RHS"] for r in rs if r["RHS"] > 1e-12])
        asym = 2 * sym
        nsym = int(np.sum(sym <= 1 + 1e-9)); nas = int(np.sum(asym <= 1 + 1e-9))
        print(f"  {label:7s}: LHS_sym/RHS max={sym.max():.3f} (≤1: {nsym}/{len(sym)}) | "
              f"asym(2·sym)/RHS max={asym.max():.3f} (≤1: {nas}/{len(asym)})")
    print("  (W1/RHS for reference:)")
    for label, rs in [("corpus", rows), ("hard", hard)]:
        w = np.array([r["W1"] / r["RHS"] for r in rs if r["RHS"] > 1e-12])
        print(f"  {label:7s}: W1/RHS max={w.max():.4f}  (B2' holds: {int(np.sum(w<=1+1e-9))}/{len(w)})")

    # --- the essential term: how often is ½E_grad needed (sym fails but min works)? ---
    symfail = [r for r in rows + hard if r["LHSsym"] > r["RHS"] + 1e-9]
    print(f"\n  symmetric relaxation FAILS on {len(symfail)}/{N+len(hard)} graphs "
          f"(min-1 works on all) ⇒ the |d_a-d_b| (E_grad) term is ESSENTIAL")
    if symfail:
        worst = max(symfail, key=lambda r: r["LHSsym"]/r["RHS"])
        print(f"   worst LHS_sym/RHS = {worst['LHSsym']/worst['RHS']:.3f} (n={worst['n']} m={worst['m']})")

    # --- APPROACH 3: SOS / quadratic-form structure ---
    print("\n[APPROACH 3] structure of B2' ⟺ ½E_disc - ½E_grad ≤ R'':")
    # E_disc = Σ f_v² disc(v) is signed; E_grad ≥0; R'' = λ₂(fDf-λ₂+1-S²/m).
    # report sign distribution of E_disc and the slack R'' + ½E_grad - ½E_disc
    Ed = np.array([r["Edisc"] for r in rows])
    slack = np.array([r["Rpp"] + 0.5*r["Egrad"] - 0.5*r["Edisc"] for r in rows])
    print(f"  E_disc: min={Ed.min():.3f} median={np.median(Ed):.3f} max={Ed.max():.3f} "
          f"(signed; <0 on {100*np.mean(Ed<0):.0f}%)")
    print(f"  slack (RHS-W1): min={slack.min():.4f} (≥0 ⟺ B2')  — manifestly SOS? "
          f"E_grad≥0 but E_disc signed and R'' can be <0, so NOT term-wise nonneg")
    nRppneg = int(np.sum([r["Rpp"] < 0 for r in rows]))
    print(f"  R'' < 0 on {nRppneg}/{N} graphs (so R'' alone is not the certificate)")

    main.rows = rows; main.hard = hard


if __name__ == "__main__":
    main()
