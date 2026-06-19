"""
PART 1 — direct-B vs aggregate-Poincare margin test.

B (the true lift bound)  <=>  T <= RHS = lam(2 fDf - lam - S^2/m).
Using T+Open = sum[sigma_v-(d_v-lam)^2]f_v^2, this is equivalent to

    B  <=>  Open >= target_B := -A + lam S^2/m            (A = Cov_L(d,f^2))

while aggregate_triangle_poincare (T <= lam fDf, sufficient for B in regime (i)) is

    AP <=>  Open >= target_AP := lam fAf - A              (fAf = fDf - lam)

Difference  target_AP - target_B = lam(fAf - S^2/m) = lam(fDf - lam - S^2/m) = -Required/...
  >= 0 in regime (i) (Required<=0), < 0 in regime (ii).

S = sum_v d_v f_v, m = |E|.  Run: python conjecture_B_direct_bypass.py
"""
import numpy as np
import networkx as nx
from conjecture_B_nodal_decomposition import corpus
from conjecture_B_same_sign_reservoir import glue, chain_cliques


def graph_quant(fam, G):
    nodes = list(G.nodes())
    idx = {u: i for i, u in enumerate(nodes)}
    L = nx.laplacian_matrix(G, nodelist=nodes).toarray().astype(float)
    d = L.diagonal().copy()
    A = np.diag(d) - L
    m = G.number_of_edges()
    ev, V = np.linalg.eigh(L)
    lam = ev[1]
    f = V[:, 1] / np.linalg.norm(V[:, 1])
    f2 = f * f
    A2 = A @ A
    M = A * A2
    P = A2 - np.diag(d) - M
    L_M = np.diag(M.sum(1)) - M
    L_P = np.diag(P.sum(1)) - P
    T = float(f @ L_M @ f)
    Open = float(f @ L_P @ f)
    fDf = float(d @ f2)
    fAf = float(f @ A @ f)               # = fDf - lam
    S = float(d @ f)
    # 𝒜 = Cov_L(d,f²) = dᵀL(f²) = sum over UNORDERED edges (no 1/2; the 1/2 is for the
    # ordered double sum). Each edge counted once below.
    Acal = float(sum((d[idx[u]] - d[idx[v]]) * (f2[idx[u]] - f2[idx[v]])
                     for u, v in G.edges()))
    S2m = S * S / m
    target_B = -Acal + lam * S2m
    target_AP = lam * fAf - Acal
    Required = lam * (lam + S2m - fDf)
    RHS = lam * (2 * fDf - lam - S2m)     # direct lift-B RHS = lam(fᵀQf - S²/m)
    return dict(fam=fam, n=len(nodes), lam=lam, Open=Open, T=T, RHS=RHS, fDf=fDf, fAf=fAf,
                S=S, m=m, Acal=Acal, S2m=S2m, target_B=target_B, target_AP=target_AP,
                Required=Required)


def all_graphs():
    gs = [("corpus", G) for _, G in corpus()]
    gs += [("barbell", nx.barbell_graph(m, Lb)) for m in (5, 20, 40, 80) for Lb in (0, 1, 3)]
    gs += [("glue", glue(a, b)) for a, b in ((5, 5), (20, 20), (40, 40), (3, 60))]
    gs += [("chain", chain_cliques(m, k)) for m, k in ((10, 2), (20, 2), (40, 2), (15, 4))]
    out = []
    for fam, G in gs:
        if G.number_of_nodes() < 4 or not nx.is_connected(G):
            continue
        ev = np.linalg.eigvalsh(nx.laplacian_matrix(G, nodelist=list(G.nodes()))
                                .toarray().astype(float))
        if ev[1] < 1e-9:
            continue
        out.append((fam, G))
    return out


def main():
    data = [graph_quant(fam, G) for fam, G in all_graphs()]
    ng = len(data)
    print(f"{ng} graphs\n")

    tol = 1e-7
    # consistency: Open>=target_B  <=>  T<=RHS  (direct lift-B). Verify they agree exactly.
    resid = max(abs((q['Open'] - q['target_B']) - (q['RHS'] - q['T'])) for q in data)
    okB = sum(1 for q in data if q['Open'] >= q['target_B'] - tol)
    okT = sum(1 for q in data if q['T'] <= q['RHS'] + tol)
    okAP = sum(1 for q in data if q['Open'] >= q['target_AP'] - tol)
    print(f"CONSISTENCY (Open-target_B)==(RHS-T) residual : {resid:.2e}")
    print(f"DIRECT lift-B:  T <= RHS                   : {okT}/{ng}")
    print(f"        equiv:  Open >= target_B           : {okB}/{ng}")
    print(f"AGG Poincare:   Open >= target_AP (T<=λfDf): {okAP}/{ng}")
    rel = [(q['fam'], q['n'], q['lam'], q['T'] / q['RHS']) for q in data
           if q['T'] > q['RHS'] + tol]
    if rel:
        print(f"  lift-B FAILURES (T>RHS): {rel}")

    # ---- Q1: target_B vs target_AP, margin gained ----
    print("\n" + "=" * 72)
    print("Q1 — target_B vs target_AP  (margin = target_AP - target_B = lam(fAf - S^2/m))")
    print("=" * 72)
    diff = np.array([q['target_AP'] - q['target_B'] for q in data])
    print(f"  target_AP - target_B : min={diff.min():+.4f} median={np.median(diff):+.4f} "
          f"max={diff.max():+.4f}")
    print(f"  >= 0 (direct is easier, regime i): {int((diff >= -tol).sum())}/{ng}")
    rel = np.array([(q['target_AP'] - q['target_B']) / abs(q['target_AP'])
                    for q in data if abs(q['target_AP']) > 1e-9])
    print(f"  relative margin (target_AP-target_B)/|target_AP|: median={np.median(rel):+.3f}")

    # ---- Q2: target_B <= 0 (B trivial, Open>=0 suffices) ----
    print("\n" + "=" * 72)
    print("Q2 — graphs with target_B <= 0  (B trivially true since Open >= 0)")
    print("=" * 72)
    trivB = [q for q in data if q['target_B'] <= tol]
    print(f"  target_B <= 0 : {len(trivB)}/{ng}")
    from collections import Counter
    cfam = Counter(q['fam'] for q in trivB)
    print(f"  by family: {dict(cfam)}")
    trivAP = [q for q in data if q['target_AP'] <= tol]
    print(f"  (compare) target_AP <= 0 : {len(trivAP)}/{ng}")
    # also: how many have target_B<=0 due to A>=lam S^2/m
    print(f"  target_B<=0 needs A >= lam S^2/m (A>0): A>0 graphs = "
          f"{sum(1 for q in data if q['Acal'] > tol)}")

    # ---- Q3: tightness on nontrivial graphs ----
    print("\n" + "=" * 72)
    print("Q3 — for target_B > 0:  Open/target_B  vs  Open/target_AP")
    print("=" * 72)
    ntB = [q for q in data if q['target_B'] > tol]
    rB = np.array([q['Open'] / q['target_B'] for q in ntB])
    print(f"  target_B>0: {len(ntB)} graphs")
    print(f"  Open/target_B  : min={rB.min():.4f} median={np.median(rB):.3f} max={rB.max():.3f}")
    ntAP = [q for q in data if q['target_AP'] > tol]
    rAP = np.array([q['Open'] / q['target_AP'] for q in ntAP])
    print(f"  Open/target_AP : min={rAP.min():.4f} median={np.median(rAP):.3f} "
          f"(on {len(ntAP)} graphs with target_AP>0)")
    # head to head on graphs where BOTH > 0
    both = [q for q in data if q['target_B'] > tol and q['target_AP'] > tol]
    rBb = np.array([q['Open'] / q['target_B'] for q in both])
    rAPb = np.array([q['Open'] / q['target_AP'] for q in both])
    print(f"  head-to-head ({len(both)} graphs, both targets>0):")
    print(f"    min Open/target_B  = {rBb.min():.4f}   min Open/target_AP = {rAPb.min():.4f}")
    print(f"    median ratio of ratios (B looser by) = {np.median(rBb/rAPb):.3f}x")
    worst = min(both, key=lambda q: q['Open'] / q['target_B'])
    print(f"  TIGHTEST direct-B graph: fam={worst['fam']} n={worst['n']} "
          f"Open/target_B={worst['Open']/worst['target_B']:.4f} "
          f"lam={worst['lam']:.3f} A={worst['Acal']:.3f} S2m={worst['S2m']:.3f}")

    # ---- Q4: which graphs NEED Open>0 (target_B>0) ----
    print("\n" + "=" * 72)
    print("Q4 — classification: B needs Open>0 iff target_B>0")
    print("=" * 72)
    need = [q for q in ntB]
    famneed = Counter(q['fam'] for q in need)
    print(f"  NEED Open>0 (target_B>0): {len(need)}/{ng}  by family: {dict(famneed)}")
    print(f"  of these, regime (i) Required<=0: {sum(1 for q in need if q['Required']<=tol)}")
    print(f"            regime (ii) Required>0 : {sum(1 for q in need if q['Required']>tol)}")
    # regime split overall
    reg2 = [q for q in data if q['Required'] > tol]
    print(f"  regime (ii) Required>0 overall: {len(reg2)}/{ng}; among them target_B<=0: "
          f"{sum(1 for q in reg2 if q['target_B']<=tol)}")

    print("\n" + "=" * 72)
    print("SUMMARY")
    print("=" * 72)
    print(f"  direct-B closes trivially (Open>=0) on {len(trivB)}/{ng}; "
          f"needs Open>0 on {len(need)}/{ng}.")
    print(f"  minimum slack on direct B: Open/target_B >= {rB.min():.4f} "
          f"(vs Open/target_AP >= {rAP.min():.4f}).")


if __name__ == "__main__":
    main()
