"""
Extending the regular proof to irregular graphs.

Correct target: B <=> T <= lam2 G,  G = Sum h^2 - S^2/m = m Var_E(h),  T = Sum t_e g_e^2.
Regular proof key: t_e <= d-1, Sum g^2 = lam2, G = 2d - lam2 (S=0).
Irregular candidate (min-degree relaxation): replace t_e by min(d_a,d_b)-1.

TASK2 B2_LHS = Sum_e (min(d_a,d_b)-1) g_e^2  vs  target = lam2 G.  (since t_e<=min-1, this >= T.)
TASK3 t_avg = (Sum t_e)/m ;  T <= t_avg lam2 ?  t_avg <= G ?
TASK4 slack Sum_e [min(d_a,d_b)-1 - t_e] g_e^2  >= 0 ; both relaxations vs lam2 G.
Run: python conjecture_B_regular_extension.py
"""
import numpy as np
import networkx as nx
from conjecture_B_nodal_decomposition import corpus
from conjecture_B_same_sign_reservoir import glue, chain_cliques


def edge_data(fam, G):
    nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}
    L = nx.laplacian_matrix(G, nodelist=nodes).toarray().astype(float)
    d = L.diagonal().copy(); A = np.diag(d) - L
    m = G.number_of_edges()
    w, U = np.linalg.eigh(L); lam = w[1]; f = U[:, 1].copy()
    A2 = A @ A
    es = [(idx[a], idx[b]) for a, b in G.edges()]
    t = np.array([A2[a, b] for a, b in es])
    mind = np.array([min(d[a], d[b]) for a, b in es])
    g2 = np.array([(f[a] - f[b]) ** 2 for a, b in es])
    he = np.array([f[a] + f[b] for a, b in es])
    S = float(d @ f)
    G_var = float((he ** 2).sum() - S ** 2 / m)
    T = float((t * g2).sum())
    B2 = float(((mind - 1) * g2).sum())
    t_avg = float(t.sum() / m)
    return dict(fam=fam, n=len(nodes), m=m, lam=lam, T=T, G=G_var, B2=B2, t_avg=t_avg,
                t=t, mind=mind, g2=g2, dmax=float(d.max()), dmin=float(d.min()))


def all_graphs():
    gs = [("corpus", G) for _, G in corpus()]
    gs += [("barbell", nx.barbell_graph(mm, Lb)) for mm in (5, 20, 40, 80) for Lb in (0, 1, 3)]
    gs += [("glue", glue(a, b)) for a, b in ((5, 5), (20, 20), (40, 40), (3, 60))]
    gs += [("chain", chain_cliques(mm, k)) for mm, k in ((10, 2), (20, 2), (40, 2), (15, 4))]
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
    data = [edge_data(fam, G) for fam, G in all_graphs()]
    ng = len(data); tol = 1e-7

    print("=" * 74)
    print("TASK 2 — min-degree relaxation  B2 = Sum (min(d_a,d_b)-1) g^2  <=  lam2 G ?")
    print("=" * 74)
    ok = sum(1 for q in data if q['B2'] <= q['lam'] * q['G'] + tol)
    rat = np.array([q['B2'] / (q['lam'] * q['G']) for q in data if q['lam'] * q['G'] > 1e-12])
    print(f"  B2 <= lam2 G : {ok}/{ng}  (B2/(lam2 G) min={rat.min():.3f} median={np.median(rat):.3f} "
          f"max={rat.max():.4f})")
    print(f"  (B2 >= T always since t_e <= min-1; this is the degree-only relaxation = B2' route)")
    worst = max(data, key=lambda q: q['B2'] / (q['lam'] * q['G']) if q['lam'] * q['G'] > 1e-12 else 0)
    print(f"  worst graph: fam={worst['fam']} n={worst['n']} dmax={worst['dmax']:.0f} "
          f"dmin={worst['dmin']:.0f} ratio={worst['B2']/(worst['lam']*worst['G']):.4f}")
    # spotlight hard families
    for fam in ("barbell", "glue", "chain"):
        sub = [q for q in data if q['fam'] == fam]
        if sub:
            r = np.array([q['B2'] / (q['lam'] * q['G']) for q in sub if q['lam'] * q['G'] > 1e-12])
            print(f"    {fam:8s}: n={len(sub):3d} B2/(lam2 G) max={r.max():.4f} (all<=1: "
                  f"{all(q['B2'] <= q['lam']*q['G']+tol for q in sub)})")

    print("\n" + "=" * 74)
    print("TASK 3 — average triangle count bound")
    print("=" * 74)
    okT = sum(1 for q in data if q['T'] <= q['t_avg'] * q['lam'] + tol)
    okTG = sum(1 for q in data if q['t_avg'] <= q['G'] + tol)
    print(f"  T <= t_avg * lam2 (Chebyshev anti-corr) : {okT}/{ng}")
    print(f"  t_avg <= G                              : {okTG}/{ng}")
    comb = sum(1 for q in data if q['T'] <= q['t_avg']*q['lam']+tol and q['t_avg'] <= q['G']+tol)
    print(f"  both (=> T <= t_avg lam2 <= G lam2 = lam2 G) : {comb}/{ng}")
    rt = np.array([q['T'] / (q['t_avg'] * q['lam']) for q in data if q['t_avg']*q['lam'] > 1e-12])
    print(f"  T/(t_avg lam2): min={rt.min():.3f} median={np.median(rt):.3f} max={rt.max():.3f}")

    print("\n" + "=" * 74)
    print("TASK 4 — relaxations vs lam2 G, and the slack")
    print("=" * 74)
    okTrue = sum(1 for q in data if q['T'] <= q['lam'] * q['G'] + tol)
    print(f"  T   <= lam2 G  (true conjecture)         : {okTrue}/{ng}")
    print(f"  B2  <= lam2 G  (min-deg relaxation)      : {ok}/{ng}")
    slack_neg = sum(1 for q in data if ((q['mind'] - 1 - q['t']) * q['g2']).sum() < -tol)
    print(f"  slack Sum (min-1 - t_e) g^2 >= 0 (t_e<=min-1): {ng - slack_neg}/{ng}")
    # how much does the relaxation cost? B2 - T over lam2 G
    cost = np.array([(q['B2'] - q['T']) / (q['lam'] * q['G']) for q in data
                     if q['lam'] * q['G'] > 1e-12])
    print(f"  relaxation cost (B2-T)/(lam2 G): median={np.median(cost):.3f} max={cost.max():.3f}")

    print("\n" + "=" * 74)
    print("SUMMARY")
    print("=" * 74)
    print(f"  Min-degree relaxation B2=Sum(min(d_a,d_b)-1)g^2 <= lam2 G : {ok}/{ng} "
          f"(max ratio {rat.max():.3f}).")
    print("  => if it holds 580/580, the IRREGULAR proof reduces to the degree-only inequality")
    print("     Sum_e (min(d_a,d_b)-1) g_e^2 <= lam2 (Sum h^2 - S^2/m), with NO triangle counts.")
    print(f"  Chebyshev route T<=t_avg lam2 holds {okT}/{ng}; t_avg<=G {okTG}/{ng}.")


if __name__ == "__main__":
    main()
