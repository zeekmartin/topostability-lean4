"""
Lower bound for R'' in the TYPE A deg-2 core-gap model, to match |C_attach| <= C Delta/gamma f_v0^2.

R'' = lam2(fDf - lam2 + 1 - S^2/m).  Goal: R'' >= c Delta/gamma f_v0^2 with c >= C  => gap>=0.

Tested quantities (per core H, deg-2 vertex attached at 0,1):
  rho_R = R'' * gamma / (Delta f_v0^2)   (R'' lower-bound constant)
  rho_C = |C_attach| * gamma / (Delta f_v0^2)   (|C_attach| upper-bound constant)
  leading: R''/f_v0^2 ~ 2(1 - dbar/(n)) ?   |C_attach|/f_v0^2 ~ ?   gap/f_v0^2 -> 0 ?
Run: python conjecture_B_Rpp_lower_bound_typeA.py
"""
import numpy as np
import networkx as nx
from conjecture_B_core_gap_stability import attach_deg2


def analyze(H):
    G, v0lbl = attach_deg2(H)
    nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}; n = len(nodes)
    A = nx.to_numpy_array(G, nodelist=nodes); d = A.sum(1); L = np.diag(d) - A
    ev, U = np.linalg.eigh(L); lam = ev[1]; f = U[:, 1]; f = f / np.linalg.norm(f)
    v0 = idx[v0lbl]
    if f[v0] < 0:
        f = -f
    m = G.number_of_edges(); S = float(d @ f); fDf = float(d @ (f * f))
    fv0 = float(f[v0]); fa = float(f[idx[0]]); fb = float(f[idx[1]])
    Hc = nx.convert_node_labels_to_integers(H)
    evH = np.linalg.eigvalsh(nx.laplacian_matrix(Hc, nodelist=list(Hc.nodes())).toarray().astype(float))
    gamma = float(evH[1])
    dcore = np.array([d[idx[u]] - (1 if u in (0, 1) else 0) for u in range(v0lbl)])
    Delta = float(dcore.max()); dbar = float(dcore.mean())
    Catt = 0.0
    for u, v in G.edges():
        ia, ib = idx[u], idx[v]
        if ia == v0 or ib == v0:
            if d[ia] > d[ib]:
                Catt += (d[ia] - d[ib]) * f[ia] * (f[ia] - f[ib])
            elif d[ib] > d[ia]:
                Catt += (d[ib] - d[ia]) * f[ib] * (f[ib] - f[ia])
    Rpp = lam * (fDf - lam + 1 - S ** 2 / m)
    return dict(n=n, lam=lam, gamma=gamma, Delta=Delta, dbar=dbar, fv0=fv0, fa=fa, fb=fb,
                Rpp=Rpp, Catt=Catt, fDf=fDf, S=S, m=m)


def cores():
    out = []
    for m in [100, 300, 600]:
        out.append((f"K_{m}", nx.complete_graph(m)))
        for q in [0.2, 0.3, 0.5, 0.65, 0.8, 0.9]:
            out.append((f"gnp({m},{q})", nx.gnp_random_graph(m, q, seed=1)))
        for frac in (0.2, 0.4):
            r = max(3, int(frac * m))
            out.append((f"randreg({m},{r})", nx.random_regular_graph(r, m, seed=2)))
    return out


def main():
    data = []
    for name, H in cores():
        if H.number_of_nodes() < 4 or not nx.is_connected(H):
            continue
        data.append((name, analyze(H)))

    print("=" * 92)
    print("R'' vs |C_attach| in Delta/gamma f_v0^2 units  (rho = quantity * gamma/(Delta f_v0^2))")
    print("=" * 92)
    print(f"  {'core':16s} {'q≈dbar/n':>9} {'R''/fv0²':>9} {'|Catt|/fv0²':>11} {'gap/fv0²':>9} "
          f"{'rho_R':>7} {'rho_C':>7} {'rho_R>rho_C':>11}")
    rhoR = []; rhoC = []
    for name, q in data:
        f2 = q['fv0'] ** 2
        gap = q['Rpp'] + q['Catt']
        rR = q['Rpp'] * q['gamma'] / (q['Delta'] * f2)
        rC = abs(q['Catt']) * q['gamma'] / (q['Delta'] * f2)
        rhoR.append(rR); rhoC.append(rC)
        qd = q['dbar'] / q['n']
        print(f"  {name:16s} {qd:9.3f} {q['Rpp']/f2:9.4f} {abs(q['Catt'])/f2:11.4f} {gap/f2:9.5f} "
              f"{rR:7.3f} {rC:7.3f} {str(rR>rC):>11}")
    rhoR = np.array(rhoR); rhoC = np.array(rhoC)

    print("\n" + "=" * 92)
    print("CAN SEPARATE BOUNDS WORK?  (need inf rho_R >= sup rho_C for a universal c)")
    print("=" * 92)
    print(f"  inf rho_R = {rhoR.min():.3f}   sup rho_C = {rhoC.max():.3f}   "
          f"=> universal separation: {'YES' if rhoR.min() >= rhoC.max() else 'NO'}")
    print(f"  per-graph rho_R > rho_C : {int((rhoR > rhoC - 1e-9).sum())}/{len(data)} "
          f"(gap>0 per graph), but NOT via a universal Delta/gamma constant.")

    print("\n" + "=" * 92)
    print("LEADING ORDER:  R''/f_v0^2 ~ 2(1 - q),  |C_attach|/f_v0^2 ~ ? ,  gap/f_v0^2 -> 0")
    print("=" * 92)
    for name, q in data:
        if name.startswith("gnp"):
            f2 = q['fv0'] ** 2; qd = q['dbar'] / q['n']
            print(f"  {name:16s} 2(1-q)={2*(1-qd):.3f}  R''/fv0²={q['Rpp']/f2:.3f}  "
                  f"|Catt|/fv0²={abs(q['Catt'])/f2:.3f}  gap/fv0²={(q['Rpp']+q['Catt'])/f2:.4f}")

    print("\n" + "=" * 92)
    print("SUMMARY")
    print("=" * 92)
    print("  R''/f_v0^2 ~ 2(1-q) and |C_attach|/f_v0^2 track each other (both Theta(1)); their")
    print("  difference gap/f_v0^2 -> 0. So R'' and |C_attach| MATCH at leading order: a separate")
    print(f"  lower bound R'' >= c Delta/gamma f_v0^2 with c>=sup rho_C FAILS (inf rho_R={rhoR.min():.2f}"
          f" < sup rho_C={rhoC.max():.2f}). gap>0 is per-graph (R'' and C_attach correlated via f_a),")
    print("  not separable by universal constants -> need a JOINT bound on R''+C_attach.")


if __name__ == "__main__":
    main()
