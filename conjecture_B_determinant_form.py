"""
Determinant formulation of Conjecture B.

det(M_low) = (4 lam2/n)(m f^TMf - lam2 S^2) >= 0,  M=lam2 Q - L_M, Q=D+A, S=sum d_v f_v.
Since f^TMf = lam2 f^TQf - T  (f^TQf=2fDf-lam2, T triangle energy):
   D := m f^TMf - lam2 S^2 = lam2 (m f^TQf - S^2) - m T.

KEY: the lift h = B^T f (unsigned incidence), h_e = f_a+f_b for edge e={a,b}.
   ||h||^2 = f^TQf = sum_{e}(f_a+f_b)^2     (signless-Laplacian quadratic form)
   <1_E, h> = sum_e (f_a+f_b) = sum_v d_v f_v = S
   G := m f^TQf - S^2 = m||h||^2 - <1_E,h>^2 = GRAM det of {h, 1_E}
      = 1/2 sum_{e,e'} (h_e - h_e')^2  (Lagrange identity)  = m^2 Var_E(h)  >= 0  (Cauchy-Schwarz)

Hence  D = lam2 * G - m * T  =  lam2 * (manifest Cauchy-Schwarz/variance term)  -  m * (triangle energy).
Conjecture  <=>  lam2 * G >= m * T  <=>  T <= lam2 (f^TQf - S^2/m) = lam2 ||h_perp||^2  (lift bound).

So D is NOT a single covariance determinant Var.Var - Cov^2; it is lam2 * (a Cauchy-Schwarz Gram
determinant, the edge-lift variance) MINUS m*T.  Run: python conjecture_B_determinant_form.py
"""
import numpy as np
import networkx as nx
from conjecture_B_nodal_decomposition import corpus
from conjecture_B_same_sign_reservoir import glue, chain_cliques


def graph_quant(fam, G):
    nodes = list(G.nodes())
    n = len(nodes); idx = {u: i for i, u in enumerate(nodes)}
    L = nx.laplacian_matrix(G, nodelist=nodes).toarray().astype(float)
    d = L.diagonal().copy(); A = np.diag(d) - L
    m = G.number_of_edges()
    w, U = np.linalg.eigh(L); lam = w[1]; f = U[:, 1].copy()
    Q = np.diag(d) + A
    A2 = A @ A; Mtri = A * A2; L_M = np.diag(Mtri.sum(1)) - Mtri
    Mop = lam * Q - L_M
    fDf = float(d @ (f * f)); S = float(d @ f)
    fQf = float(f @ Q @ f); fMf = float(f @ Mop @ f); T = float(f @ L_M @ f)
    # edge-lift h
    edges = [(idx[a], idx[b]) for a, b in G.edges()]
    h = np.array([f[a] + f[b] for a, b in edges])
    Det = m * fMf - lam * S ** 2
    G_gram = m * fQf - S ** 2
    return dict(fam=fam, n=n, m=m, lam=lam, f=f, fDf=fDf, S=S, fQf=fQf, fMf=fMf, T=T,
                h=h, Det=Det, G_gram=G_gram)


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
    data = [graph_quant(fam, G) for fam, G in all_graphs()]
    ng = len(data)
    print(f"{ng} graphs\n")

    def mx(fn):
        return max(abs(fn(q)) for q in data)

    print("=" * 74)
    print("EXACT identities (residuals over all graphs)")
    print("=" * 74)
    # signless-Laplacian QF: f^TQf = sum_e (f_a+f_b)^2
    r_qf = mx(lambda q: q['fQf'] - float((q['h'] ** 2).sum()))
    # <1_E,h> = S
    r_s = mx(lambda q: q['S'] - float(q['h'].sum()))
    # G = m f^TQf - S^2  =  Gram det of {h,1_E}
    r_g = mx(lambda q: q['G_gram'] - (q['m'] * float((q['h'] ** 2).sum()) - float(q['h'].sum()) ** 2))
    # determinant core: D = lam2 G - m T
    r_det = mx(lambda q: q['Det'] - (q['lam'] * q['G_gram'] - q['m'] * q['T']))
    print(f"  f^TQf == sum_e (f_a+f_b)^2          : {r_qf:.2e}")
    print(f"  <1_E,h> == S = sum_v d_v f_v        : {r_s:.2e}")
    print(f"  G := m f^TQf - S^2 == Gram(h,1_E)   : {r_g:.2e}")
    print(f"  D := m f^TMf - lam2 S^2 == lam2*G - m*T : {r_det:.2e}")

    # Lagrange / variance SOS for G  (verify on small graphs only; O(m^2))
    print("\n  Lagrange SOS  G == 1/2 sum_{e,e'} (h_e - h_e')^2  (small graphs, m<=400):")
    r_lag = 0.0; ncheck = 0
    for q in data:
        if len(q['h']) <= 400:
            hh = q['h']
            sos = 0.5 * float(((hh[:, None] - hh[None, :]) ** 2).sum())
            r_lag = max(r_lag, abs(q['G_gram'] - sos)); ncheck += 1
    print(f"    max residual {r_lag:.2e}  ({ncheck} graphs)")
    # variance form
    r_var = 0.0
    for q in data:
        m = q['m']; hh = q['h']
        var = float((hh ** 2).mean()) - float(hh.mean()) ** 2
        r_var = max(r_var, abs(q['G_gram'] - m ** 2 * var))
    print(f"  G == m^2 * Var_E(h)  (edge-lift variance) : residual {r_var:.2e}")

    print("\n" + "=" * 74)
    print("DECOMPOSITION:  D = lam2 * G  -  m * T")
    print("=" * 74)
    Gs = np.array([q['G_gram'] for q in data]); Ts = np.array([q['T'] for q in data])
    lams = np.array([q['lam'] for q in data]); ms = np.array([q['m'] for q in data])
    Dets = np.array([q['Det'] for q in data])
    print(f"  G (Cauchy-Schwarz/variance, >=0): min={Gs.min():.4f} (all >=0: {int((Gs>=-1e-7).sum())}/{ng})")
    print(f"  m*T (triangle energy, >=0)      : min={(ms*Ts).min():.4f}")
    print(f"  D = lam2*G - m*T                : min={Dets.min():.4f} (all >=0: {int((Dets>=-1e-7).sum())}/{ng})")
    # how much of lam2*G does m*T eat?  ratio m*T / (lam2*G)
    ratio = np.array([ms[i]*Ts[i] / (lams[i]*Gs[i]) for i in range(ng) if lams[i]*Gs[i] > 1e-12])
    print(f"  m*T / (lam2*G) (must be <=1): min={ratio.min():.3f} median={np.median(ratio):.3f} "
          f"max={ratio.max():.4f}")
    print(f"  => conjecture <=> m*T <= lam2*G; max ratio {ratio.max():.4f} < 1 (margin "
          f"{(1-ratio.max())*100:.2f}% at tightest).")

    print("\n" + "=" * 74)
    print("Is D a single covariance determinant Var.Var - Cov^2 ?")
    print("=" * 74)
    print("  NO. D = lam2*G - m*T where G=Gram(h,1_E)=m^2 Var_E(h) is a Cauchy-Schwarz determinant")
    print("  (manifestly >=0), but m*T (triangle energy) is SUBTRACTED, not a second variance.")
    print("  The manifestly-nonneg PART is lam2*G (edge-lift variance); the obstruction is the")
    print("  triangle energy T eating into it. Closing D>=0 = the projected lift bound T<=lam2||h_perp||^2.")

    print("\n" + "=" * 74)
    print("SUMMARY")
    print("=" * 74)
    print("  D = m f^TMf - lam2 S^2 = lam2 * G - m * T,  G = m f^TQf - S^2 = 1/2 sum_{e,e'}(h_e-h_e')^2")
    print("    = m^2 Var_E(f_a+f_b) >= 0 (Cauchy-Schwarz/Lagrange).  Conjecture <=> lam2 G >= m T.")


if __name__ == "__main__":
    main()
