"""
Spectral separation: why does the Fiedler f=u2 avoid M's negative cone?

M = lam2 (D+A) - L_t = lam2 Q - L_M   (Q=D+A signless Laplacian, L_M=triangle Laplacian).
f^T M f = 2 lam2 fDf - lam2^2 - T.
Relations:  f^T M f = -Q_slack + lam2 fAf  (>= -Q_slack >= 0),  fAf=fDf-lam2.
2x2 low-frequency block of M in {u1=const, u2=f}:
   M_low = [[<u1,Mu1>, <u1,Mu2>],[<u2,Mu1>, <u2,Mu2>]]
   <u1,Mu1> = lam2 <u1,Qu1>   (L_M u1=0)
   <u1,Mu2> = lam2 <u1,Qf> = lam2 * 2S/sqrt(n)   (S=sum d_v f_v)
   <u2,Mu2> = f^T M f
   det(M_low) = (4 lam2/n)(m f^TMf - lam2 S^2)  >=0  <=>  f^TMf >= lam2 S^2/m  <=> LIFT-B.

TASK1 M's negative eigenvectors in L's eigenbasis (overlap with u2, hi/lo-freq mass).
TASK2 the 2x2 Fiedler block of M; M_low PSD <=> B (lift bound).
TASK3 is V-(M) _|_ u2 provable?  (numeric evidence)
TASK4 #negative eigenvalues of M; Weyl/interlacing.
Run: python conjecture_B_spectral_orthogonality.py
"""
import numpy as np
import networkx as nx
from conjecture_B_nodal_decomposition import corpus
from conjecture_B_same_sign_reservoir import glue, chain_cliques


def graph_quant(fam, G):
    nodes = list(G.nodes())
    n = len(nodes)
    L = nx.laplacian_matrix(G, nodelist=nodes).toarray().astype(float)
    d = L.diagonal().copy()
    A = np.diag(d) - L
    m = G.number_of_edges()
    w, U = np.linalg.eigh(L)               # ascending; U[:,0]=const, U[:,1]=Fiedler
    lam = w[1]
    f = U[:, 1].copy()                     # unit Fiedler (eigh returns orthonormal)
    Q = np.diag(d) + A
    A2 = A @ A
    Mtri = A * A2
    L_M = np.diag(Mtri.sum(1)) - Mtri
    Mop = lam * Q - L_M                     # the indefinite operator
    fDf = float(d @ (f * f)); S = float(d @ f)
    fMf = float(f @ Mop @ f)
    T = float(f @ L_M @ f)
    return dict(fam=fam, n=n, m=m, lam=lam, L=L, U=U, w=w, f=f, Q=Q, L_M=L_M, Mop=Mop,
                fDf=fDf, S=S, fMf=fMf, T=T, d=d)


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
    tol = 1e-7

    # ---------------- TASK 1 ----------------
    print("=" * 76)
    print("TASK 1 — M's negative eigenvectors expressed in L's eigenbasis")
    print("=" * 76)
    max_ov_u2 = []        # max |<w_j,u2>|^2 over M-negative w_j, per graph
    min_hifreq = []       # min high-freq mass of M-negative vectors
    neg_u2_mass = []      # total ||P_{V-} u2||^2 (Fiedler mass in M's negative subspace)
    neg_lo_mass = []      # mean low-freq (u1,u2) mass of M-negative vectors
    for q in data:
        U = q['U']; mu, W = np.linalg.eigh(q['Mop'])
        neg = mu < -tol
        if not neg.any():
            max_ov_u2.append(0.0); min_hifreq.append(1.0); neg_u2_mass.append(0.0)
            neg_lo_mass.append(0.0); continue
        Wn = W[:, neg]                       # columns = M-negative eigenvectors
        coeff = U.T @ Wn                     # coeff[k,j] = <u_k, w_j>
        ov_u2 = coeff[1, :] ** 2
        lo = coeff[0, :] ** 2 + coeff[1, :] ** 2
        hi = (coeff[2:, :] ** 2).sum(0)
        max_ov_u2.append(float(ov_u2.max()))
        min_hifreq.append(float(hi.min()))
        neg_u2_mass.append(float(ov_u2.sum()))    # = ||P_{V-} u2||^2 (orthonormal w_j)
        neg_lo_mass.append(float(lo.mean()))
    max_ov_u2 = np.array(max_ov_u2); min_hifreq = np.array(min_hifreq)
    neg_u2_mass = np.array(neg_u2_mass); neg_lo_mass = np.array(neg_lo_mass)
    print(f"  max |<w_j,u2>|^2 over M-neg vectors : median={np.median(max_ov_u2):.4f} "
          f"max={max_ov_u2.max():.4f}")
    print(f"  min high-freq mass of M-neg vectors : median={np.median(min_hifreq):.4f} "
          f"min={min_hifreq.min():.4f}")
    print(f"  ||P_{{V-}} u2||^2 (Fiedler mass IN M's neg subspace): "
          f"median={np.median(neg_u2_mass):.4f} max={neg_u2_mass.max():.4f}")
    print(f"  fraction of graphs with ||P_{{V-}}u2||^2 < 0.01 : "
          f"{int((neg_u2_mass<0.01).sum())}/{ng}")
    print("  => if ||P_{V-}u2||^2 is NOT ~0, f is NOT orthogonal to the neg cone; the protection")
    print("     is then by WEIGHTING (small |mu_j| on the modes f overlaps), tested in TASK 2/4.")

    # ---------------- TASK 2 ----------------
    print("\n" + "=" * 76)
    print("TASK 2 — the 2x2 low-frequency block M_low and its PSD <=> B")
    print("=" * 76)
    blockpsd = 0; liftB = 0; agree = 0
    detmin = []
    for q in data:
        U = q['U']; Mop = q['Mop']
        u1 = U[:, 0]; u2 = U[:, 1]
        a11 = float(u1 @ Mop @ u1); a12 = float(u1 @ Mop @ u2); a22 = float(u2 @ Mop @ u2)
        det = a11 * a22 - a12 ** 2
        detmin.append(det)
        psd = (a11 >= -tol) and (a22 >= -tol) and (det >= -tol)
        # lift-B: f^T M f >= lam2 S^2/m
        lb = q['fMf'] >= q['lam'] * q['S'] ** 2 / q['m'] - tol
        if psd: blockpsd += 1
        if lb: liftB += 1
        if psd == lb: agree += 1
    detmin = np.array(detmin)
    print(f"  M_low PSD (2x2 Fiedler block)        : {blockpsd}/{ng}")
    print(f"  lift-B  f^TMf >= lam2 S^2/m          : {liftB}/{ng}")
    print(f"  M_low PSD  <=>  lift-B agree         : {agree}/{ng}")
    print(f"  det(M_low) : min={detmin.min():.4e} median={np.median(detmin):.4e}")
    print("  => CONJECTURE B = positive-semidefiniteness of the 2x2 (u1,u2) block of M.")
    print("     The off-diagonal <u1,Mu2>=lam2*2S/sqrt(n) is exactly what produces the S^2/m term.")
    # verify the algebraic forms of the block entries
    # sign-normalise u1 (eigh returns +-1/sqrt(n)); compare magnitudes (det is sign-invariant)
    r11 = max(abs(float(q['U'][:, 0] @ q['Mop'] @ q['U'][:, 0])
                  - q['lam'] * float(q['U'][:, 0] @ q['Q'] @ q['U'][:, 0])) for q in data)
    r12 = max(abs(abs(float(q['U'][:, 0] @ q['Mop'] @ q['U'][:, 1]))
                  - q['lam'] * 2 * abs(q['S']) / np.sqrt(q['n'])) for q in data)
    print(f"  check <u1,Mu1>=lam2<u1,Qu1> resid {r11:.2e}; |<u1,Mu2>|=lam2*2|S|/sqrt(n) resid {r12:.2e}")

    # ---------------- TASK 3 ----------------
    print("\n" + "=" * 76)
    print("TASK 3 — is V-(M) _|_ u2 ?  (numeric)")
    print("=" * 76)
    print(f"  ||P_{{V-}} u2||^2 : min={neg_u2_mass.min():.4f} median={np.median(neg_u2_mass):.4f} "
          f"max={neg_u2_mass.max():.4f}")
    # weighted: f^TMf = sum_j mu_j |<f,w_j>|^2 ; negative contribution vs positive
    negcontrib = []; poscontrib = []
    for q in data:
        mu, W = np.linalg.eigh(q['Mop'])
        c = (q['f'] @ W) ** 2
        negcontrib.append(float((mu[mu < 0] * c[mu < 0]).sum()))
        poscontrib.append(float((mu[mu >= 0] * c[mu >= 0]).sum()))
    negcontrib = np.array(negcontrib); poscontrib = np.array(poscontrib)
    print(f"  f's NEGATIVE-mode contribution sum mu_j<0 mu_j|<f,w_j>|^2 : "
          f"median={np.median(negcontrib):.3f} min={negcontrib.min():.3f}")
    print(f"  f's POSITIVE-mode contribution : median={np.median(poscontrib):.3f}")
    print(f"  ratio |neg|/pos : median={np.median(np.abs(negcontrib)/poscontrib):.3f}")
    print("  => f DOES overlap M's negative modes; positivity of f^TMf is a WEIGHTED balance,")
    print("     not orthogonality. The clean statement is the 2x2 block (TASK 2), not V- _|_ u2.")

    # ---------------- TASK 4 ----------------
    print("\n" + "=" * 76)
    print("TASK 4 — number of negative eigenvalues of M; interlacing")
    print("=" * 76)
    nneg = []; npos = []; nzero = []
    for q in data:
        mu = np.linalg.eigvalsh(q['Mop'])
        nneg.append(int((mu < -tol).sum()))
        npos.append(int((mu > tol).sum()))
        nzero.append(int((np.abs(mu) <= tol).sum()))
    nneg = np.array(nneg); npos = np.array(npos)
    ns = np.array([q['n'] for q in data])
    print(f"  #negative eig of M : min={nneg.min()} median={int(np.median(nneg))} max={nneg.max()}")
    print(f"  #positive eig of M : min={npos.min()} median={int(np.median(npos))} max={npos.max()}")
    print(f"  #neg == n-2 (only 2 nonneg, the low block) : {int((nneg==ns-2).sum())}/{ng}")
    print(f"  #pos <= 2 : {int((npos<=2).sum())}/{ng};  #pos distribution unique: "
          f"{sorted(set(npos.tolist()))[:10]}")
    # Weyl: mu_2(M) >= lam2*sigma_min...(Q) - sigma_max(L_M)?  test whether mu_2(M)>=0 ever.
    mu2 = []
    for q in data:
        mu = np.linalg.eigvalsh(q['Mop'])
        mu2.append(float(mu[1]))    # 2nd smallest
    mu2 = np.array(mu2)
    print(f"  2nd-smallest eig mu_2(M): min={mu2.min():.3f} median={np.median(mu2):.3f} "
          f"(>=0 would mean <=1 negative eig)")
    print(f"  graphs with mu_2(M) >= 0 (M has <=1 negative eig) : {int((mu2>=-tol).sum())}/{ng}")

    print("\n" + "=" * 76)
    print("SUMMARY")
    print("=" * 76)
    print(f"  B = PSD of the 2x2 low-freq block M_low (agree {agree}/{ng}).")
    print(f"  M has MANY negative eigenvalues (median {int(np.median(nneg))} of n); f is NOT")
    print(f"  orthogonal to V-(M) (||P_{{V-}}u2||^2 median {np.median(neg_u2_mass):.3f}).")
    print("  The protection is the (u1,u2) block PSD via the S-coupling, NOT eigenvector orthogonality.")


if __name__ == "__main__":
    main()
