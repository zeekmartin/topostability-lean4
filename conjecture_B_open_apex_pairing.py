"""
Apex (neighbourhood) decomposition of the open-2-path energy and the covariance correction.

Target (= -Q >= 0, conjecture):  Open + A >= lam f^T A f
  Open = f^T L_P f         (open-2-path Laplacian energy)
  A    = Cov_L(d,f^2) = 1/2 sum_{ab in E}(d_a-d_b)(f_a^2-f_b^2) = d^T L(f o f)
  lam f^T A f = lam (f^T D f - lam)   (unit f),  f^T A f = sum_c s_c f_c  (s_c=(Af)_c)

Conventions for apex sums (ORDERED pairs a,b in N(c), a != b):
  Open_c = sum_{a,b in N(c), a!=b, a not~ b} (f_a-f_b)^2     -> sum_c Open_c = 2*Open
  T_c    = sum_{a,b in N(c), a~b}           (f_a-f_b)^2      -> sum_c T_c    = 2*T
  Open_c + T_c = sum_{a,b in N(c)}(f_a-f_b)^2 = 2 d_c mass_c - 2 s_c^2
  mass_c = sum_{v in N(c)} f_v^2,  s_c = sum_{v in N(c)} f_v = (d_c-lam) f_c.

Apex covariance pieces (from d_a-d_b = sum_c [1_{a in N(c)} - 1_{b in N(c)}]):
  A = sum_c A_c,  A_c = 1/2 sum_{ab in E, exactly one endpoint in N(c)} (f_in^2 - f_out^2)
     (a BOUNDARY sum over edges leaving N(c); in = endpoint in N(c)).

TASK 1 apex decomposition of Open (circular vs new local terms)
TASK 2 apex decomposition of A (boundary form), check support vs Open_c
TASK 3 local apex inequality  open_c + A_c >= lam s_c f_c  (the share summing to target)
TASK 4 Cauchy-Schwarz on open cherries inside N(c)
Run: python conjecture_B_open_apex_pairing.py
"""
import numpy as np
import networkx as nx
from conjecture_B_nodal_decomposition import corpus
from conjecture_B_same_sign_reservoir import glue, chain_cliques


def graph_quant(G):
    nodes = list(G.nodes())
    idx = {u: i for i, u in enumerate(nodes)}
    n = len(nodes)
    L = nx.laplacian_matrix(G, nodelist=nodes).toarray().astype(float)
    d = L.diagonal().copy()
    A = np.diag(d) - L
    ev, V = np.linalg.eigh(L)
    lam = ev[1]
    f = V[:, 1] / np.linalg.norm(V[:, 1])
    A2 = A @ A
    D = np.diag(d)
    M = A * A2
    P = A2 - D - M
    sigma = A @ d
    L_M = np.diag(M.sum(1)) - M
    L_P = np.diag(P.sum(1)) - P
    T = float(f @ L_M @ f)
    Open = float(f @ L_P @ f)
    fDf = float((d * f * f).sum())
    fAf = float(f @ A @ f)
    f2 = f * f

    # per-apex quantities
    nbr_list = [np.where(A[c] > 0)[0] for c in range(n)]
    open_c = np.zeros(n)      # ordered Open_c
    T_c = np.zeros(n)         # ordered T_c
    s_c = np.zeros(n)
    mass_c = np.zeros(n)
    A_c = np.zeros(n)         # boundary covariance piece
    nbrset = [set(nb.tolist()) for nb in nbr_list]
    for c in range(n):
        nb = nbr_list[c]
        fc = f[nb]
        s_c[c] = fc.sum()
        mass_c[c] = (fc * fc).sum()
        sub = A[np.ix_(nb, nb)]
        g2 = np.subtract.outer(fc, fc) ** 2
        T_c[c] = float((sub * g2).sum())                  # ordered, a~b
        tot = float((g2).sum())                           # ordered all pairs
        open_c[c] = tot - T_c[c]                           # ordered, a not~ b
        # boundary covariance piece A_c = 1/2 sum_{v in N(c)} sum_{w~v, w not in N(c)}(f_v^2 - f_w^2)
        acc = 0.0
        S = nbrset[c]
        for v in nb:
            for w in nbr_list[v]:
                if w not in S:                             # w outside N(c) (includes w=c)
                    acc += f2[v] - f2[w]
        A_c[c] = 0.5 * acc
    return dict(n=n, d=d, lam=lam, f=f, f2=f2, sigma=sigma, T=T, Open=Open, fDf=fDf, fAf=fAf,
                open_c=open_c, T_c=T_c, s_c=s_c, mass_c=mass_c, A_c=A_c,
                Acal=0.5 * float(sum((d[a] - d[b]) * (f2[a] - f2[b]) for a, b in
                                     [(idx[u], idx[v]) for u, v in G.edges()])))


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
    data = [(fam, graph_quant(G)) for fam, G in all_graphs()]
    ng = len(data)
    print(f"{ng} graphs\n")

    def mx(fn):
        return max(abs(fn(q)) for _, q in data)

    # ---------------- TASK 1 ----------------
    print("=" * 78)
    print("TASK 1 — apex decomposition of Open / T (exact identities)")
    print("=" * 78)
    r_open = mx(lambda q: q['open_c'].sum() - 2 * q['Open'])
    r_T = mx(lambda q: q['T_c'].sum() - 2 * q['T'])
    r_sum = mx(lambda q: max(abs((q['open_c'] + q['T_c'])
                                 - (2 * q['d'] * q['mass_c'] - 2 * q['s_c'] ** 2))))
    r_s = mx(lambda q: max(abs(q['s_c'] - (q['d'] - q['lam']) * q['f'])))
    print(f"  sum_c Open_c == 2*Open                         : max residual {r_open:.2e}")
    print(f"  sum_c T_c    == 2*T                            : max residual {r_T:.2e}")
    print(f"  Open_c+T_c == 2 d_c mass_c - 2 s_c^2           : max residual {r_sum:.2e}")
    print(f"  s_c == (d_c - lam) f_c   (eigen-recursion)     : max residual {r_s:.2e}")
    print("  => apex Open/T split is EXACT; summed it reproduces T+Open = Σσf² - fᵀA²f")
    print("     (the A² identity, circular). New object = per-apex Open_c, T_c, A_c.")

    # ---------------- TASK 2 ----------------
    print("\n" + "=" * 78)
    print("TASK 2 — apex (boundary) decomposition of the covariance A")
    print("=" * 78)
    r_Asum = mx(lambda q: q['A_c'].sum() - q['Acal'])
    print(f"  sum_c A_c == A = Cov_L(d,f²)                   : max residual {r_Asum:.2e}")
    # support overlap: A_c is a BOUNDARY sum, Open_c an INTERNAL sum. Are they correlated per apex?
    corr_ao = []
    for _, q in data:
        oc = q['open_c'] / 2.0
        if oc.std() > 1e-12 and q['A_c'].std() > 1e-12:
            corr_ao.append(np.corrcoef(oc, q['A_c'])[0, 1])
    print(f"  A_c is a BOUNDARY sum (edges leaving N(c)); Open_c an INTERNAL (cherry) sum.")
    print(f"  corr(open_c, A_c) across apices: mean={np.mean(corr_ao):+.3f}")
    frac_Aneg = np.mean([np.mean(q['A_c'] < 0) for _, q in data])
    print(f"  fraction of apices with A_c < 0 (mean over graphs): {frac_Aneg:.3f}")

    # ---------------- TASK 3 ----------------
    print("\n" + "=" * 78)
    print("TASK 3 — local apex inequality  open_c + A_c  >=  share_c")
    print("=" * 78)
    print("  (open_c := Open_c/2 so Σ open_c = Open; Σ A_c = A; target Open+A >= lam fᵀAf)")
    shares = {
        "lam s_c f_c   (Σ=lam fᵀAf)": lambda q: q['lam'] * q['s_c'] * q['f'],
        "lam mass_c": lambda q: q['lam'] * q['mass_c'],
        "lam f_c s_c, pos part only": lambda q: np.maximum(q['lam'] * q['s_c'] * q['f'], 0),
    }
    for name, shfn in shares.items():
        loc_ok = 0
        loc_tot = 0
        agg_ok = 0
        for _, q in data:
            lhs = q['open_c'] / 2.0 + q['A_c']
            sh = shfn(q)
            loc = lhs >= sh - 1e-9
            loc_ok += int(loc.sum())
            loc_tot += len(lhs)
            if lhs.sum() >= sh.sum() - 1e-7:
                agg_ok += 1
        print(f"  share = {name:30s}: per-apex {loc_ok}/{loc_tot} "
              f"({100*loc_ok/loc_tot:.1f}%)  graphs-agg {agg_ok}/{ng}")

    # ---------------- TASK 4 ----------------
    print("\n" + "=" * 78)
    print("TASK 4 — Cauchy-Schwarz on open cherries inside N(c)")
    print("=" * 78)
    # open-2-path Laplacian inside N(c): for the cherry set, the bilinear pairing of d and f^2
    # restricted to N(c) would give a 'local covariance'. Test |localCov_c| <= sqrt(Open_c * Ed_c)
    # where Ed_c = sum_{a,b in N(c),a not~b}(d_a-d_b)^2 (open-cherry Dirichlet energy of d).
    holds = 0
    tot = 0
    tight = []
    for _, q in data:
        n = q['n']
        f = q['f']
        d = q['d']
        # recompute per-apex localCov and Ed using neighbour lists is expensive; approximate via
        # the identity localCov_c = 1/2 sum_{a,b in N(c),a not~b}(d_a-d_b)(f_a^2-f_b^2)
        # We compare to A_c? No: A_c is boundary. Here test the INTERNAL-cherry covariance vs Open_c.
        pass
    # internal-cherry covariance computed alongside open_c:
    cs_hold = 0
    cs_tot = 0
    ratios = []
    for _, q in data:
        # reconstruct neighbour cherries from stored quantities is not possible; recompute lite
        pass
    print("  (internal-cherry covariance vs Open_c computed in TASK4b below)")

    # TASK 4b: recompute internal cherry covariance per apex and run Cauchy-Schwarz
    print("\n  TASK 4b — internal-cherry covariance  cov_c = 1/2 Σ_{cherries}(d_a-d_b)(f_a²-f_b²)")
    cs_hold = 0
    cs_tot = 0
    ratios = []
    sum_match = []
    for fam, G in all_graphs():
        nodes = list(G.nodes())
        n = len(nodes)
        Lm = nx.laplacian_matrix(G, nodelist=nodes).toarray().astype(float)
        d = Lm.diagonal().copy()
        Am = np.diag(d) - Lm
        ev, Vv = np.linalg.eigh(Lm)
        f = Vv[:, 1] / np.linalg.norm(Vv[:, 1])
        f2 = f * f
        nbr = [np.where(Am[c] > 0)[0] for c in range(n)]
        covsum = 0.0
        for c in range(n):
            nb = nbr[c]
            sub = Am[np.ix_(nb, nb)]
            dd = np.subtract.outer(d[nb], d[nb])
            ff = np.subtract.outer(f2[nb], f2[nb])
            openmask = 1.0 - sub
            np.fill_diagonal(openmask, 0.0)
            cov_c = 0.5 * float((openmask * dd * ff).sum())      # ordered open cherries
            # open-cherry Dirichlet energies (ordered)
            Ed = float((openmask * dd ** 2).sum())
            Ef = float((openmask * (np.subtract.outer(f[nb], f[nb]) ** 2)).sum())  # = 2*Open_c
            cs_tot += 1
            if abs(cov_c) <= np.sqrt(max(Ed, 0) * max(Ef, 0)) + 1e-7:
                cs_hold += 1
            if Ed * Ef > 1e-12:
                ratios.append(abs(cov_c) / np.sqrt(Ed * Ef))
            covsum += cov_c
    ratios = np.array(ratios)
    print(f"  per-apex CS |cov_c| <= sqrt(Ed_c · 2Open_c)   : {cs_hold}/{cs_tot} apices")
    if len(ratios):
        print(f"  tightness |cov_c|/sqrt(Ed·Ef): min={ratios.min():.3f} "
              f"median={np.median(ratios):.3f} max={ratios.max():.3f}")
    print("  NOTE: cov_c (internal cherries) != A_c (boundary). The covariance A localizes to")
    print("  the BOUNDARY of N(c), Open to the INTERIOR -- they do not share a per-apex support.")

    print("\n" + "=" * 78)
    print("SUMMARY")
    print("=" * 78)


if __name__ == "__main__":
    main()
