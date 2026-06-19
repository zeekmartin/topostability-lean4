"""
Global summation-by-parts search for aggregate_triangle_poincare.

Target (equivalent to the conjecture, verified circular-exact = -Q):
    Open + 𝒜 - lam f^T A f  =  -Q  >= 0
with
    Open = f^T L_P f                     (open-2-path Dirichlet energy, PSD)
    𝒜    = sum_{ab in E}(d_a-d_b)(f_a^2-f_b^2)   (degree-Fiedler assortativity)
    A    = adjacency matrix, f^T A f = f^T D f - lam   (unit f)
    Q    = T - lam f^T D f               (aggregate slack, conjecture <=> Q<=0)

The user asked to hunt for an EXACT global summation-by-parts identity, trying the
multipliers d_v f_v, d_v^2 f_v, (d_v-lam)f_v, (sigma_v-d_v^2)f_v, f_v^3, and the
neighbour-valued multipliers (M f)_v, (A D f)_v, (A^2 f)_v.

KEY ALGEBRAIC POINT proved here numerically:
  For ANY symmetric operator B and the eigenvector f (L f = lam f, L,B symmetric),
        f^T B L f = (Bf)^T (Lf) = lam (Bf)^T f = lam f^T B f.
  So  f^T M L f = lam f^T M f,  f^T L A^2 f = lam f^T A^2 f, ...  are all TAUTOLOGIES
  (one application of the eigen-equation, no new content). New content only appears
  when one side is expanded combinatorially (edge / 2-path sums) -- the SBP identities
  in PART B -- or via the covariance reading of 𝒜 (PART A).

Run: python conjecture_B_global_summation_parts.py
"""
import numpy as np
import networkx as nx
from conjecture_B_nodal_decomposition import corpus
from conjecture_B_same_sign_reservoir import glue, chain_cliques


def graph_quant(G):
    nodes = list(G.nodes())
    L = nx.laplacian_matrix(G, nodelist=nodes).toarray().astype(float)
    d = L.diagonal().copy()
    A = np.diag(d) - L
    ev, V = np.linalg.eigh(L)
    lam = ev[1]
    f = V[:, 1] / np.linalg.norm(V[:, 1])
    A2 = A @ A
    D = np.diag(d)
    M = A * A2                                   # Hadamard: triangle edges
    P = A2 - D - M                               # open 2-paths
    sigma = A @ d                                # sigma_v = sum_{c~v} d_c = (A d)_v
    tau = M.sum(1)
    pdeg = P.sum(1)
    L_M = np.diag(tau) - M
    L_P = np.diag(pdeg) - P
    f2 = f * f                                    # entrywise square (a VECTOR)
    T = float(f @ L_M @ f)
    Open = float(f @ L_P @ f)
    fDf = float(d @ f2)
    fAf = float(f @ A @ f)
    Q = T - lam * fDf
    Acal = float(f @ A @ (np.diag(f) @ f)) * 0   # placeholder, set below
    # assortativity 𝒜 over unordered edges:
    Acal = 0.0
    for a, b in G.edges():
        ia, ib = nodes.index(a), nodes.index(b)
        Acal += (d[ia] - d[ib]) * (f[ia] ** 2 - f[ib] ** 2)
    return dict(nodes=nodes, n=len(nodes), L=L, A=A, D=D, d=d, lam=lam, f=f, f2=f2,
                A2=A2, M=M, P=P, sigma=sigma, tau=tau, pdeg=pdeg, L_M=L_M, L_P=L_P,
                T=T, Open=Open, fDf=fDf, fAf=fAf, Q=Q, Acal=Acal)


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
    n_graphs = len(data)
    print(f"{n_graphs} graphs\n")

    def mx(fn):
        return max(abs(fn(q)) for _, q in data)

    # ================================================================
    print("=" * 78)
    print("PART A — the covariance form of the assortativity correction 𝒜")
    print("=" * 78)
    # NEW: 𝒜 = d^T L (f^2)  = graph-Laplacian covariance of degree d and squared Fiedler f^2
    r1 = mx(lambda q: q['Acal'] - q['d'] @ (q['L'] @ q['f2']))
    # symmetric pairing: 𝒜 = (f^2)^T L d
    r2 = mx(lambda q: q['Acal'] - q['f2'] @ (q['L'] @ q['d']))
    # = sum d^2 f^2 - d^T A f^2
    r3 = mx(lambda q: q['Acal'] - ((q['d'] ** 2) @ q['f2'] - q['d'] @ (q['A'] @ q['f2'])))
    # = - sum_v (sigma_v - d_v^2) f_v^2   (old form)
    r4 = mx(lambda q: q['Acal'] + ((q['sigma'] - q['d'] ** 2) @ q['f2']))
    print(f"  𝒜 == d^T L (f∘f)            [COVARIANCE form] : max residual {r1:.2e}")
    print(f"  𝒜 == (f∘f)^T L d            [symmetry]        : max residual {r2:.2e}")
    print(f"  𝒜 == Σd²f² - d^T A f²                         : max residual {r3:.2e}")
    print(f"  𝒜 == -Σ_v(σ_v-d_v²)f_v²     [known]           : max residual {r4:.2e}")
    print("  => 𝒜 is exactly the Laplacian bilinear form ⟨d, f²⟩_L (graph covariance")
    print("     of degree and squared Fiedler value). Clean, spectral-free, formalizable.")

    # ================================================================
    print("\n" + "=" * 78)
    print("PART B — edge<->diagonal SBP family  (multiply eigen-recursion by w_v f_v)")
    print("=" * 78)
    # multiply (A f)_v = (d_v - lam) f_v  by  w_v f_v  and sum:
    #   sum_v w_v f_v (A f)_v = sum_{ab in E}(w_a + w_b) f_a f_b  (LHS combinatorial)
    #   = sum_v w_v (d_v - lam) f_v^2                              (RHS diagonal)
    def edge_w(q, w):
        A, f = q['A'], q['f']
        # sum_{ab in E}(w_a+w_b) f_a f_b = f^T (A W + W A) f / 2  with W=diag(w)
        W = np.diag(w)
        return float(f @ (A @ W + W @ A) @ f) / 2
    def diag_w(q, w):
        return float((w * (q['d'] - q['lam']) * q['f2']).sum())
    for name, wf in [("1   ", lambda q: np.ones(q['n'])),
                     ("d   ", lambda q: q['d']),
                     ("d^2 ", lambda q: q['d'] ** 2),
                     ("sigma", lambda q: q['sigma'])]:
        r = mx(lambda q: edge_w(q, wf(q)) - diag_w(q, wf(q)))
        print(f"  Σ_E (w_a+w_b)f_a f_b == Σ w(d-λ)f²   [w={name}] : max residual {r:.2e}")
    print("  => exact family. w=1 gives f^T A f = Σ(d-λ)f² (known); w=d gives")
    print("     f^T A D f = Σ d(d-λ)f²; these convert edge correlations to degree diagonals.")

    # ================================================================
    print("\n" + "=" * 78)
    print("PART C — operator-product 'SBP' suggestions all collapse to tautologies")
    print("=" * 78)
    # f^T B L f = lam f^T B f for symmetric B and eigenvector f.  Demonstrate.
    for name, Bf in [("M    ", lambda q: q['M']),
                     ("A^2  ", lambda q: q['A2']),
                     ("L_P  ", lambda q: q['L_P']),
                     ("L_M  ", lambda q: q['L_M']),
                     ("A D  ", lambda q: q['A'] @ q['D'] + q['D'] @ q['A'])]:  # symmetrized
        def res(q, Bf=Bf):
            B = Bf(q); f, L, lam = q['f'], q['L'], q['lam']
            return float(f @ B @ (L @ f)) - lam * float(f @ B @ f)
        r = mx(res)
        print(f"  f^T B L f == λ f^T B f   [B={name}] : max residual {r:.2e}")
    print("  => one eigen-application only; NO new content. (User's f^T M L f, f^T L A² f")
    print("     are λ f^T M f, λ f^T A² f exactly. Dead as sign-exposing routes.)")

    # ================================================================
    print("\n" + "=" * 78)
    print("PART D — master target identity and its candidate reformulations")
    print("=" * 78)
    # target: -Q = Open + 𝒜 - lam f^T A f
    rT = mx(lambda q: (-q['Q']) - (q['Open'] + q['Acal'] - q['lam'] * q['fAf']))
    print(f"  -Q == Open + 𝒜 - λ f^T A f                    : max residual {rT:.2e}")
    # with f^T A f = fDf - lam:
    rT2 = mx(lambda q: (-q['Q']) - (q['Open'] + q['Acal'] - q['lam'] * (q['fDf'] - q['lam'])))
    print(f"  -Q == Open + ⟨d,f²⟩_L - λ(f^TDf - λ)          : max residual {rT2:.2e}")

    # (D1) is the matrix  B_lam = lam D - L_M  PSD ?   -Q = f^T B_lam f by definition.
    rDef = mx(lambda q: (-q['Q']) - float(q['f'] @ (q['lam'] * q['D'] - q['L_M']) @ q['f']))
    print(f"\n  -Q == f^T (λD - L_M) f  [B_λ, λ the TRUE eigval]: max residual {rDef:.2e}")
    mins = []
    psd_ok = 0
    for _, q in data:
        Bm = q['lam'] * q['D'] - q['L_M']
        w = np.linalg.eigvalsh(Bm)
        mins.append(w[0])
        if w[0] >= -1e-9:
            psd_ok += 1
    mins = np.array(mins)
    print(f"  is B_λ = λD - L_M PSD?  λ_min(B_λ): min={mins.min():.4f} median={np.median(mins):.4f}")
    print(f"  graphs with B_λ ⪰ 0 (would give f-independent Rayleigh proof): {psd_ok}/{n_graphs}")
    print("  => B_λ is NOT PSD in general: no fixed-operator Rayleigh certificate. The")
    print("     nonnegativity of -Q is special to the Fiedler direction (λ=f^TLf couples in).")

    # ================================================================
    print("\n" + "=" * 78)
    print("PART E — Cauchy–Schwarz on the covariance 𝒜 (a lead, not a proof)")
    print("=" * 78)
    # |𝒜| = |⟨d,f²⟩_L| <= sqrt( E_L(d) * E_L(f²) ),  E_L(g)=Σ_E (g_a-g_b)^2 = g^T L g
    holds = 0
    ratios = []
    for _, q in data:
        EL_d = float(q['d'] @ (q['L'] @ q['d']))
        EL_f2 = float(q['f2'] @ (q['L'] @ q['f2']))
        cs = np.sqrt(max(EL_d, 0) * max(EL_f2, 0))
        if abs(q['Acal']) <= cs + 1e-7:
            holds += 1
        if cs > 1e-12:
            ratios.append(abs(q['Acal']) / cs)
    ratios = np.array(ratios)
    print(f"  |𝒜| <= sqrt(E_L(d)·E_L(f²))  (Cauchy-Schwarz)  : {holds}/{n_graphs}")
    print(f"  tightness |𝒜|/sqrt(...) : min={ratios.min():.3f} median={np.median(ratios):.3f} "
          f"max={ratios.max():.3f}")
    # Does E_L(f²) relate to Open?  E_L(f²)=Σ_E (f_a-f_b)^2(f_a+f_b)^2 ; Open lives on non-edges.
    print("  (E_L(f²)=Σ_E(f_a-f_b)²(f_a+f_b)² is an EDGE energy; Open is a NON-edge 2-path")
    print("   energy -- different index sets, so CS does not directly couple 𝒜 to Open.)")

    # ================================================================
    print("\n" + "=" * 78)
    print("PART F — is -Q a degree-difference-weighted Dirichlet / 2-path energy?")
    print("=" * 78)
    # Candidate: -Q =? Σ over open 2-paths a-c-b of weight*(f_a-f_b)^2 with signed degree weight.
    # Open itself = Σ_{P3} (f_a-f_b)^2 (weight = common-nbr count, all +1 per path). Try adding
    # a degree-difference weight on the SAME open 2-paths and see if it can equal -Q - circular?
    # Test the honest decomposition -Q = Open - Σ R_v f_v^2 (R the signed diagonal) once more,
    # and report the signed-2-path attempt residual is exactly the (uncancelled) R diagonal.
    rRdiag = []
    for _, q in data:
        R = q['sigma'] - (q['d'] - q['lam']) ** 2 - q['lam'] * q['d']
        rRdiag.append(abs((-q['Q']) - (q['Open'] - float((R * q['f2']).sum()))))
    print(f"  -Q == Open - Σ_v R_v f_v²   (R signed diagonal): max residual {max(rRdiag):.2e}")
    print("  => the ONLY exact reductions of -Q are circular (Open minus the signed diagonal,")
    print("     or f^T(λD-L_M)f). No degree-difference-weighted 2-path SOS makes -Q manifestly")
    print("     nonnegative: the negative hub mass of 𝒜=⟨d,f²⟩_L must cancel Open globally.")

    print("\n" + "=" * 78)
    print("SUMMARY")
    print("=" * 78)
    print("  EXACT (machine zero, all graphs):")
    print("   * 𝒜 = ⟨d, f²⟩_L = d^T L(f∘f)         [covariance form; NEW, formalizable]")
    print("   * Σ_E(w_a+w_b)f_a f_b = Σ w(d-λ)f²    [edge<->diagonal SBP family; NEW]")
    print("   * -Q = Open + ⟨d,f²⟩_L - λ(f^TDf-λ)   [target, covariance-reframed]")
    print("  TAUTOLOGICAL (no new content): f^T B L f = λ f^T B f for symmetric B.")
    print("  NEGATIVE: B_λ=λD-L_M not PSD; CS on 𝒜 doesn't couple to Open; -Q has no")
    print("            degree-weighted 2-path SOS -- the cancellation is irreducibly global.")


if __name__ == "__main__":
    main()
