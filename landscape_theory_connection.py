"""Test Tao-Filoche-Mayboroda landscape theory for aggregate_triangle_poincare.

Target (undirected):  T = Σ_e t_e (f_a-f_b)² ≤ λ·degQuad   (Lean triEnergy ≤ 2λ degQuad is ×2).
  L_t = D_t - A_t,  A_t = A⊙A² (Hadamard, weights t_ij),  D_t = diag(σ_v), σ_v = Σ_u t_uv.
  T = fᵀ L_t f,  degQuad = fᵀ D f,  f = unit Fiedler (L f = λ f).

KEY IDENTITY (TASK 5):  with S = ½(LD+DL) - L_t,   fᵀSf = λ·degQuad - T,
  so aggregate ⟺ fᵀSf ≥ 0.  S is a Z-matrix (off-diag t_ij-(d_i+d_j)/2 ≤ 0).  PSD?
"""
import numpy as np, networkx as nx
from numpy.linalg import solve, eigvalsh
from scipy.stats import pearsonr


def corr(x, y):
    x, y = np.asarray(x, float), np.asarray(y, float)
    if x.std() < 1e-12 or y.std() < 1e-12: return float('nan')
    return float(pearsonr(x, y)[0])


def analyze(name, G):
    G = nx.convert_node_labels_to_integers(G)
    if not nx.is_connected(G) or G.number_of_nodes() < 4: return None
    A = nx.to_numpy_array(G); n = len(A); d = A.sum(1); D = np.diag(d)
    L = D - A; A2 = A @ A
    At = A * A2                       # Hadamard: weights t_ij on edges
    sig = At.sum(1)                   # σ_v = Σ_u t_uv = triDeg_v  (=2·triangles through v)
    Dt = np.diag(sig); Lt = Dt - At
    ev, U = eigvalsh(L), None
    w, V = np.linalg.eigh(L); lam = w[1]; f = V[:, 1]; f = f / np.linalg.norm(f)
    T = float(f @ Lt @ f); degQuad = float(f @ D @ f)
    agg = T / (lam * degQuad) if lam * degQuad > 1e-12 else float('nan')

    # ---- TASK 1: landscape of the manufactured M-matrix  A_land = L + diag(σ/maxσ) ----
    pot = sig / sig.max() if sig.max() > 0 else np.zeros(n)
    Aland = L + np.diag(pot)
    u = solve(Aland, np.ones(n))      # u > 0 (M-matrix); effective potential W = 1/u
    W = 1.0 / u

    # ---- TASK 2: correlations ----
    c_Wsig = corr(W, sig); c_Wd = corr(W, d); c_uf2 = corr(u, f * f)
    c_te_g2 = []                       # known anti-corr(t_e, g_e²) over edges
    iu, ju = np.where(np.triu(A, 1) > 0)
    te = np.array([A2[i, j] for i, j in zip(iu, ju)])
    g2 = np.array([(f[i] - f[j]) ** 2 for i, j in zip(iu, ju)])
    c_anti = corr(te, g2)

    # ---- TASK 3: Agmon-style pointwise bound  |f_v| ≤ λ u_v max|f| ----
    fmax = np.abs(f).max()
    agmon_ok = float(np.mean(np.abs(f) <= lam * u * fmax + 1e-9))   # fraction satisfied
    # edge gradient vs landscape: corr(g_e², (u_a+u_b)²) and validity of g²≤C λ²(u_a+u_b)²
    ula = np.array([(u[i] + u[j]) ** 2 for i, j in zip(iu, ju)])
    c_grad_u = corr(g2, ula)
    Cg = float((g2 / (lam ** 2 * ula)).max()) if len(ula) else float('nan')   # needed C

    # ---- TASK 4: candidate landscape upper bounds on T (valid? close vs λ·degQuad?) ----
    cand = {}
    B = lam ** 2 * float(sig @ (u * u))                 # λ²·Σ σ_v u_v²
    cand['lam2 Σσ u²'] = (T / B if B > 1e-12 else np.inf, B / (lam * degQuad) if degQuad>0 else np.inf)
    B = lam ** 2 * float(d @ (u * u)) * lam             # λ³·Σ d_v u_v²
    cand['lam3 Σd u²'] = (T / B if B > 1e-12 else np.inf, B / (lam * degQuad) if degQuad>0 else np.inf)
    B = lam ** 2 * float(sig @ (u * u * f * f))          # λ²·Σ σ_v u_v² f_v² (mixed)
    cand['lam2 Σσ u² f²'] = (T / B if B > 1e-12 else np.inf, B / (lam * degQuad) if degQuad>0 else np.inf)

    # ---- TASK 5: M-matrix / Z-matrix structure ----
    M = L + At                                          # = D - A + A_t ; off-diag t_ij - 1
    Moff = M - np.diag(np.diag(M)); M_maxoff = float(Moff.max())     # >0 ⇒ NOT M-matrix
    S = 0.5 * (L @ D + D @ L) - Lt
    Soff = S - np.diag(np.diag(S)); S_maxoff = float(Soff.max())     # ≤0 ⇒ Z-matrix
    S_mineig = float(eigvalsh(S).min())                  # ≥0 ⇒ PSD ⇒ M-matrix ⇒ aggregate ∀f
    fSf = float(f @ S @ f); identity_err = abs(fSf - (lam * degQuad - T))

    return dict(name=name, n=n, lam=lam, agg=agg, c_Wsig=c_Wsig, c_Wd=c_Wd, c_uf2=c_uf2,
                c_anti=c_anti, agmon_ok=agmon_ok, c_grad_u=c_grad_u, Cg=Cg, cand=cand,
                M_maxoff=M_maxoff, S_maxoff=S_maxoff, S_mineig=S_mineig,
                identity_err=identity_err, fSf=fSf, lamDQminusT=lam * degQuad - T)


def lollipop(m, p): return nx.lollipop_graph(m, p)
def dumbbell(m):
    G = nx.disjoint_union(nx.complete_graph(m), nx.complete_graph(m)); G.add_edge(0, m); return G
def deg2d(nn, q, s):
    H = nx.gnp_random_graph(nn - 1, q, seed=s); H.add_node(nn - 1); H.add_edge(nn - 1, 0); H.add_edge(nn - 1, 1); return H
def twin(N, dd):
    K = nx.complete_graph(N); a, b = N, N + 1
    for x in (a, b):
        for w in range(dd): K.add_edge(x, w)
    K.add_node(N + 2); K.add_edge(N + 2, a); K.add_edge(N + 2, b); return K

corpus = [
    ("K8", nx.complete_graph(8)), ("K20", nx.complete_graph(20)),
    ("cycle20", nx.cycle_graph(20)), ("torus6x6", nx.grid_2d_graph(6, 6, periodic=True)),
    ("dumbbell10", dumbbell(10)), ("dumbbell20", dumbbell(20)),
    ("lollipop10_8", lollipop(10, 8)), ("lollipop15_10", lollipop(15, 10)),
    ("gnp30_0.3", nx.gnp_random_graph(30, 0.3, seed=1)),
    ("gnp40_0.5", nx.gnp_random_graph(40, 0.5, seed=2)),
    ("gnp50_0.15", nx.gnp_random_graph(50, 0.15, seed=3)),
    ("deg2d40_0.6", deg2d(40, 0.6, 7)), ("deg2d60_0.4", deg2d(60, 0.4, 7)),
    ("twin30_3", twin(30, 3)), ("twin50_2", twin(50, 2)),
    ("BA50_3", nx.barabasi_albert_graph(50, 3, seed=4)),
    ("WS40_6", nx.watts_strogatz_graph(40, 6, 0.3, seed=5)),
    ("petersen", nx.petersen_graph()),
]
R = [analyze(nm, G) for nm, G in corpus]; R = [r for r in R if r]

print("=" * 100)
print("TASK 5 — S = ½(LD+DL) − L_t :  identity fᵀSf = λ·degQuad − T,  Z-matrix?,  PSD (M-matrix)?")
print("=" * 100)
print(f"{'graph':<15}{'agg T/λDQ':<11}{'fᵀSf':<10}{'λDQ−T':<10}{'id.err':<9}{'S off≤0?':<10}{'S min eig':<11}{'M off (t-1)':<10}")
for r in R:
    print(f"{r['name']:<15}{r['agg']:<11.3f}{r['fSf']:<10.3f}{r['lamDQminusT']:<10.3f}{r['identity_err']:<9.1e}"
          f"{('YES' if r['S_maxoff']<=1e-9 else 'NO'):<10}{r['S_mineig']:<11.4f}{r['M_maxoff']:<10.1f}")
nS_psd = sum(r['S_mineig'] >= -1e-7 for r in R)
print(f"\n  S is a Z-matrix on {sum(r['S_maxoff']<=1e-9 for r in R)}/{len(R)} graphs;  "
      f"S is PSD (M-matrix) on {nS_psd}/{len(R)} graphs.")
print(f"  M = L + A⊙A² has a POSITIVE off-diagonal (t_ij−1>0) on {sum(r['M_maxoff']>1e-9 for r in R)}/{len(R)} "
      f"(⇒ not an M-matrix).")

print("\n" + "=" * 100)
print("TASK 2/3 — landscape u = (L+diag(σ/maxσ))⁻¹·1 correlations + Agmon pointwise bound")
print("=" * 100)
print(f"{'graph':<15}{'corr(1/u,σ)':<12}{'corr(1/u,d)':<12}{'corr(u,f²)':<12}{'corr(t_e,g²)':<13}{'|f|≤λu·max':<11}{'corr(g²,(u+u)²)'}")
for r in R:
    print(f"{r['name']:<15}{r['c_Wsig']:<12.3f}{r['c_Wd']:<12.3f}{r['c_uf2']:<12.3f}{r['c_anti']:<13.3f}"
          f"{r['agmon_ok']:<11.2f}{r['c_grad_u']:.3f}")

print("\n" + "=" * 100)
print("TASK 4 — candidate landscape bounds:  T/B (≤1 ⇒ valid upper bd) ,  B/(λ·degQuad) (≤1 ⇒ closes)")
print("=" * 100)
keys = list(R[0]['cand'].keys())
print(f"{'graph':<15}" + "".join(f"{k+' T/B':<16}{k+' B/λDQ':<16}" for k in keys))
for r in R:
    row = f"{r['name']:<15}"
    for k in keys:
        tb, bl = r['cand'][k]; row += f"{tb:<16.3f}{bl:<16.2f}"
    print(row)
print("\n  A bound CLOSES iff (T/B ≤ 1 on all graphs) AND (B/λDQ ≤ 1 on all graphs).")
