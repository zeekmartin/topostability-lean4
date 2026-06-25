"""Test a link-based log-Sobolev / Fisher route for aggregate_triangle_poincare.

Target (undirected normalization):  T_und = Σ_e t_e (f_a-f_b)²  ≤  λ·degQuad,
   degQuad = Σ_v d_v f_v²,  t_e = |N(a)∩N(b)|,  f = unit Fiedler (L f = λ f).
(The Lean form triEnergy ≤ 2λ·degQuad is this ×2, since triEnergy is the ordered sum.)

Key identity:  T_und = Σ_{triangles {a,b,c}} (g_ab² + g_bc² + g_ca²)
   = Σ_v τ_v ... no: Σ_tri (f_a²+f_b²+f_c²) = Σ_v τ_v f_v²  (τ_v = #triangles through v).
"""
import numpy as np, networkx as nx
from itertools import combinations


def fiedler(G):
    A = nx.to_numpy_array(G); d = A.sum(1); L = np.diag(d) - A
    ev, U = np.linalg.eigh(L); lam = ev[1]; f = U[:, 1]; f = f / np.linalg.norm(f)
    return A, d, lam, f


def triangles(G):
    A = nx.to_numpy_array(G); n = len(A)
    tris = []
    adj = [set(np.where(A[i] > 0)[0]) for i in range(n)]
    for a in range(n):
        for b in adj[a]:
            if b <= a: continue
            for c in adj[a] & adj[b]:
                if c > b: tris.append((a, b, c))
    return tris


def stats(name, G):
    G = nx.convert_node_labels_to_integers(G)
    if not nx.is_connected(G): return None
    A, d, lam, f = fiedler(G)
    n = len(A); mE = G.number_of_edges()
    A2 = A @ A
    tau = np.array([0.5 * sum(A[i, k] for j in range(n) for k in range(n)
                              if A[i, j] and A[i, k] and A[j, k]) for i in range(n)])  # triangles thru i
    # T_und and degQuad
    Tund = 0.0; degQuad = float(d @ (f * f))
    Am = np.triu(A, 1); ii, jj = np.where(Am > 0)
    te = {}
    for i, j in zip(ii, jj):
        t = int(A2[i, j]); te[(i, j)] = t
        Tund += t * (f[i] - f[j]) ** 2
    agg_ratio = Tund / (lam * degQuad) if lam * degQuad > 1e-12 else float('nan')
    # direction-AGNOSTIC crude local bound: gaps ≤ 4(f_a²+f_b²+f_c²) ⇒ T ≤ 4 Σ τ_v f_v²
    crude = 4 * float(tau @ (f * f))
    crude_ratio = crude / (lam * degQuad) if lam * degQuad > 1e-12 else float('nan')
    # per-vertex closure condition for crude bound: 4 τ_v ≤ λ d_v
    pv = np.array([4 * tau[v] / (lam * d[v]) if lam * d[v] > 1e-12 else 0.0 for v in range(n)])
    pv_max = float(pv.max())
    # TASK 1/3 circularity: RHS of link expansion / T   (should be 4)
    rhs = 0.0
    for (a, b, c) in triangles(G):
        for (x, y, z) in [(a, b, c), (b, c, a), (c, a, b)]:  # base (x,y), apex z
            rhs += 2 * ((f[x] - f[z]) ** 2 + (f[z] - f[y]) ** 2)
    circ = rhs / Tund if Tund > 1e-12 else float('nan')
    # TASK 4 Fisher normalizations: Σ_e t_e g_e² / w_e  (per-edge weight)
    norms = {'d_a+d_b': 0.0, 'min(d_a,d_b)': 0.0, 'sqrt(d_a d_b)': 0.0}
    for (i, j), t in te.items():
        g2 = (f[i] - f[j]) ** 2
        norms['d_a+d_b'] += t * g2 / (d[i] + d[j])
        norms['min(d_a,d_b)'] += t * g2 / min(d[i], d[j])
        norms['sqrt(d_a d_b)'] += t * g2 / np.sqrt(d[i] * d[j])
    sumf2 = float(f @ f)  # = 1
    return dict(name=name, n=n, lam=lam, degQuad=degQuad, Tund=Tund, agg=agg_ratio,
                crude=crude_ratio, pv_max=pv_max, circ=circ,
                nd=norms['d_a+d_b'] / (lam * sumf2), nm=norms['min(d_a,d_b)'] / (lam * sumf2),
                ns=norms['sqrt(d_a d_b)'] / (lam * sumf2),
                tris=triangles(G), A=A, d=d, lamv=lam, fv=f, A2=A2, tau=tau)


# ---- corpus: cliques, dumbbells (bottlenecks), random, deg2/twin, grids, expanders ----
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
    ("K8", nx.complete_graph(8)), ("K15", nx.complete_graph(15)),
    ("dumbbell8", dumbbell(8)), ("dumbbell15", dumbbell(15)),
    ("gnp30_0.3", nx.gnp_random_graph(30, 0.3, seed=1)),
    ("gnp30_0.6", nx.gnp_random_graph(30, 0.6, seed=2)),
    ("deg2d40_0.6", deg2d(40, 0.6, 7)), ("deg2d60_0.4", deg2d(60, 0.4, 7)),
    ("twin30_3", twin(30, 3)), ("twin50_2", twin(50, 2)),
    ("powerlaw50", nx.barabasi_albert_graph(50, 3, seed=4)),
    ("ws40", nx.watts_strogatz_graph(40, 6, 0.3, seed=5)),
    ("grid5x5", nx.triangular_lattice_graph(4, 4)),
]
R = [stats(nm, G) for nm, G in corpus]; R = [r for r in R if r]

print("=" * 92)
print("TASK 1/3 CIRCULARITY + aggregate slack + direction-agnostic crude local bound")
print("=" * 92)
print(f"{'graph':<14}{'lam':<8}{'agg=T/(λDQ)':<13}{'crude/(λDQ)':<13}{'max 4τv/λdv':<13}{'circ RHS/T'}")
for r in R:
    print(f"{r['name']:<14}{r['lam']:<8.3f}{r['agg']:<13.3f}{r['crude']:<13.2f}{r['pv_max']:<13.2f}{r['circ']:.3f}")
print("\n  agg<1 everywhere = conjecture holds (with big slack).")
print("  circ=4 confirms link-expansion regenerates T (T ≤ 4T): CIRCULAR.")
print("  crude/(λDQ)>1 or max 4τv/λdv>1 = direction-agnostic local bound FAILS to close.")

print("\n" + "=" * 92)
print("TASK 4 FISHER NORMALIZATIONS:  [Σ_e t_e g_e² / w_e] / (λ·‖f‖²)   -- universal & small?")
print("=" * 92)
print(f"{'graph':<14}{'/(d_a+d_b)':<13}{'/min(d)':<13}{'/sqrt(d_a d_b)':<15}")
for r in R:
    print(f"{r['name']:<14}{r['nd']:<13.4f}{r['nm']:<13.4f}{r['ns']:<15.4f}")

print("\n" + "=" * 92)
print("TASK 2 LOCAL TRIANGLE VARIANCE vs local function  -- is Var_tri ≤ g(d_a,d_b,d_c,λ)?")
print("=" * 92)
# For each graph: among triangles with the SAME local degree-triple, how much does Var_tri spread?
# Big spread ⇒ no local functional bound. Also test candidate bound Var ≤ λ²·meanf²/(min d)².
for r in R[:6] + [R[2]]:  # include dumbbell
    f = r['fv']; d = r['d']
    rows = []
    for (a, b, c) in r['tris']:
        vals = np.array([f[a], f[b], f[c]]); var = float(vals.var())
        key = tuple(sorted((int(d[a]), int(d[b]), int(d[c]))))
        meanf2 = float((vals ** 2).mean()); dmin = min(d[a], d[b], d[c])
        rows.append((key, var, meanf2, dmin))
    if not rows: continue
    # group by degree-triple, report worst within-group spread (max/min var ratio)
    from collections import defaultdict
    grp = defaultdict(list)
    for key, var, mf2, dmin in rows: grp[key].append(var)
    spreads = [(max(v) / (min(v) + 1e-18), key, len(v)) for key, v in grp.items() if len(v) >= 3]
    spreads.sort(reverse=True)
    worst = spreads[0] if spreads else (1.0, None, 0)
    # candidate local bound ratio: Var_tri / (λ² meanf2 / dmin²)  -- want ≤ const universally
    cand = [var / (r['lamv'] ** 2 * mf2 / dmin ** 2 + 1e-18) for _, var, mf2, dmin in rows]
    print(f"{r['name']:<14} #tri={len(rows):<6} worst within-(deg-triple) Var spread "
          f"x{worst[0]:.1f} (triple {worst[1]}, n={worst[2]});  "
          f"cand-bound ratio range [{min(cand):.2g},{max(cand):.2g}]")
