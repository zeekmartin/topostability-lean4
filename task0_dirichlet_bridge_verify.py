"""TASK 0 — verify the three claims the Lean Dirichlet-partition bridge relies on,
on all 17 Case 2A corpus graphs.  If any fails, STOP (do not write Lean).

(a) partition identity:  D_core + D_cross + D_pp = lambda_2      (err < 1e-9)
(b) zero port-port triangles:  t_pp = 0
(c) tight three-class scalar closes:
        2*((delta-1)*D_cross + maxt_core*(lambda_2 - D_cross - D_pp)) <= RHS
    (note  lambda_2 - D_cross - D_pp = D_core  by (a), so this is the verified hcond)
"""
import numpy as np, networkx as nx


def split_ports(d):
    n = len(d); order = np.argsort(d); sd = d[order]
    gaps = [(sd[i + 1] - sd[i], i) for i in range(n - 1)]; gap, idx = max(gaps)
    return set(order[:idx + 1].tolist()) if (gap >= 2 and idx < n - 1) else set()


def check(G):
    G = nx.convert_node_labels_to_integers(G); n = G.number_of_nodes()
    if not nx.is_connected(G): return None
    A = nx.to_numpy_array(G); d = A.sum(1); L = np.diag(d) - A; A2 = A @ A
    ev, U = np.linalg.eigh(L); lam = ev[1]; f = U[:, 1]; f = f / np.linalg.norm(f)
    mE = G.number_of_edges(); dq = float(d @ (f * f)); dl = float(d @ f)
    req = 2 * lam * (lam + dl ** 2 / mE - dq)
    if req <= 1e-9: return None
    RHS = 2 * lam * (2 * dq - lam - dl ** 2 / mE)
    P = split_ports(d); Pl = np.array(sorted(P)); H = np.array(sorted(set(range(n)) - P))
    if len(H) < 2 or len(Pl) == 0: return None
    Am = np.triu(A, 1); inP = np.zeros(n, bool); inP[Pl] = True
    EW = (f[:, None] - f[None, :]) ** 2 * Am; Tri = A2 * Am
    cross = (inP[:, None] ^ inP[None, :]); core = (~inP[:, None]) & (~inP[None, :])
    pp = (inP[:, None]) & (inP[None, :])
    Dcross = float(EW[cross].sum()); Dcore = float(EW[core].sum()); Dpp = float(EW[pp].sum())
    tpp = float(Tri[pp].max()) if (pp & (Am > 0)).any() else 0.0
    delta = float(d[Pl].max()); maxt = float(Tri[core].max()) if (core & (Am > 0)).any() else 0.0
    err_partition = abs(Dcore + Dcross + Dpp - lam)
    scalar = 2 * ((delta - 1) * Dcross + maxt * (lam - Dcross - Dpp))
    return dict(err=err_partition, tpp=tpp, scalar=scalar, RHS=RHS, ratio=scalar / RHS)


def d2(nn, q, s):
    H = nx.gnp_random_graph(nn - 1, q, seed=s); H.add_node(nn - 1)
    H.add_edge(nn - 1, 0); H.add_edge(nn - 1, 1); return H
def twin(N, dd):
    K = nx.complete_graph(N); a, b = N, N + 1
    for x in (a, b):
        for w in range(dd): K.add_edge(x, w)
    K.add_node(N + 2); K.add_edge(N + 2, a); K.add_edge(N + 2, b); return K


gs = [(f"deg2d{nn}_{q}", d2(nn, q, 7)) for nn in [40, 60, 80] for q in [0.2, 0.4, 0.6, 0.85]]
gs += [(f"twin{N}_{dd}", twin(N, dd)) for N in [30, 50, 80] for dd in [2, 3, 4]]
R = [(nm, check(G)) for nm, G in gs]; R = [(nm, r) for nm, r in R if r]
N = len(R)

fa = sum(r["err"] > 1e-9 for _, r in R)
fb = sum(r["tpp"] > 1e-12 for _, r in R)
fc = sum(r["ratio"] > 1 + 1e-9 for _, r in R)
print(f"{N} Case 2A graphs")
print(f"(a) partition identity  D_core+D_cross+D_pp = lam : {N-fa}/{N} pass "
      f"(max err {max(r['err'] for _,r in R):.2e})")
print(f"(b) port-port triangles t_pp = 0                  : {N-fb}/{N} pass "
      f"(max t_pp {max(r['tpp'] for _,r in R):.0f})")
print(f"(c) 2[(d-1)Dcross + maxt(lam-Dcross-Dpp)] <= RHS   : {N-fc}/{N} pass "
      f"(max ratio {max(r['ratio'] for _,r in R):.4f})")
print("ALL PASS — proceed to Lean" if fa == fb == fc == 0 else "FAILURE — STOP")
