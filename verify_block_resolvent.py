"""TASK 1 verification (vectorized): the 4 checks for the block resolvent bound on 17 Case 2A graphs."""
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
    Am = np.triu(A, 1)                                   # upper edges
    inP = np.zeros(n, bool); inP[Pl] = True
    EW = (f[:, None] - f[None, :]) ** 2 * Am             # edge g² (upper)
    portmask = (inP[:, None] ^ inP[None, :])
    Dport = float(EW[portmask].sum())
    coremask = (~inP[:, None]) & (~inP[None, :])
    Dcore = float(EW[coremask].sum())
    delta = float(d[Pl].max()); maxt = float((A2 * Am)[coremask].max()) if coremask.any() else 0.0
    Ah = A[np.ix_(H, H)]; Lh = np.diag(Ah.sum(1)) - Ah
    evh, Uh = np.linalg.eigh(Lh); gamma = evh[1]
    fH = f[H]; s = Lh @ fH - lam * fH; s2 = float(s @ s)
    w = np.where(evh > 1e-9, evh / np.where(np.abs(evh - lam) > 1e-9, (evh - lam) ** 2, np.inf), 0.0)
    M = (Uh * w) @ Uh.T                                  # R L_H R  (Dirichlet resolvent)
    Hidx = {v: i for i, v in enumerate(H)}
    dD = [Hidx[v] for v in H if A[v, Pl].sum() > 0]
    Dcore_quad = float(s @ M @ s)
    lmax_blk = float(np.linalg.eigvalsh(M[np.ix_(dD, dD)])[-1])
    return (abs(s2 - Dport), abs(Dcore - Dcore_quad), lmax_blk * Dport - Dcore,
            2 * ((delta - 1) * Dport + maxt * lmax_blk * s2) / RHS, len(dD))


def d2(nn, q, s):
    H = nx.gnp_random_graph(nn - 1, q, seed=s); H.add_node(nn - 1); H.add_edge(nn - 1, 0); H.add_edge(nn - 1, 1); return H
def twin(N, dd):
    K = nx.complete_graph(N); a, b = N, N + 1
    for x in (a, b):
        for w in range(dd): K.add_edge(x, w)
    K.add_node(N + 2); K.add_edge(N + 2, a); K.add_edge(N + 2, b); return K


gs = [(f"deg2d{nn}_{q}", d2(nn, q, 7)) for nn in [40, 60, 80] for q in [0.2, 0.4, 0.6, 0.85]]
gs += [(f"twin{N}_{dd}", twin(N, dd)) for N in [30, 50, 80] for dd in [2, 3, 4]]
res = [(nm, check(G)) for nm, G in gs]; res = [(nm, r) for nm, r in res if r]
fa = sum(r[0] > 1e-7 for _, r in res); fb = sum(r[1] > 1e-7 for _, r in res)
fc = sum(r[2] < -1e-7 for _, r in res); fd = sum(r[3] > 1 + 1e-7 for _, r in res)
N = len(res)
print(f"{N} Case 2A graphs; |∂| range {min(r[4] for _,r in res)}–{max(r[4] for _,r in res)}")
print(f"(a) ||s||^2 = D_port            : {N-fa}/{N} pass (max err {max(r[0] for _,r in res):.2e})")
print(f"(b) D_core = s^T M_dD s exact   : {N-fb}/{N} pass (max err {max(r[1] for _,r in res):.2e})")
print(f"(c) lmax(M_dD)*D_port >= D_core : {N-fc}/{N} pass (min slack {min(r[2] for _,r in res):.4f})")
print(f"(d) hcond closes (2[...]/RHS<=1): {N-fd}/{N} pass (max ratio {max(r[3] for _,r in res):.4f})")
print("ALL PASS" if fa == fb == fc == fd == 0 else "FAILURE - STOP")
