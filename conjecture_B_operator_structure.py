"""
Operator structure of Q = lam*D - L_t on the Fiedler eigenspace E_{lam2}.
L_t = diag(rowsum(A^2 o A)) - (A^2 o A) (triangle Laplacian). f^T Q f = lam*degQuad - T_unord >= 0 (aggregate).
TASK1 spectrum of Q; TASK2 Qf structure; TASK3 commutator [L_t,L]; TASK4 S-procedure multiplier M.
Run: python conjecture_B_operator_structure.py
"""
import numpy as np
import networkx as nx
from scipy.optimize import minimize


def build(G):
    G = nx.convert_node_labels_to_integers(G); n = G.number_of_nodes()
    A = nx.to_numpy_array(G); d = A.sum(1); L = np.diag(d) - A; A2 = A @ A
    ev, U = np.linalg.eigh(L); lam = ev[1]; f = U[:, 1]; f = f / np.linalg.norm(f)
    Had = A2 * A; Lt = np.diag(Had.sum(1)) - Had
    D = np.diag(d)
    Q = lam * D - Lt
    return dict(n=n, A=A, d=d, L=L, ev=ev, U=U, lam=lam, f=f, Lt=Lt, D=D, Q=Q)


def analyze(G, name, do_sproc=True):
    B = build(G); n = B['n']; Q = B['Q']; f = B['f']; L = B['L']; lam = B['lam']
    ev, U = B['ev'], B['U']; D = B['D']; Lt = B['Lt']
    # TASK 1: spectrum of Q
    qev, qvec = np.linalg.eigh(Q)
    nneg = int((qev < -1e-7).sum())
    # Fiedler overlap with negative eigenspace of Q
    neg_idx = np.where(qev < -1e-7)[0]
    overlap_neg = float(np.sqrt(sum((qvec[:, k] @ f) ** 2 for k in neg_idx))) if len(neg_idx) else 0.0
    fQf = float(f @ Q @ f)
    # TASK 2: r = Qf, projections
    r = Q @ f; rn = np.linalg.norm(r)
    one = np.ones(n) / np.sqrt(n)
    p_f = (r @ f); p_1 = (r @ one)
    # projection onto E_lam2 (mult) and onto range(L-lam)
    mult = int((np.abs(ev - lam) < 1e-6).sum())
    Eidx = np.where(np.abs(ev - lam) < 1e-6)[0]
    PE = U[:, Eidx] @ U[:, Eidx].T
    r_inE = np.linalg.norm(PE @ r); r_outE = np.linalg.norm(r - PE @ r)
    # TASK 3: commutator [L_t, L] f
    comm = Lt @ L - L @ Lt
    commf = np.linalg.norm(comm @ f)
    # does L_t preserve E_lam2? ||(I-PE) L_t f||
    preserve = np.linalg.norm((np.eye(n) - PE) @ (Lt @ f))
    LtfE = np.linalg.norm(PE @ (Lt @ f))
    out = dict(name=name, n=n, lam=lam, fQf=fQf, minQ=qev[0], nneg=nneg, overlap_neg=overlap_neg,
               rn=rn, p_f=p_f, p_1=p_1, mult=mult, r_inE=r_inE, r_outE=r_outE,
               commf=commf, preserve=preserve, LtfE=LtfE, normf_Ltf=np.linalg.norm(Lt @ f))
    # TASK 4: S-procedure  Q + C M + M C >= 0, C=L-lam I, M = a I + b D + c L (symmetric)
    if do_sproc:
        C = L - lam * np.eye(n)
        def minus_min_eig(x):
            a, b, c = x
            M = a * np.eye(n) + b * D + c * L
            S = Q + C @ M + M @ C
            return -np.linalg.eigvalsh(S)[0]
        best = None
        for x0 in [(0, 0, 0), (1, 0, 0), (0, 1, 0), (0, 0, 1), (-1, 1, 0), (1, -1, 0)]:
            res = minimize(minus_min_eig, x0, method='Nelder-Mead',
                           options={'xatol': 1e-4, 'fatol': 1e-6, 'maxiter': 2000})
            if best is None or res.fun < best[0]: best = (res.fun, res.x)
        out['sproc_mineig'] = -best[0]      # max achievable min-eig of Q+CM+MC
        out['sproc_M'] = best[1]
    return out


def main():
    def d2(nn, q, s):
        H = nx.gnp_random_graph(nn - 1, q, seed=s); H.add_node(nn - 1); H.add_edge(nn - 1, 0); H.add_edge(nn - 1, 1); return H
    def twin(N, dd):
        K = nx.complete_graph(N); a, b = N, N + 1
        for x in (a, b):
            for w in range(dd): K.add_edge(x, w)
        K.add_node(N + 2); K.add_edge(N + 2, a); K.add_edge(N + 2, b); return K
    reps = [
        ("K12", nx.complete_graph(12)),
        ("rr20_6", nx.random_regular_graph(6, 20, seed=1)),
        ("deg2d40_0.6", d2(40, 0.6, 7)),
        ("deg2d40_0.2", d2(40, 0.2, 7)),
        ("twin30_2", twin(30, 2)),
        ("lolli15_12", nx.lollipop_graph(15, 12)),
        ("gnp30_0.5", nx.gnp_random_graph(30, 0.5, seed=3)),
        ("cocktail6", nx.complete_multipartite_graph(*([2] * 6))),
    ]
    res = [analyze(G, nm) for nm, G in reps]

    print("=" * 100)
    print("TASK 1 — spectrum of Q=λD-L_t: f^T Q f (>=0?), min eig, #neg, Fiedler overlap w/ neg eigenspace")
    print("=" * 100)
    print(f"  {'graph':12s} {'fQf':>9} {'minQ':>9} {'#neg':>5} {'mult':>5} {'overlap(f,neg)':>14}")
    for q in res:
        print(f"  {q['name']:12s} {q['fQf']:9.4f} {q['minQ']:9.3f} {q['nneg']:5d} {q['mult']:5d} {q['overlap_neg']:14.2e}")

    print("\n" + "=" * 100)
    print("TASK 2 — r=Qf: ||r||, proj on f and 1, in/out of E_{λ₂}")
    print("=" * 100)
    print(f"  {'graph':12s} {'||r||':>9} {'<r,f>':>9} {'<r,1norm>':>10} {'||PE r||':>9} {'||(I-PE)r||':>11}")
    for q in res:
        print(f"  {q['name']:12s} {q['rn']:9.3f} {q['p_f']:9.4f} {q['p_1']:10.2e} {q['r_inE']:9.4f} {q['r_outE']:11.4f}")
    print("  (if ||(I-PE)r|| >> ||PE r||: Qf mostly leaves E_{λ₂} => Q does NOT preserve it)")

    print("\n" + "=" * 100)
    print("TASK 3 — commutator [L_t,L]f and L_t-preservation of E_{λ₂}")
    print("=" * 100)
    print(f"  {'graph':12s} {'||[Lt,L]f||':>12} {'||Lt f||':>9} {'||PE Lt f||':>11} {'||(I-PE)Lt f||':>14}")
    for q in res:
        print(f"  {q['name']:12s} {q['commf']:12.4f} {q['normf_Ltf']:9.3f} {q['LtfE']:11.4f} {q['preserve']:14.4f}")
    print("  (||(I-PE)Lt f|| small => L_t nearly preserves E_{λ₂})")

    print("\n" + "=" * 100)
    print("TASK 4 — S-procedure: max min-eig of Q + CM + MC, C=L-λI, M=aI+bD+cL (>=0 => certificate)")
    print("=" * 100)
    print(f"  {'graph':12s} {'minQ (no M)':>12} {'best min-eig (with M)':>22} {'M=(a,b,c)':>22}")
    for q in res:
        Mc = q.get('sproc_M', [0, 0, 0])
        print(f"  {q['name']:12s} {q['minQ']:12.3f} {q['sproc_mineig']:22.4f} "
              f"({Mc[0]:.2f},{Mc[1]:.2f},{Mc[2]:.2f})")
    print("  (best min-eig >= 0 => Q+CM+MC PSD => Q PSD on E_{λ₂} with explicit multiplier M)")

    print("\n" + "=" * 100)
    print("SUMMARY")
    print("=" * 100)
    cert = sum(1 for q in res if q['sproc_mineig'] >= -1e-4)
    print(f"  S-procedure (M=aI+bD+cL) certifies Q⪰0 on E_λ₂: {cert}/{len(res)}")
    print(f"  Fiedler overlap with Q-negative eigenspace: max {max(q['overlap_neg'] for q in res):.2e} "
          f"(small => f nearly orthogonal to negative directions)")


if __name__ == "__main__":
    main()
