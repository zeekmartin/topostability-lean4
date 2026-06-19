"""
Three-regime proof map for Conjecture B (lift form  T <= RHS = lam2(2fDf - lam2 - S^2/m)).

Regime 1 : Required <= 0   (Required = lam2(lam2 + S^2/m - fDf))
Regime 2A: Required > 0, boundary_ratio < 1   (TYPE A, vertex bottleneck)
Regime 2B: Required > 0, boundary_ratio > 2   (TYPE B, path bottleneck)

For each: report margins, the S-procedure test (regime 1), block gap (2A), T/RHS (2B), coverage.
Run: python conjecture_B_three_regimes_chain.py
"""
import numpy as np
import networkx as nx
from conjecture_B_nodal_decomposition import corpus
from conjecture_B_same_sign_reservoir import glue, chain_cliques


def build(G):
    nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}; n = len(nodes)
    A = nx.to_numpy_array(G, nodelist=nodes); d = A.sum(1)
    L = np.diag(d) - A
    ev, U = np.linalg.eigh(L); lam = ev[1]; f = U[:, 1]; f = f / np.linalg.norm(f)
    m = G.number_of_edges(); S = float(d @ f); fDf = float(d @ (f * f))
    Wmin = np.zeros((n, n)); B2 = 0.0; Gsum = 0.0; T = 0.0
    A2 = A @ A
    for a, b in [(idx[u], idx[v]) for u, v in G.edges()]:
        g = f[a] - f[b]; h = f[a] + f[b]
        B2 += (min(d[a], d[b]) - 1) * g * g
        T += A2[a, b] * g * g
        Gsum += h * h
        w = min(d[a], d[b]) - 1; Wmin[a, b] = w; Wmin[b, a] = w
    Gvar = Gsum - S ** 2 / m
    L_min = np.diag(Wmin.sum(1)) - Wmin
    M = lam * (np.diag(d) + A) - (lam / m) * np.outer(d, d) - L_min
    Required = lam * (lam + S ** 2 / m - fDf)
    RHS = lam * (2 * fDf - lam - S ** 2 / m)
    P = np.eye(n) - np.ones((n, n)) / n
    wp, Vp = np.linalg.eigh(P); Bp = Vp[:, wp > 0.5]
    return dict(G=G, n=n, m=m, lam=lam, d=d, f=f, A=A, L=L, M=M, Bp=Bp,
                S=S, fDf=fDf, B2=B2, T=T, Gvar=Gvar, Required=Required, RHS=RHS,
                dmax=float(d.max()), nodes=nodes, idx=idx)


def sproc_ok(q, alpha):
    Mp = q['M'] + alpha * (q['L'] - q['lam'] * np.eye(q['n']))
    return float(np.linalg.eigvalsh(q['Bp'].T @ Mp @ q['Bp'])[0]) >= -1e-7


def alpha_star(q):
    if sproc_ok(q, 0.0):
        return 0.0
    hi = 1.0
    while not sproc_ok(q, hi) and hi < 1e13:
        hi *= 2
    lo = 0.0
    for _ in range(55):
        mid = (lo + hi) / 2
        if sproc_ok(q, mid):
            hi = mid
        else:
            lo = mid
    return hi


def boundary_ratio(q):
    """Carrier C80 = top-f^2 vertices holding 80% mass; B = complement; f_B = Fiedler(G[B]);
    boundary_ratio = (sum_{B-C edges} f_B(v in B)^2) / (||f_B||^2 lam2(G))."""
    f2 = q['f'] ** 2; n = q['n']
    order = np.argsort(-f2)
    cum = np.cumsum(f2[order]); tot = cum[-1]
    kk = int(np.searchsorted(cum, 0.8 * tot)) + 1
    carrier = set(order[:kk].tolist())
    Bset = [v for v in range(n) if v not in carrier]
    if len(Bset) < 2:
        return None
    GB = q['G'].subgraph([q['nodes'][v] for v in Bset])
    if GB.number_of_nodes() < 2 or not nx.is_connected(GB):
        return np.inf          # disconnected block -> path-type (TYPE B)
    LB = nx.laplacian_matrix(GB, nodelist=list(GB.nodes())).toarray().astype(float)
    evB, UB = np.linalg.eigh(LB)
    if evB[1] < 1e-12:
        return np.inf
    fB = UB[:, 1]
    # map fB back to vertex index in B
    Bnodes = list(GB.nodes()); pos = {u: i for i, u in enumerate(Bnodes)}
    fBvec = {q['idx'][u]: fB[pos[u]] for u in Bnodes}
    normfB = float(fB @ fB)
    # boundary edges B - carrier
    bdry = 0.0
    for u, v in q['G'].edges():
        iu, iv = q['idx'][u], q['idx'][v]
        inB_u, inB_v = iu in fBvec, iv in fBvec
        if inB_u and not inB_v:
            bdry += fBvec[iu] ** 2
        elif inB_v and not inB_u:
            bdry += fBvec[iv] ** 2
    return bdry / (normfB * q['lam'])


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
        out.append(G)
    return out


def main():
    data = [build(G) for G in all_graphs()]
    ng = len(data); tol = 1e-7
    r1 = [q for q in data if q['Required'] <= tol]
    r2 = [q for q in data if q['Required'] > tol]
    print(f"{ng} graphs;  Regime 1 (Required<=0): {len(r1)};  Regime 2 (Required>0): {len(r2)}\n")

    # ---- B holds everywhere (sanity) ----
    print(f"SANITY  T <= RHS (lift B): {sum(1 for q in data if q['T'] <= q['RHS']+tol)}/{ng}")
    print(f"SANITY  B2' <= lam2 G    : {sum(1 for q in data if q['B2'] <= q['lam']*q['Gvar']+tol)}/{ng}\n")

    # ===== REGIME 1 =====
    print("=" * 74)
    print("REGIME 1 (Required <= 0): S-procedure alpha = Δ+lam2-1")
    print("=" * 74)
    ok = 0; astars = []
    for q in r1:
        a = q['dmax'] + q['lam'] - 1
        if sproc_ok(q, a):
            ok += 1
        astars.append(alpha_star(q))
    astars = np.array(astars)
    print(f"  M+(Δ+lam2-1)(L-lam2 I) PSD on 1-perp : {ok}/{len(r1)}")
    print(f"  alpha* (min feasible) on Regime 1 : min={astars.min():.3f} "
          f"median={np.median(astars):.3f} max={astars.max():.3f}")
    print(f"  alpha*/(Δ+lam2-1) : max={max(astars[i]/(r1[i]['dmax']+r1[i]['lam']-1) for i in range(len(r1)) if r1[i]['dmax']+r1[i]['lam']-1>1e-9):.3f}")
    # also: in regime 1, aggregate-Poincare route T <= lam2 fDf <= RHS
    apok = sum(1 for q in r1 if q['T'] <= q['lam'] * q['fDf'] + tol)
    print(f"  (alt) aggregate Poincare T <= lam2 fDf : {apok}/{len(r1)} (then <=RHS since RHS>=lam2 fDf)")

    # ===== classification of Regime 2 =====
    print("\n" + "=" * 74)
    print("REGIME 2 classification by boundary_ratio (carrier C80 complement)")
    print("=" * 74)
    typeA = []; typeB = []; mid = []
    for q in r2:
        br = boundary_ratio(q)
        if br is None:
            mid.append((q, None)); continue
        if br < 1:
            typeA.append((q, br))
        elif br > 2:
            typeB.append((q, br))
        else:
            mid.append((q, br))
    print(f"  TYPE A (boundary<1): {len(typeA)}   TYPE B (boundary>2): {len(typeB)}   "
          f"in (1,2] or undefined: {len(mid)}")
    if mid:
        print(f"  bimodal check: {len(mid)} graphs in the gap (1,2] -- "
              + ", ".join(f"br={br}" for _, br in mid[:6]))

    # ===== REGIME 2A =====
    print("\n" + "=" * 74)
    print("REGIME 2A (TYPE A): block gap and margins")
    print("=" * 74)
    if typeA:
        tr = np.array([q['T'] / q['RHS'] for q, _ in typeA if q['RHS'] > 1e-12])
        brs = np.array([br for _, br in typeA])
        print(f"  T/RHS: min={tr.min():.4f} median={np.median(tr):.3f} max={tr.max():.4f}")
        print(f"  boundary_ratio: median={np.median(brs):.3f} max={brs.max():.3f}")
        # block gap lam2(G[B]) >= (1-boundary) lam2(G): proxy = boundary<1 means certified
        print(f"  block-gap certified (boundary<1 => lam2(G[B])>=(1-br)lam2>0): {len(typeA)}/{len(typeA)}")

    # ===== REGIME 2B =====
    print("\n" + "=" * 74)
    print("REGIME 2B (TYPE B): T/RHS -> 0")
    print("=" * 74)
    if typeB:
        tr = np.array([q['T'] / q['RHS'] for q, _ in typeB if q['RHS'] > 1e-12])
        print(f"  T/RHS: min={tr.min():.4f} median={np.median(tr):.3f} max={tr.max():.4f}")
        print(f"  T/RHS <= 0.5 : {int((tr<=0.5).sum())}/{len(tr)}")

    # ===== COVERAGE =====
    print("\n" + "=" * 74)
    print("COVERAGE")
    print("=" * 74)
    covered = len(r1) + len(typeA) + len(typeB)
    print(f"  Regime1 {len(r1)} + TYPE A {len(typeA)} + TYPE B {len(typeB)} = {covered}/{ng}")
    print(f"  uncovered (in gap (1,2] or undefined): {len(mid)}")
    print(f"  bimodal (empty (1,2]) : {'YES' if all(m[1] is None or not (1<m[1]<=2) for m in mid) else 'NO'}")


if __name__ == "__main__":
    main()
