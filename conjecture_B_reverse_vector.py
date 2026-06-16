"""
Reverse-engineer the test vector g for  target := C+R'' = gᵀ(L-λ₂)g  (g ⊥ {1,f}).

KEY SUBTLETY: the MIN-NORM g* with g*ᵀMg*=target (M=L-λ₂I on {1,f}⊥) is, by Lagrange,
the TOP eigenvector of L (largest μ minimizes ‖g‖²) — it encodes only target's
magnitude, not structure. So we test it (expect uninformative) AND the real question:
is target = gᵀ(L-λ₂)g for g a UNIVERSAL polynomial-in-(D,A) image of f?

TASK1: compute min-norm g*, regress its per-vertex values on features (expect low R²).
TASK2: feature vectors φ_k (projected ⊥{1,f}); regress target on pairwise energies
       P_kl = φ_kᵀ(L-λ₂)φ_l → universal-g feasibility (R²) + rank-1/PSD of coeff matrix.
TASK3: cross-check review candidates.
Run:  python conjecture_B_reverse_vector.py
"""
import numpy as np
import networkx as nx
import counterexample_search as ce


def proj(w, ones, f, n):
    w = w - (w @ ones / n) * ones
    w = w - (w @ f) * f
    return w


def data(G):
    nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}
    edges = list(G.edges()); n, m = len(nodes), len(edges)
    L = nx.laplacian_matrix(G, nodelist=nodes).toarray().astype(float)
    d = L.diagonal().copy(); A = np.diag(d) - L
    ev, V = np.linalg.eigh(L); l2 = float(ev[1]); f = V[:, 1] / np.linalg.norm(V[:, 1])
    ones = np.ones(n); dbar = d.mean()
    S = float(d @ f); fDf = float((d * f * f).sum())
    Rpp = l2 * (fDf - l2 + 1 - S * S / m)
    C = 0.0
    for u, v in edges:
        i, j = idx[u], idx[v]
        h, lo = (i, j) if d[i] >= d[j] else (j, i)
        C += (d[h] - d[lo]) * f[h] * (f[h] - f[lo])
    target = C + Rpp
    M = L - l2 * np.eye(n)

    # --- min-norm g*: top eigenvector of L (largest μ=λ_n-λ₂) scaled to energy=target ---
    un = V[:, -1] / np.linalg.norm(V[:, -1])           # top Laplacian eigenvector
    mu_top = float(ev[-1] - l2)
    gstar = np.sqrt(max(target, 0) / mu_top) * un if mu_top > 1e-9 else np.zeros(n)
    # check: is gstar ⊥ f and ⊥1 ? (yes generically)

    # --- feature vectors (vertex space) ---
    Af = A @ f; A2f = A @ Af; Df = d * f; D2f = d * d * f
    gradf = np.array([sum((d[idx[w]] - d[idx[u]]) * f[idx[w]] for w in G[u]) for u in nodes])
    feats = {
        "f": f, "d": d.copy(), "Df": Df, "D2f": D2f, "Af": Af, "A2f": A2f,
        "gradf": gradf, "(d-db)f": (d - dbar) * f, "(d-db)2f": (d - dbar) ** 2 * f,
    }
    # per-vertex feature matrix for regressing g*_v
    fnames = list(feats.keys())
    Fmat = np.array([feats[k] for k in fnames]).T       # n x 9
    # projected features for energy regression
    pf = {k: proj(v.copy(), ones, f, n) for k, v in feats.items()}
    # pairwise energies
    P = {}
    for a in range(len(fnames)):
        for b in range(a, len(fnames)):
            P[(fnames[a], fnames[b])] = float(pf[fnames[a]] @ (M @ pf[fnames[b]]))

    # --- review cross-check candidates ---
    xQ = proj((d * f + Af), ones, f, n)                 # (D+A)f projected
    xdown = np.array([sum((f[idx[u]] - f[idx[w]]) for w in G[u] if d[idx[w]] > d[idx[u]])
                      for u in nodes])                  # Σ_{u~v,d_u>d_v}(f_v-f_u)
    xdown_p = proj(xdown, ones, f, n)
    eQ = float(xQ @ (M @ xQ)); edown = float(xdown_p @ (M @ xdown_p))

    return dict(n=n, m=m, l2=l2, target=target, gstar=gstar, Fmat=Fmat, fnames=fnames,
                P=P, eQ=eQ, edown=edown, mu_top=mu_top)


def corpus(maxn=9):
    seen = {}
    for tag, exh, G in ce._gen_graphs_hier(maxn):
        if G.number_of_nodes() < 3 or not nx.is_connected(G):
            continue
        T = ce.triangle_graph(G)
        if T.number_of_nodes() < 2 or not nx.is_connected(T):
            continue
        key = (G.number_of_nodes(), G.number_of_edges(),
               nx.weisfeiler_lehman_graph_hash(G, iterations=3))
        if key not in seen:
            seen[key] = G.copy()
    return list(seen.values())


def r2(y, pred):
    y = np.asarray(y); pred = np.asarray(pred)
    ss = ((y - pred) ** 2).sum(); tot = ((y - y.mean()) ** 2).sum()
    return 1 - ss / tot if tot > 0 else 0.0


def main():
    graphs = corpus(9)
    rows = [data(G) for G in graphs]
    rows = [r for r in rows if r["l2"] > 1e-6 and r["mu_top"] > 1e-9]
    N = len(rows)
    print(f"distinct corpus graphs: {N}")
    fnames = rows[0]["fnames"]

    # ===== TASK 1: min-norm g* is the top Laplacian eigenvector — regress on features =====
    print("\n===== TASK 1: min-norm g* = top L-eigenvector (regress g*_v on features) =====")
    # per-graph R² of regressing g*_v on the 9 features (sign/scale-free via R²)
    r2s = []
    for r in rows:
        y = r["gstar"]
        if np.linalg.norm(y) < 1e-12:
            continue
        coef, *_ = np.linalg.lstsq(r["Fmat"], y, rcond=None)
        r2s.append(r2(y, r["Fmat"] @ coef))
    r2s = np.array(r2s)
    print(f"  per-graph R²(g*_v ~ all 9 features): median={np.median(r2s):.3f} "
          f"mean={r2s.mean():.3f}  (>0.95 on {100*np.mean(r2s>0.95):.0f}%)")
    print("  => min-norm g* is the highest-frequency Laplacian mode; NOT a low-order")
    print("     degree/Fiedler formula. Confirms min-norm reverse-engineering is degenerate.")

    # ===== TASK 2: universal-g feasibility via pairwise-energy regression =====
    print("\n===== TASK 2: is target = gᵀ(L-λ₂)g for universal g=Σc_k φ_k ? =====")
    tgt = np.array([r["target"] for r in rows])
    keys = list(rows[0]["P"].keys())
    Pmat = np.array([[r["P"][k] for k in keys] for r in rows])   # N x 45
    coef, *_ = np.linalg.lstsq(Pmat, tgt, rcond=None)
    pred = Pmat @ coef
    print(f"  regress target on all {len(keys)} pairwise energies P_kl: "
          f"R²={r2(tgt,pred):.4f}  maxResid={np.abs(tgt-pred).max():.3f}")

    # subsets: only diagonal energies (single-feature second variations)
    diagk = [k for k in keys if k[0] == k[1]]
    Pd = np.array([[r["P"][k] for k in diagk] for r in rows])
    cd, *_ = np.linalg.lstsq(Pd, tgt, rcond=None)
    print(f"  regress target on {len(diagk)} DIAGONAL energies only: R²={r2(tgt,Pd@cd):.4f}")

    # rank/PSD of the recovered coefficient matrix Φ (Φ_kl from coef; off-diag split /2... but
    # since P_kl already symmetric counted once, build Φ with Φ_kk=coef, Φ_kl=coef/... )
    nf = len(fnames); Phi = np.zeros((nf, nf)); ck = dict(zip(keys, coef))
    for a in range(nf):
        for b in range(a, nf):
            v = ck.get((fnames[a], fnames[b]), 0.0)
            if a == b:
                Phi[a, a] = v
            else:
                Phi[a, b] = Phi[b, a] = v / 2
    evPhi = np.linalg.eigvalsh(Phi)
    print(f"  recovered coeff matrix Φ eigenvalues: min={evPhi.min():.3f} max={evPhi.max():.3f} "
          f"(#neg={int(np.sum(evPhi<-1e-6))}) => {'PSD (g exists)' if evPhi.min()>=-1e-6 else 'INDEFINITE (no single g; signed combo only)'}")

    # ===== TASK 3: cross-check review candidates =====
    print("\n===== TASK 3: review candidates vs target =====")
    eQ = np.array([r["eQ"] for r in rows]); edown = np.array([r["edown"] for r in rows])
    print(f"  x=(D+A)f proj:  corr(energy,target)={np.corrcoef(eQ,tgt)[0,1]:+.3f}  "
          f"best-c R²={r2(tgt, (eQ@tgt/(eQ@eQ))*eQ):+.3f}")
    print(f"  x_v=Σ_{{u~v,d_u>d_v}}(f_v-f_u):  corr={np.corrcoef(edown,tgt)[0,1]:+.3f}  "
          f"best-c R²={r2(tgt, (edown@tgt/(edown@edown))*edown):+.3f}")

    main.rows = rows


if __name__ == "__main__":
    main()
