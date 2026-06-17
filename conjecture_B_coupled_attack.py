"""
Attack C+R'' >= 0 as a COUPLED quantity (do not bound |C| separately from R'').
C = Σ_{ab}(d_h-d_l) f_h (f_h-f_l);  R'' = λ₂(fᵀDf-λ₂+1-S²/m);  f=unit Fiedler.

TASK 1: |C|/R'' asymptote on deg2+dense to n=1000 (-> 1, or constant c<1?).
TASK 2: per-LOW-vertex C(l)=Σ_{h~l,d_h>d_l}(d_h-d_l)f_h(f_h-f_l); local Dirichlet
        E(l)=Σ_{u~l}(f_l-f_u)²; eigen-eq Σ(f_l-f_u)=λ₂f_l ⇒ λ₂²f_l²≤d_l E(l).
        test -C(l) ≤ α λ₂ E(l)  and  -C(l) ≤ α λ₂ d_l f_l².
TASK 3: perturbative Rayleigh — p' ⊥{1,f}, E_p=p'ᵀ(L-λ₂)p' ≥0 by minimality;
        does C+R'' relate to E_p for some natural p?
Run:  python conjecture_B_coupled_attack.py
"""
import numpy as np
import networkx as nx
import counterexample_search as ce


def core(G):
    nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}
    edges = list(G.edges()); n, m = len(nodes), len(edges)
    L = nx.laplacian_matrix(G, nodelist=nodes).toarray().astype(float)
    d = L.diagonal().copy(); A = np.diag(d) - L
    ev, V = np.linalg.eigh(L); l2 = float(ev[1]); f = V[:, 1] / np.linalg.norm(V[:, 1])
    fDf = float((d * f * f).sum()); S = float(d @ f)
    Rpp = l2 * (fDf - l2 + 1 - S * S / m)
    C = 0.0
    for u, v in edges:
        i, j = idx[u], idx[v]
        h, lo = (i, j) if d[i] >= d[j] else (j, i)
        C += (d[h] - d[lo]) * f[h] * (f[h] - f[lo])
    return dict(n=n, m=m, l2=l2, fDf=fDf, S=S, Rpp=Rpp, C=C, L=L, d=d, A=A,
                f=f, idx=idx, ev=ev, V=V, nodes=nodes)


def deg2dense(n, q, seed):
    rng = np.random.default_rng(seed)
    G = nx.gnp_random_graph(n - 1, q, seed=int(rng.integers(0, 2**31)))
    G = nx.relabel_nodes(G, {i: i + 1 for i in range(n - 1)}); G.add_node(0)
    for b in rng.choice(range(1, n), size=2, replace=False):
        G.add_edge(0, int(b))
    return G


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


# ---------- TASK 1 ----------
def task1():
    print("===== TASK 1: |C|/R'' asymptote on deg2+dense =====")
    print("   n   | samples | max |C|/R'' | max(1-(C+R'')/R'')  (B2' margin = C+R''/R'')")
    for n, reps in [(50, 8), (100, 6), (200, 4), (300, 3), (500, 2), (1000, 2)]:
        rs = []
        for s in range(reps):
            G = deg2dense(n, 0.65, seed=1000 + 100 * n + s)
            if not nx.is_connected(G):
                continue
            r = core(G)
            if r["Rpp"] > 1e-9:
                rs.append(abs(r["C"]) / r["Rpp"])
        if rs:
            print(f"  {n:5d} | {len(rs):7d} | {max(rs):11.4f} | margin min={1-max(rs):.4f}")


# ---------- TASK 2 ----------
def task2(rows, hard, label):
    # per-low-vertex bound  -C(l) <= α λ₂ E(l)   and   -C(l) <= α λ₂ d_l f_l²
    a_E = []; a_df = []; agg_close = 0; agg_tot = 0
    for r in rows:
        d = r["d"]; f = r["f"]; idx = r["idx"]; l2 = r["l2"]
        Cl = np.zeros(len(d)); El = np.zeros(len(d))
        # edges from adjacency (upper triangle)
        Aedges = np.argwhere(np.triu(r["A"], 1) > 0.5)
        for i, j in Aedges:
            if d[i] < d[j]:
                lo, h = i, j
            elif d[j] < d[i]:
                lo, h = j, i
            else:
                continue
            Cl[lo] += (d[h] - d[lo]) * f[h] * (f[h] - f[lo])
        # local Dirichlet E(l) over ALL neighbours
        for i, j in np.argwhere(r["A"] > 0.5):
            El[i] += (f[i] - f[j]) ** 2
        negl = Cl < -1e-12
        for l in np.where(negl)[0]:
            if l2 * El[l] > 1e-12:
                a_E.append(-Cl[l] / (l2 * El[l]))
            if l2 * d[l] * f[l] ** 2 > 1e-12:
                a_df.append(-Cl[l] / (l2 * d[l] * f[l] ** 2))
    a_E = np.array(a_E); a_df = np.array(a_df)
    print(f"  [{label}] per-low-vertex (over l with C(l)<0):")
    if len(a_E):
        print(f"     -C(l)/(λ₂E(l)): max={a_E.max():.3f} median={np.median(a_E):.3f} "
              f"(<1 on {100*np.mean(a_E<=1):.1f}%)")
    if len(a_df):
        print(f"     -C(l)/(λ₂ d_l f_l²): max={a_df.max():.3f} median={np.median(a_df):.3f} "
              f"(<1 on {100*np.mean(a_df<=1):.1f}%)")


# ---------- TASK 3 ----------
def proj(w, f, n):
    ones = np.ones(n)
    w = w - (w @ ones / n) * ones
    w = w - (w @ f) * f
    return w


def task3(rows, label):
    cands = {
        "(d-dbar)f": lambda d, f, l2: (d - d.mean()) * f,
        "f/d": lambda d, f, l2: f / d,
        "(d-λ)f": lambda d, f, l2: (d - l2) * f,
        "sign(d-med)f": lambda d, f, l2: np.sign(d - np.median(d)) * f,
    }
    tgt = np.array([r["C"] + r["Rpp"] for r in rows])
    print(f"  [{label}] perturbative Rayleigh: corr(C+R'', E_p) and best-c fit:")
    for name, fn in cands.items():
        Es = []
        for r in rows:
            n = len(r["d"]); p = proj(fn(r["d"], r["f"], r["l2"]), r["f"], n)
            if np.linalg.norm(p) < 1e-12:
                Es.append(0.0); continue
            Es.append(float(p @ (r["L"] - r["l2"] * np.eye(n)) @ p))
        Es = np.array(Es)
        cc = np.corrcoef(Es, tgt)[0, 1] if Es.std() > 0 else float("nan")
        c = float(Es @ tgt / (Es @ Es)) if Es @ Es > 0 else 0.0
        r2 = 1 - ((tgt - c * Es) ** 2).sum() / ((tgt - tgt.mean()) ** 2).sum()
        # does C+R'' <= c·E_p hold? (would need C+R'' bounded by a nonneg energy — wrong dir)
        # the useful test: is C+R'' = E_p exactly (ratio ~const)?
        print(f"     p={name:14s}: corr={cc:+.3f}  best-c={c:+.3f}  R²(c·E)={r2:+.3f}")


def main():
    task1()

    print("\n===== TASK 2 & 3 on n<=9 corpus + hard core =====")
    graphs = corpus(9)
    rows = [core(G) for G in graphs]
    rows = [r for r in rows if r["l2"] > 1e-6]
    hard = [r for r in rows if r["C"] < -1e-9 and r["Rpp"] > 1e-9]
    # also scale samples
    scale = []
    for n in (50, 100, 200):
        for s in range(4):
            G = deg2dense(n, 0.65, seed=7000 + n + s)
            if nx.is_connected(G):
                r = core(G)
                if r["Rpp"] > 1e-9:
                    scale.append(r)

    print("\n--- TASK 2 ---")
    task2(rows, hard, "corpus")
    task2(scale, scale, "deg2+dense n=50..200")

    print("\n--- TASK 3 ---")
    task3(rows, "corpus")
    task3(hard, "hard core")


if __name__ == "__main__":
    main()
