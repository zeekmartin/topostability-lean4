"""
Conjecture B — candidate lemmas for the uniform smallness of ρ = W/ΣH.

Lock (C4''):  W = Σ_{ab}(min(d_a,d_b)-δ)(f_a-f_b)²  ≤  R'' = λ₂(fᵀDf-λ₂+1-S²/m).
ρ := W/ΣH,  ΣH = Σ_{ab,w>0}(min(d_a,d_b)-δ).  Empirically ρ ≤ 0.104 λ₂.

GATING TEST (separation): a uniform ρ ≤ c·λ₂ can close the lock iff
   max_G ρ/λ₂   ≤   min_G R''/(λ₂·ΣH).
If separated, any c in the gap proves B (given a proof of ρ ≤ c λ₂).

Then one concrete candidate per direction:
  D1 weighted-Poincaré : W ≤ λ₂(fᵀDf-δ)         [ratio W/(λ₂(fDf-δ))]
  D2 level-set smooth  : per degree-level uphill energy share
  D3 rearrangement/mass: gradient mass G_w by weight class w; decay
  D4 normalized Laplac.: W ≤ μ₂·fᵀDf ; ρ ≤ μ₂·d̄   [μ₂ = normalized Fiedler value]
  D5 conductance/sweep : per-edge  g_e·min(d_a,d_b) ≤ c·λ₂  (inverse-degree gradient)

Run:  python conjecture_B_rho_lemmas.py
"""
import numpy as np
import networkx as nx
import counterexample_search as ce
from collections import defaultdict

TOL = 1e-9


def data(G):
    nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}
    L = nx.laplacian_matrix(G, nodelist=nodes).toarray().astype(float)
    d = L.diagonal().copy(); n = len(nodes); m = G.number_of_edges()
    ev, V = np.linalg.eigh(L); l2 = float(ev[1]); f = V[:, 1] / np.linalg.norm(V[:, 1])
    delta = float(d.min()); Delta = float(d.max())
    S = float(d @ f); fDf = float((d * f * f).sum())
    Rpp = l2 * (fDf - l2 + 1.0 - S * S / m)
    # normalized Laplacian Fiedler value μ₂
    Ln = nx.normalized_laplacian_matrix(G, nodelist=nodes).toarray().astype(float)
    mu2 = float(np.linalg.eigvalsh(Ln)[1])
    # edges with positive weight
    W = 0.0; SH = 0.0; m_up = 0
    Gw = defaultdict(float)                       # gradient mass by weight class
    Dplus_level = defaultdict(float)              # uphill energy by lower-endpoint degree
    max_g_min = 0.0                               # max g_e * min(d_a,d_b)
    for u, v in G.edges():
        i, j = idx[u], idx[v]
        mn = min(d[i], d[j]); w = mn - delta
        g = (f[i] - f[j]) ** 2
        if w > 0:
            W += w * g; SH += w; m_up += 1
            Gw[int(w)] += g
            Dplus_level[int(mn)] += g
        max_g_min = max(max_g_min, g * mn)
    rho = W / SH if SH > 1e-12 else 0.0
    return dict(n=n, m=m, d=d, delta=delta, Delta=Delta, l2=l2, mu2=mu2,
                fDf=fDf, S=S, Rpp=Rpp, W=W, SH=SH, m_up=m_up, rho=rho,
                Gw=dict(Gw), Dplus_level=dict(Dplus_level), max_g_min=max_g_min,
                dbar=2.0 * m / n)


def hard_set():
    import conjecture_B_proof_v4_explore as v4
    gs = [G for _, G in v4.tight_graphs()]
    gs += [G for _, G in v4.broad_graphs(1500)]
    rng = np.random.default_rng(99); seen = set(); ndense = 0
    while ndense < 600:
        n = int(rng.integers(8, 14)); p = float(rng.uniform(0.45, 0.95))
        G = nx.gnp_random_graph(n, p, seed=int(rng.integers(0, 2**31)))
        if not nx.is_connected(G):
            continue
        gs.append(G); ndense += 1
    # adversarial triangle-rich: dense Watts-Strogatz + planted-degree
    for _ in range(800):
        n = int(rng.integers(10, 30)); k = int(rng.integers(4, min(14, n - 1)))
        p = float(rng.uniform(0.05, 0.5))
        gs.append(nx.watts_strogatz_graph(n, k + (k % 2), p, seed=int(rng.integers(0, 2**31))))

    def keep(G):
        if G.number_of_nodes() < 3 or not nx.is_connected(G):
            return False
        T = ce.triangle_graph(G)
        return T.number_of_nodes() >= 2 and nx.is_connected(T) and ce.lambda2(T) > 1e-6
    return [G for G in gs if keep(G)]


def main():
    rows = [data(G) for G in hard_set()]
    rows = [r for r in rows if r["SH"] > 1e-9 and r["l2"] > 1e-6]   # nontrivial (irregular)
    N = len(rows)
    print(f"hard set (irregular, T(G)-connected): {N} graphs")

    # ===== GATING: separation =====
    rho_l2 = np.array([r["rho"] / r["l2"] for r in rows])
    sep_rhs = np.array([r["Rpp"] / (r["l2"] * r["SH"]) for r in rows])  # R''/(λ₂ΣH)
    print("\n=== GATING TEST (does uniform ρ ≤ c·λ₂ suffice?) ===")
    print(f"  max  ρ/λ₂            = {rho_l2.max():.4f}")
    print(f"  min  R''/(λ₂·ΣH)     = {sep_rhs.min():.4f}")
    sep = rho_l2.max() <= sep_rhs.min()
    print(f"  SEPARATED: {sep}  ->  uniform c in ({rho_l2.max():.4f}, {sep_rhs.min():.4f}) "
          f"{'CLOSES B if ρ≤cλ₂ provable' if sep else 'does NOT exist (overlap) -> need graph-dependent bound'}")
    # how often does ρ ≤ c λ₂ with c = max suffice per-graph (it's the lock)
    lock = sum(1 for r in rows if r["W"] <= r["Rpp"] + 1e-7)
    print(f"  (lock W<=R'' holds {lock}/{N})")

    # ===== D1 weighted Poincaré =====
    r1 = np.array([r["W"] / (r["l2"] * (r["fDf"] - r["delta"]))
                   for r in rows if r["fDf"] - r["delta"] > 1e-9])
    print("\n[D1] weighted Poincaré  W ≤ λ₂(fᵀDf-δ):")
    print(f"   max W/(λ₂(fDf-δ)) = {r1.max():.4f}  ({'holds' if r1.max()<=1+1e-6 else 'FAILS (ratio>1)'})  "
          f"pass {np.mean(r1<=1+1e-6)*100:.0f}%")

    # ===== D4 normalized Laplacian =====
    r4a = np.array([r["W"] / (r["mu2"] * r["fDf"]) for r in rows if r["mu2"] > 1e-9])
    r4b = np.array([r["rho"] / (r["mu2"] * r["dbar"]) for r in rows if r["mu2"] > 1e-9])
    # does μ₂·fDf ≤ R''?
    d4close = np.mean([r["mu2"] * r["fDf"] <= r["Rpp"] + 1e-7 for r in rows]) * 100
    print("\n[D4] normalized Laplacian (μ₂ = normalized Fiedler value):")
    print(f"   max W/(μ₂·fDf) = {r4a.max():.4f} (pass {np.mean(r4a<=1+1e-6)*100:.0f}%) ; "
          f"μ₂·fDf ≤ R'' on {d4close:.0f}%")
    print(f"   max ρ/(μ₂·d̄)   = {r4b.max():.4f}")

    # ===== D5 conductance/sweep: per-edge inverse-degree gradient =====
    r5 = np.array([r["max_g_min"] / r["l2"] for r in rows])
    print("\n[D5] sweep/conductance  g_e·min(d_a,d_b) ≤ c·λ₂ (inverse-degree gradient):")
    print(f"   max over edges of g_e·min/λ₂ = {r5.max():.4f}  (tightest c)")
    # if g_e ≤ cλ₂/min, then W ≤ cλ₂ Σ(1-δ/min) ≤ cλ₂·m_up ; does cλ₂ m_up ≤ R''?
    c5 = r5.max()
    d5close = np.mean([c5 * r["l2"] * r["m_up"] <= r["Rpp"] + 1e-7 for r in rows]) * 100
    print(f"   with c={c5:.3f}: c·λ₂·m_up ≤ R'' on {d5close:.0f}% (per-edge bound too lossy if low)")

    # ===== D3 gradient-mass decay by weight class =====
    print("\n[D3] gradient mass G_w by weight class (anticorrelation -> decay):")
    # aggregate: fraction of total gradient-on-positive-weight-edges at each weight,
    # and the W-share from the top weight class
    topshare = []
    decaying = 0
    for r in rows:
        Gw = r["Gw"]
        if not Gw:
            continue
        ws = sorted(Gw)
        masses = [Gw[w] for w in ws]
        Wparts = [w * Gw[w] for w in ws]
        topshare.append(Wparts[-1] / sum(Wparts) if sum(Wparts) > 0 else 0)
        # is gradient mass non-increasing in weight? (anticorrelation signature)
        if all(masses[i] >= masses[i+1] - 1e-12 for i in range(len(masses)-1)):
            decaying += 1
    topshare = np.array(topshare)
    print(f"   W-share from top weight class: mean={topshare.mean():.3f} max={topshare.max():.3f}")
    print(f"   gradient mass G_w monotone-decreasing in w: {decaying}/{len(topshare)} "
          f"({100*decaying/max(len(topshare),1):.0f}%)")

    # ===== D2 level-set smoothness =====
    print("\n[D2] uphill energy by lower-endpoint degree level (flat-at-hubs):")
    # for each graph, ratio of uphill gradient energy at the TOP half degree levels
    hi_share = []
    for r in rows:
        DL = r["Dplus_level"]
        if not DL:
            continue
        lv = sorted(DL)
        mid = lv[len(lv)//2]
        hi = sum(g for k, g in DL.items() if k >= mid)
        tot = sum(DL.values())
        hi_share.append(hi / tot if tot > 0 else 0)
    hi_share = np.array(hi_share)
    print(f"   gradient-energy share from upper-half degree levels: mean={hi_share.mean():.3f}")

    main.rows = rows; main.sep = (rho_l2.max(), sep_rhs.min())


if __name__ == "__main__":
    main()
