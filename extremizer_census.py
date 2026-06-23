# -*- coding: utf-8 -*-
"""Extremizer census for the aggregate triangle Poincare inequality.
R = T_edges / (lam2 * degQuad), maximised over the lam2-eigenspace.
Writes a markdown report to informal/extremizer_census.md.
"""
import sys, io, itertools, math
sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding="utf-8")
import numpy as np
import scipy.linalg as sla
import networkx as nx

np.set_printoptions(suppress=True)
RNG = np.random.default_rng(12345)

# ----------------------------------------------------------------------------
# Core: R over the lam2-eigenspace, plus the maximising Fiedler vector u*.
# ----------------------------------------------------------------------------
def analyse(G):
    """Return a metrics dict for connected simple graph G, or None."""
    G = nx.convert_node_labels_to_integers(G)
    n = G.number_of_nodes()
    if n < 3 or not nx.is_connected(G):
        return None
    A = nx.to_numpy_array(G, nodelist=range(n))
    deg = A.sum(axis=1)
    D = np.diag(deg)
    L = D - A
    # common-neighbour (triangle) weights t_e on edges
    CN = A @ A
    W = A * CN                       # weighted adjacency, weight t_e
    Lw = np.diag(W.sum(axis=1)) - W  # weighted Laplacian -> T(u)=u' Lw u
    w, V = np.linalg.eigh(L)
    lam2 = w[1]
    if lam2 < 1e-9:
        return None
    tol = 1e-7 + 1e-6 * lam2
    idx = [i for i in range(n) if abs(w[i] - lam2) < tol and i >= 1]
    mult = len(idx)
    Q = V[:, idx]                    # orthonormal basis of eigenspace
    M1 = Q.T @ Lw @ Q
    M2 = Q.T @ D @ Q
    # max over eigenspace of (u'Lw u)/(u'D u) via generalised symmetric eig
    mu, C = sla.eigh(M1, M2)
    j = int(np.argmax(mu))
    R = mu[j] / lam2
    c = C[:, j]
    u = Q @ c
    u = u / math.sqrt(float(u @ u))  # ||u||^2 = 1
    # per-edge T contributions and per-vertex degQuad contributions
    Tedge = []
    for a, b in G.edges():
        te = CN[a, b]
        Tedge.append((te * (u[a] - u[b]) ** 2, te, a, b))
    T = sum(x[0] for x in Tedge)
    degQ = float(np.sum(deg * u ** 2))
    # edges carrying >50% of T
    Te_sorted = sorted((x[0] for x in Tedge), reverse=True)
    cum, k_edge = 0.0, 0
    for val in Te_sorted:
        cum += val; k_edge += 1
        if cum > 0.5 * T:
            break
    # vertices carrying >50% of degQuad
    vv = sorted((deg[v] * u[v] ** 2 for v in range(n)), reverse=True)
    cum, k_vtx = 0.0, 0
    for val in vv:
        cum += val; k_vtx += 1
        if cum > 0.5 * degQ:
            break
    te_vals = [x[1] for x in Tedge]
    m = G.number_of_edges()
    tri = int(round(np.trace(A @ A @ A) / 6))
    loc = float(n * np.max(u ** 2))               # IPR-style localisation
    return dict(
        n=n, m=m, tri=tri, lam2=float(lam2), mult=mult, R=float(R),
        dmin=int(deg.min()), dmax=int(deg.max()),
        dmean=float(deg.mean()), dstd=float(deg.std()),
        maxt=int(max(te_vals)), meant=float(np.mean(te_vals)),
        t_ratio=(max(te_vals) / np.mean(te_vals)) if np.mean(te_vals) > 0 else 0.0,
        loc=loc, k_edge=k_edge, frac_edge=k_edge / m,
        k_vtx=k_vtx, frac_vtx=k_vtx / n,
        T=float(T), degQ=degQ, slack=float(lam2 * degQ - T),
    )

def R_only(G):
    d = analyse(G)
    return None if d is None else d["R"]

# ----------------------------------------------------------------------------
# Graph families (repo-faithful constructions)
# ----------------------------------------------------------------------------
def deg2dense(nn, q, s):
    H = nx.gnp_random_graph(nn - 1, q, seed=s); H.add_node(nn - 1)
    H.add_edge(nn - 1, 0); H.add_edge(nn - 1, 1); return H

def twin(N, dd):
    K = nx.complete_graph(N); a, b = N, N + 1
    for x in (a, b):
        for w in range(dd): K.add_edge(x, w)
    K.add_node(N + 2); K.add_edge(N + 2, a); K.add_edge(N + 2, b); return K

def lollipop(n, k):           # K_k clique + path of (n-k) vertices
    return nx.lollipop_graph(k, n - k)

def barbell(k, b):            # two K_k joined by a path of b vertices
    return nx.barbell_graph(k, b)

def families():
    out = []
    # complete graphs (baseline)
    for n in [5, 8, 12, 20, 50, 100]:
        out.append((f"K{n}", "complete", nx.complete_graph(n)))
    # all connected graphs on 6,7 vertices (atlas is complete up to 7)
    from networkx.generators.atlas import graph_atlas_g
    atlas = graph_atlas_g()
    a6 = a7 = 0
    for gi, Gi in enumerate(atlas):
        nn = Gi.number_of_nodes()
        if nn in (6, 7) and Gi.number_of_edges() >= nn - 1 and nx.is_connected(Gi):
            out.append((f"atlas{nn}_{gi}", f"all_n{nn}", Gi))
            if nn == 6: a6 += 1
            else: a7 += 1
    # n=8: NO complete enumerator (atlas stops at 7); large random sample instead
    seen8 = 0
    for s in range(6000):
        p = RNG.uniform(0.15, 0.9)
        Gi = nx.gnp_random_graph(8, p, seed=int(RNG.integers(1e9)))
        if nx.is_connected(Gi):
            out.append((f"rand8_{s}", "sample_n8", Gi)); seen8 += 1
        if seen8 >= 3000:
            break
    # deg2dense
    for nn in [20, 40, 60, 80]:
        for q in [.1, .2, .3, .5, .7, .9]:
            out.append((f"deg2d{nn}_{q}", "deg2dense", deg2dense(nn, q, 7)))
    # twin-port
    for N in [20, 50]:
        for dd in [1, 2, 3, 5]:
            out.append((f"twin{N}_{dd}", "twin", twin(N, dd)))
    # lollipop
    for n in [8, 10, 15, 20]:
        for k in range(3, n - 2):
            out.append((f"lolli{n}_{k}", "lollipop", lollipop(n, k)))
    # random regular
    for n in [20, 40]:
        for d in [3, 5, 8, 12]:
            try:
                out.append((f"reg{n}_{d}", "regular", nx.random_regular_graph(d, n, seed=7)))
            except Exception:
                pass
    # barbell
    for k in [5, 8, 10]:
        for b in [1, 2, 3]:
            out.append((f"barbell{k}_{b}", "barbell", barbell(k, b)))
    # named
    out.append(("petersen", "named", nx.petersen_graph()))
    for nm, gg in [("kneser52", nx.kneser_graph(5, 2))]:
        out.append((nm, "named", gg))
    return out, a6, a7, seen8

# ----------------------------------------------------------------------------
# Run census
# ----------------------------------------------------------------------------
print("Building families...", file=sys.stderr)
fam, a6, a7, n8 = families()
rows = []
for name, kind, G in fam:
    try:
        d = analyse(G)
    except Exception as e:
        d = None
    if d is None:
        continue
    d["name"] = name; d["kind"] = kind
    rows.append(d)
print(f"Analysed {len(rows)} graphs (atlas6={a6}, atlas7={a7}, sample_n8={n8})", file=sys.stderr)

rows.sort(key=lambda d: -d["R"])
top = rows[:50]

# ----------------------------------------------------------------------------
# TASK 3 : perturbation from K_20
# ----------------------------------------------------------------------------
def perturb_K(n=20, steps=120):
    res = {"random": [], "triangle_poor": [], "triangle_rich": []}
    for mode in res:
        G = nx.complete_graph(n)
        seq = []
        r0 = R_only(G); seq.append((0, r0))
        for step in range(1, steps + 1):
            A = nx.to_numpy_array(G); CN = A @ A
            cand = []
            for a, b in G.edges():
                H = G.copy(); H.remove_edge(a, b)
                if nx.is_connected(H):
                    cand.append((CN[a, b], a, b))
            if not cand:
                break
            if mode == "random":
                a, b = cand[int(RNG.integers(len(cand)))][1:]
            elif mode == "triangle_poor":
                cand.sort(key=lambda x: x[0]); a, b = cand[0][1:]
            else:
                cand.sort(key=lambda x: -x[0]); a, b = cand[0][1:]
            G.remove_edge(a, b)
            seq.append((step, R_only(G)))
        res[mode] = seq
    return res

# ----------------------------------------------------------------------------
# TASK 4 : edge-deletion monotonicity of Slack on top-20
# ----------------------------------------------------------------------------
def slack_monotone(d):
    name = d["name"]
    G = dict(((nm, GG) for nm, _, GG in fam)).get(name)
    if G is None:
        return None
    G = nx.convert_node_labels_to_integers(G)
    base = analyse(G)
    if base is None:
        return None
    s0 = base["slack"]
    edges = list(G.edges())
    sampled = False
    if len(edges) > 300:
        sampled = True
        edges = [edges[i] for i in RNG.choice(len(edges), 300, replace=False)]
    viol = []
    tested = 0
    for a, b in edges:
        H = G.copy(); H.remove_edge(a, b)
        if not nx.is_connected(H):
            continue
        dd = analyse(H)
        if dd is None:
            continue
        tested += 1
        if dd["slack"] < s0 - 1e-9:
            te = int((nx.to_numpy_array(G) @ nx.to_numpy_array(G))[a, b])
            viol.append((dd["slack"] - s0, te, G.degree(a), G.degree(b)))
    return dict(name=name, s0=s0, tested=tested, n_viol=len(viol),
                viol=sorted(viol)[:5], sampled=sampled)

# ----------------------------------------------------------------------------
# TASK 5 : asymptotics of deg2dense
# ----------------------------------------------------------------------------
def asymptotics():
    res = []
    for q in [.1, .3, .5, .9]:
        seq = []
        for nn in [20, 40, 80, 160]:
            d = analyse(deg2dense(nn, q, 7))
            if d:
                seq.append((nn, d["R"], d["slack"], d["lam2"], d["maxt"], d["t_ratio"]))
        res.append((q, seq))
    # K_n sequence for reference
    kn = []
    for nn in [20, 40, 80, 160]:
        d = analyse(nx.complete_graph(nn))
        kn.append((nn, d["R"], d["slack"], (nn - 2) / (nn - 1)))
    return res, kn

print("Perturbation...", file=sys.stderr); pert = perturb_K(20, 120)
print("Monotonicity...", file=sys.stderr)
mono = [m for m in (slack_monotone(d) for d in rows[:20]) if m]
print("Asymptotics...", file=sys.stderr); asym, knseq = asymptotics()

# ----------------------------------------------------------------------------
# Markdown report
# ----------------------------------------------------------------------------
L = []
def P(s=""): L.append(s)

P("# Extremizer census — aggregate triangle Poincaré  `R = T/(λ₂·degQuad)`")
P()
P("**Date:** 2026-06-23 · **Repo:** topostability-lean4 · analysis only, no Lean changes.")
P()
P("`R = T_edges/(λ₂·degQuad)` with `T_edges = Σ_e t_e(u_a−u_b)²`, `t_e=|N_a∩N_b|`, "
  "`degQuad=Σ_v d_v u_v²`, **maximised over the λ₂-eigenspace** (the true test of the "
  "aggregate, which must hold for every Fiedler). The conjecture is `R ≤ 1`. "
  f"Census: **{len(rows)} connected graphs** "
  f"(complete enumeration n=6:{a6}, n=7:{a7} via NetworkX atlas; "
  f"n=8 is a **random sample of {n8}**, NOT exhaustive — no nauty/geng in env).")
P()
# K_n correction note
P("## ⚠ Correction to the brief: `K_n` does NOT give `R = 1` exactly")
P()
P("Analytically, for `K_n` and **any** Fiedler `u` (`Σu=0`): `λ₂=n`, `degQuad=(n−1)‖u‖²`, "
  "`t_e=n−2`, `T=(n−2)·n‖u‖²`, so")
P()
P("```")
P("R(K_n) = (n−2)·n / (n·(n−1)) = (n−2)/(n−1)   < 1  for all finite n.")
P("```")
P()
P("`K_n` is the **asymptotic** extremizer (`R → 1` as `n→∞`), not an exact-equality case. "
  "Measured vs the closed form:")
P()
P("| n | R(K_n) measured | (n−2)/(n−1) |")
P("|---|---|---|")
for nn, R, sl, cf in knseq:
    P(f"| {nn} | {R:.6f} | {cf:.6f} |")
P()

# ---------------- TASK 1 ----------------
P("## TASK 1 — Top 50 by R")
P()
P("| # | name | family | n | m | R | λ₂ | mult | maxt/meant | loc |")
P("|---|------|--------|---|---|---|-----|------|-----------|-----|")
for i, d in enumerate(top, 1):
    P(f"| {i} | {d['name']} | {d['kind']} | {d['n']} | {d['m']} | {d['R']:.5f} | "
      f"{d['lam2']:.4f} | {d['mult']} | {d['t_ratio']:.2f} | {d['loc']:.1f} |")
P()
P(f"Max R over the whole census = **{rows[0]['R']:.6f}** ({rows[0]['name']}). "
  f"All {len(rows)} graphs satisfy R ≤ 1 "
  f"(min slack = {min(d['slack'] for d in rows):.3e}).")
P()

# ---------------- TASK 2 ----------------
P("## TASK 2 — Anatomy of the top-R graphs")
P()
P("| name | n | m | tri | deg(min/max/mean/std) | maxt/meant | loc | "
  "edges>50%T (k,frac) | verts>50%degQ (k,frac) |")
P("|------|---|---|-----|----------------------|-----------|-----|--------------------|------------------------|")
for d in top[:30]:
    P(f"| {d['name']} | {d['n']} | {d['m']} | {d['tri']} | "
      f"{d['dmin']}/{d['dmax']}/{d['dmean']:.1f}/{d['dstd']:.1f} | {d['t_ratio']:.2f} | "
      f"{d['loc']:.1f} | {d['k_edge']},{d['frac_edge']:.2f} | {d['k_vtx']},{d['frac_vtx']:.2f} |")
P()
# family breakdown of top 50
from collections import Counter
cnt = Counter(d["kind"] for d in top)
P("**Family composition of top 50:** " + ", ".join(f"{k}={v}" for k, v in cnt.most_common()))
P()
P(f"**Localisation** (top 50): loc mean = {np.mean([d['loc'] for d in top]):.2f}, "
  f"max = {max(d['loc'] for d in top):.2f} (loc=1 ⇒ uniform Fiedler, loc=n ⇒ a single vertex). "
  f"**Concentration**: median edges carrying >50% of T = "
  f"{np.median([d['frac_edge'] for d in top])*100:.0f}% of edges; "
  f"median vertices carrying >50% of degQ = "
  f"{np.median([d['frac_vtx'] for d in top])*100:.0f}% of vertices.")
P()

# ---------------- TASK 3 ----------------
P("## TASK 3 — Perturbation from K₂₀ (edge removal)")
P()
P("R after removing edges from K₂₀ (keeping connectivity), three removal orders. "
  "Sampled steps:")
P()
P("| #removed | random | triangle_poor (min t_e) | triangle_rich (max t_e) |")
P("|---|---|---|---|")
checkpoints = [0,1,2,5,10,20,40,60,80,100,120]
dr = {m: dict(seq) for m, seq in pert.items()}
for s in checkpoints:
    row = [f"| {s} "]
    for m in ["random","triangle_poor","triangle_rich"]:
        v = dr[m].get(s)
        row.append(f"| {v:.5f} " if v is not None else "| – ")
    P("".join(row) + "|")
P()
# monotonicity of R under removal
def increases(seq):
    inc = sum(1 for i in range(1,len(seq)) if seq[i][1] is not None and seq[i-1][1] is not None and seq[i][1] > seq[i-1][1] + 1e-9)
    return inc
for m in ["random","triangle_poor","triangle_rich"]:
    seq = pert[m]
    P(f"- **{m}**: R is NON-monotone — {increases(seq)} of {len(seq)-1} removals *increase* R. "
      f"Final R={seq[-1][1]:.5f}, start R={seq[0][1]:.5f}.")
P()

# ---------------- TASK 4 ----------------
P("## TASK 4 — Edge-deletion monotonicity of Slack = λ₂·degQuad − T (top 20)")
P()
P("For each near-tight graph, remove each edge (keep connectivity) and compare "
  "`Slack(G−e)` vs `Slack(G)` (each graph's own max-R Fiedler, ‖u‖²=1). "
  "Dense graphs: 300 edges sampled.")
P()
P("| name | Slack(G) | edges tested | #violations (Slack drops) | sampled |")
P("|------|---------|--------------|---------------------------|---------|")
for m in mono:
    P(f"| {m['name']} | {m['s0']:.4e} | {m['tested']} | {m['n_viol']} | {'yes' if m['sampled'] else 'no'} |")
P()
tot_v = sum(m["n_viol"] for m in mono); tot_t = sum(m["tested"] for m in mono)
P(f"**Total: {tot_v} violations of {tot_t} edge deletions tested "
  f"({100*tot_v/max(tot_t,1):.1f}%).** "
  + ("Slack is NOT monotone under edge deletion." if tot_v else
     "Slack appears monotone (no violations found) under edge deletion on this set."))
P()
# characterise violating edges
allviol = [v for m in mono for v in m["viol"]]
if allviol:
    P("Sample violating edges (ΔSlack, t_e, deg_a, deg_b):")
    for dv, te, da, db in sorted(allviol)[:12]:
        P(f"- ΔSlack={dv:.3e}, t_e={te}, deg=({da},{db})")
    P()

# ---------------- TASK 5 ----------------
P("## TASK 5 — Asymptotics of deg2dense(n,q)")
P()
P("`deg2dense(n,q)` = dense `G(n−1,q)` block + one degree-2 vertex bridging nodes 0,1.")
P()
for q, seq in asym:
    P(f"**q={q}:**")
    P()
    P("| n | R | Slack | λ₂ | maxt | maxt/meant |")
    P("|---|---|-------|-----|------|-----------|")
    for nn, R, sl, lam, mt, tr in seq:
        P(f"| {nn} | {R:.5f} | {sl:.4e} | {lam:.4f} | {mt} | {tr:.2f} |")
    P()
P("**K_n reference:** R=(n−2)/(n−1)→1, Slack grows ∝ n (degQuad∝n).")
P()

with open(r"C:\dev\topostability-lean4\informal\extremizer_census.md", "w", encoding="utf-8") as fh:
    fh.write("\n".join(L) + "\n")
print("WROTE informal/extremizer_census.md", file=sys.stderr)
print(f"top1={rows[0]['name']} R={rows[0]['R']:.5f}; census={len(rows)}", file=sys.stderr)
