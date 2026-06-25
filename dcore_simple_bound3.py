"""FINAL analysis under the VERIFIED Lean convention (matches verify_block_resolvent.py check d):

   hcond_lean :  2*[ (delta-1)*D_cross + maxt*D_core ] <= RHS      (worst actual ratio 0.935)

dirichletOn is an ORDERED double sum => factor 2 vs undirected energies.
Edge classes (by the degree-gap port split):  cross (1 port end), core (0 port ends),
port-port (2 port ends).  KEY: port-port edges here have triangle count t_e = 0
(verified below), so they contribute 0 to triEnergy and belong in the Cp=0 class.

Dirichlet identity (unit Fiedler):  D_cross + D_core + D_pp = sum_E (f_a-f_b)^2 = f^T L f = lam.
=> D_core = lam - D_cross - D_pp   (EXACT, no matrix inverse).
The D_core 'budget' for closure:  D_core <= (RHS/2 - (delta-1)*D_cross)/maxt.
"""
import numpy as np, networkx as nx


def split_ports(d):
    n = len(d); order = np.argsort(d); sd = d[order]
    gaps = [(sd[i + 1] - sd[i], i) for i in range(n - 1)]; gap, idx = max(gaps)
    return set(order[:idx + 1].tolist()) if (gap >= 2 and idx < n - 1) else set()


def analyze(G):
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
    EW = (f[:, None] - f[None, :]) ** 2 * Am
    Tri = A2 * Am                                   # triangle count per upper edge
    cross = (inP[:, None] ^ inP[None, :]); core = (~inP[:, None]) & (~inP[None, :])
    pp = (inP[:, None]) & (inP[None, :])
    Dcross = float(EW[cross].sum()); Dcore = float(EW[core].sum()); Dpp = float(EW[pp].sum())
    tpp_max = float(Tri[pp].max()) if (pp & (Am > 0)).any() else 0.0
    delta = float(d[Pl].max()); Delta = float(d.max()); dmin = float(d.min())
    maxt = float(Tri[core].max()) if (core & (Am > 0)).any() else 0.0
    Cp = delta - 1.0; Cc = maxt
    lit = 2 * (Cp * Dcross + Cc * Dcore) / RHS
    budget = (RHS / 2 - Cp * Dcross) / Cc
    return dict(lam=lam, RHS=RHS, req=req, Dcross=Dcross, Dcore=Dcore, Dpp=Dpp,
                Cp=Cp, Cc=Cc, lit=lit, budget=budget, tpp_max=tpp_max, mE=mE,
                Delta=Delta, dmin=dmin, Dtot=Dcross + Dcore + Dpp)


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
R = [(nm, analyze(G)) for nm, G in gs]; R = [(nm, r) for nm, r in R if r]
N = len(R)
print(f"=== {N} Case 2A graphs | verified convention 2[(d-1)Dcross+maxt*Dcore]<=RHS ===")
print(f"worst literal hcond ratio = {max(r['lit'] for _,r in R):.4f}   "
      f"max port-port triangle count = {max(r['tpp_max'] for _,r in R):.0f} (=> Cp=0 class)\n")

# One-sided upper bounds on D_core, tested as: valid (>=Dcore) AND closes (LHS<=RHS).
bounds = {
    "lam (total Dirichlet)":          lambda r: r["lam"],
    "lam - Dcross - Dpp  [IDENTITY]": lambda r: r["lam"] - r["Dcross"] - r["Dpp"],
    "lam - Dcross        (drop Dpp)": lambda r: r["lam"] - r["Dcross"],
    "Dcross / maxt":                  lambda r: r["Dcross"] / r["Cc"],
    "req / (2*lam*maxt)":             lambda r: r["req"] / (2 * r["lam"] * r["Cc"]),
    "Dcross^2 / lam":                 lambda r: r["Dcross"] ** 2 / r["lam"],
    "(RHS/2 - Cp*Dcross)/maxt budget":lambda r: r["budget"],
}
print(f"{'D_core bound B':<34}{'valid':<8}{'closes':<8}{'maxLHS/RHS':<12}{'min(B-Dcore)':<13}{'max B/budget'}")
print("-" * 92)
for name, fn in bounds.items():
    valid = closes = True; mlr = 0.0; mm = 1e9; mbb = 0.0
    for nm, r in R:
        B = fn(r); mm = min(mm, B - r["Dcore"]); mbb = max(mbb, B / r["budget"])
        if B - r["Dcore"] < -1e-7: valid = False
        ratio = 2 * (r["Cp"] * r["Dcross"] + r["Cc"] * B) / r["RHS"]; mlr = max(mlr, ratio)
        if ratio > 1 + 1e-7: closes = False
    print(f"{name:<34}{('YES' if valid else 'no'):<8}"
          f"{('YES' if valid and closes else '--' if not valid else 'no'):<8}"
          f"{mlr:<12.4f}{mm:<+13.4f}{mbb:.3f}")

print(f"\n{'graph':<14}{'Dcore':<9}{'budget':<9}{'Dc/bud':<9}{'Dcross':<9}{'Dpp':<8}"
      f"{'lam':<8}{'Cc':<5}{'Cp':<4}{'lit':<8}")
for nm, r in R:
    print(f"{nm:<14}{r['Dcore']:<9.4f}{r['budget']:<9.4f}{r['Dcore']/r['budget']:<9.3f}"
          f"{r['Dcross']:<9.4f}{r['Dpp']:<8.4f}{r['lam']:<8.4f}{r['Cc']:<5.0f}{r['Cp']:<4.0f}{r['lit']:<8.4f}")

# --- Extra: can required>0 give a self-contained D_core bound (no free D_port)? ---
print("\n=== required-based / self-contained candidates ===")
extra = {
    "req/(2*lam)            ": lambda r: r["req"] / (2 * r["lam"]),
    "req/(2*lam*maxt)       ": lambda r: r["req"] / (2 * r["lam"] * r["Cc"]),
    "req/(2*lam) - 0        ": lambda r: r["req"] / (2 * r["lam"]),
    "(RHS/2)/maxt - (d-1)Dx/maxt(=bud)": lambda r: r["budget"],
}
for name, fn in extra.items():
    rows = []
    for nm, r in R:
        B = fn(r); rows.append((B - r["Dcore"], 2 * (r["Cp"] * r["Dcross"] + r["Cc"] * B) / r["RHS"]))
    valid = all(m >= -1e-7 for m, _ in rows); closes = all(rt <= 1 + 1e-7 for _, rt in rows)
    print(f"{name:<36} valid={'Y' if valid else 'n'} closes={'Y' if valid and closes else 'n'} "
          f"maxratio={max(rt for _,rt in rows):.4f} min(B-Dcore)={min(m for m,_ in rows):+.4f}")

print("\nD_core vs req/(2*lam) per graph:")
for nm, r in R:
    print(f"  {nm:<14} Dcore={r['Dcore']:.4f}  req/(2lam)={r['req']/(2*r['lam']):.4f}  "
          f"ratio={r['Dcore']/(r['req']/(2*r['lam'])):.3f}")
