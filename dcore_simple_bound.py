"""Find a Lean-formalizable upper bound on D_core that closes hcond without matrix inverses.

hcond (the scalar flatness inequality that closes typeA_slack_ge_required):
    (delta-1)*D_port + maxt_core*D_core <= RHS
where RHS = 2*lam*(2*degQuad - lam - S^2/mE),  lam = lambda_2,  f the unit Fiedler.

Total Dirichlet energy identity:  sum_{all edges} (f_a-f_b)^2 = f^T L f = lam*||f||^2 = lam.
Edges partition into: core-core (D_core), cross port<->core (D_cross), port-port (D_pp).
The verified script `verify_block_resolvent.py` calls the cross term `D_port`.
So:  D_core + D_cross + D_pp = lam,  all terms >= 0.
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
    Am = np.triu(A, 1)
    inP = np.zeros(n, bool); inP[Pl] = True
    EW = (f[:, None] - f[None, :]) ** 2 * Am                  # per upper-edge g^2
    crossmask = (inP[:, None] ^ inP[None, :])
    coremask = (~inP[:, None]) & (~inP[None, :])
    ppmask = (inP[:, None]) & (inP[None, :])
    Dcross = float(EW[crossmask].sum())                       # == "D_port" in verify script
    Dcore = float(EW[coremask].sum())
    Dpp = float(EW[ppmask].sum())
    Dtot = float(EW.sum())                                    # = lam (check)
    Ecore = int((Am[coremask] > 0).sum()) if coremask.any() else 0
    Ecross = int((Am[crossmask] > 0).sum())
    delta = float(d[Pl].max())                                # max port degree -> Cp = delta-1
    maxt = float((A2 * Am)[coremask].max()) if (coremask & (Am > 0)).any() else 0.0
    Delta = float(d.max()); dmin = float(d.min())
    Cp = delta - 1.0; Cc = maxt
    # core-edge flatness
    core_e = EW[coremask & (Am > 0)]
    flat = (float(core_e.max() / core_e.mean()) if core_e.size else 0.0)
    return dict(n=n, mE=mE, lam=lam, RHS=RHS, req=req, Dcore=Dcore, Dcross=Dcross,
                Dpp=Dpp, Dtot=Dtot, Ecore=Ecore, Ecross=Ecross, Cp=Cp, Cc=Cc,
                delta=delta, Delta=Delta, dmin=dmin, flat=flat,
                Dport=Dcross)  # alias: hcond's "D_port" is the cross term


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
print(f"=== {N} Case 2A graphs ===\n")

# Candidate upper bounds on D_core (name -> function of record)
bounds = {
    "(a) lam":                 lambda r: r["lam"],
    "(b) lam - Dport":         lambda r: r["lam"] - r["Dport"],
    "(b') lam - Dport - Dpp":  lambda r: r["lam"] - r["Dport"] - r["Dpp"],
    "(c) (Ecore/E)*lam":       lambda r: (r["Ecore"] / r["mE"]) * r["lam"],
    "(d) lam*(1-dmin/Delta)":  lambda r: r["lam"] * (1 - r["dmin"] / r["Delta"]),
}

print(f"{'bound':<26}{'valid?':<14}{'closes hcond?':<18}{'max ratio':<12}{'min valid margin'}")
print("-" * 86)
results = {}
for name, fn in bounds.items():
    valid = True; min_margin = 1e9; closes = True; max_ratio = 0.0
    for nm, r in R:
        b = fn(r)
        margin = b - r["Dcore"]                          # >=0  <=> valid upper bound
        if margin < -1e-7: valid = False
        min_margin = min(min_margin, margin)
        lhs = r["Cp"] * r["Dport"] + r["Cc"] * b         # hcond LHS with this bound
        ratio = lhs / r["RHS"]
        max_ratio = max(max_ratio, ratio)
        if ratio > 1 + 1e-7: closes = False
    results[name] = dict(valid=valid, closes=closes, max_ratio=max_ratio, min_margin=min_margin)
    print(f"{name:<26}{('YES' if valid else 'NO'):<14}"
          f"{('YES' if (valid and closes) else ('--' if not valid else 'NO')):<18}"
          f"{max_ratio:<12.4f}{min_margin:+.4f}")

print("\n=== reference: real hcond with actual D_core ===")
mr = max(r["Cp"] * r["Dport"] + r["Cc"] * r["Dcore"] for _, r in R) and \
     max((r["Cp"] * r["Dport"] + r["Cc"] * r["Dcore"]) / r["RHS"] for _, r in R)
print(f"max ratio (Cp*Dport + Cc*Dcore)/RHS = {mr:.4f}  (<=1 means literal hcond holds)")

print("\n=== Dirichlet identity / partition check (per graph) ===")
print(f"{'graph':<14}{'lam':<9}{'Dtot':<9}{'Dcore':<9}{'Dport':<9}{'Dpp':<8}"
      f"{'Cp':<6}{'Cc':<6}{'Ecore':<7}{'flat':<7}")
for nm, r in R:
    print(f"{nm:<14}{r['lam']:<9.4f}{r['Dtot']:<9.4f}{r['Dcore']:<9.4f}{r['Dport']:<9.4f}"
          f"{r['Dpp']:<8.4f}{r['Cp']:<6.0f}{r['Cc']:<6.0f}{r['Ecore']:<7}{r['flat']:<7.2f}")

print("\n=== TASK 2: core Fiedler flatness (max/mean core-edge g^2) ===")
fl = [r["flat"] for _, r in R]
print(f"flatness ratio range {min(fl):.2f}-{max(fl):.2f}, mean {np.mean(fl):.2f}")
