"""Refined: Lean hcond uses dirichletOn(P)=port-touching, dirichletOn(not P)=D_core (core-core).
Clean bipartition  D_core + D_port_touch = total Dirichlet = lam  (unit Fiedler).
Test simple upper bounds on D_core and the D_core 'budget' = (RHS - Cp*D_port)/Cc.
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
    EW = (f[:, None] - f[None, :]) ** 2 * Am
    cross = (inP[:, None] ^ inP[None, :]); core = (~inP[:, None]) & (~inP[None, :])
    pp = (inP[:, None]) & (inP[None, :])
    Dcross = float(EW[cross].sum()); Dcore = float(EW[core].sum()); Dpp = float(EW[pp].sum())
    Dport = Dcross + Dpp                       # "touching a port" = the Lean dirichletOn(P)
    Dtot = Dcross + Dcore + Dpp                # == lam
    Ecore = int((Am[core] > 0).sum()); Eport = int((Am[cross] > 0).sum() + (Am[pp] > 0).sum())
    delta = float(d[Pl].max()); Delta = float(d.max()); dmin = float(d.min())
    maxt = float((A2 * Am)[core].max()) if (core & (Am > 0)).any() else 0.0
    Cp = delta - 1.0; Cc = maxt
    budget = (RHS - Cp * Dport) / Cc           # max admissible D_core (touching convention)
    budget_x = (RHS - Cp * Dcross) / Cc        # same but with cross-only port term
    return dict(n=n, mE=mE, lam=lam, RHS=RHS, req=req, Dcore=Dcore, Dcross=Dcross, Dpp=Dpp,
                Dport=Dport, Dtot=Dtot, Ecore=Ecore, Eport=Eport, Cp=Cp, Cc=Cc,
                delta=delta, Delta=Delta, dmin=dmin, budget=budget, budget_x=budget_x)


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
print(f"=== {N} Case 2A graphs (touching-port convention: D_core + D_port = lam) ===\n")

bounds = {
    "(b)  lam - D_port":          lambda r: r["lam"] - r["Dport"],
    "(c)  (Ecore/E)*lam":         lambda r: (r["Ecore"] / r["mE"]) * r["lam"],
    "(d)  lam*(1-dmin/Delta)":    lambda r: r["lam"] * (1 - r["dmin"] / r["Delta"]),
    "(e)  D_port/Cc":             lambda r: r["Dport"] / r["Cc"],
    "(f)  D_port^2 / lam":        lambda r: r["Dport"] ** 2 / r["lam"],
    "(g)  (lam-D_port)=ident":    lambda r: r["lam"] - r["Dport"],   # identity == D_core
    "(h)  RHS/(2*Cc) - Cp*Dp/Cc": lambda r: (r["RHS"] - r["Cp"] * r["Dport"]) / r["Cc"] * 0.999,
}
print(f"{'bound on D_core':<28}{'valid?':<10}{'closes?':<10}{'maxratio':<11}{'min margin':<12}")
print("-" * 75)
for name, fn in bounds.items():
    valid = closes = True; mr = 0.0; mm = 1e9
    for nm, r in R:
        b = fn(r); mm = min(mm, b - r["Dcore"])
        if b - r["Dcore"] < -1e-7: valid = False
        ratio = (r["Cp"] * r["Dport"] + r["Cc"] * b) / r["RHS"]; mr = max(mr, ratio)
        if ratio > 1 + 1e-7: closes = False
    print(f"{name:<28}{('YES' if valid else 'NO'):<10}"
          f"{('YES' if valid and closes else '--' if not valid else 'NO'):<10}{mr:<11.4f}{mm:+.4f}")

print("\n=== literal hcond (touching) ratios + D_core budget ===")
print(f"{'graph':<14}{'D_core':<9}{'budget':<9}{'D_core/budget':<14}"
      f"{'lit.ratio':<11}{'Cc':<6}{'Cp':<5}{'D_port':<8}")
for nm, r in R:
    lit = (r["Cp"] * r["Dport"] + r["Cc"] * r["Dcore"]) / r["RHS"]
    print(f"{nm:<14}{r['Dcore']:<9.4f}{r['budget']:<9.4f}{r['Dcore']/r['budget']:<14.3f}"
          f"{lit:<11.4f}{r['Cc']:<6.0f}{r['Cp']:<5.0f}{r['Dport']:<8.4f}")
print(f"\nworst literal hcond ratio (touching): {max((r['Cp']*r['Dport']+r['Cc']*r['Dcore'])/r['RHS'] for _,r in R):.4f}")
print(f"worst D_core/budget                 : {max(r['Dcore']/r['budget'] for _,r in R):.4f}")
