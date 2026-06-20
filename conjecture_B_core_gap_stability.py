"""
Deterministic core-gap stability lemma for a degree-2 bottleneck.

G = H + v0,  v0 ~ {a,b} (a,b in core H).  f = Fiedler of G (Lf = lam2 f, f perp 1).
gamma = lam2(H) (core spectral gap), core degrees in [delta, Delta].

EXACT (eigenvector restricted to H):
   (L_H - lam2 I) f_H = -(f_a - f_v0) e_a - (f_b - f_v0) e_b   =: source
   => f_H = c*1 + f_H_perp,  c = -f_v0/(n-1),  (L_H-lam2) f_H_perp = P_perp source
   => ||f_H_perp|| <= ||source|| / (gamma - lam2).

TESTED BOUNDS:
  (1) |f_a|+|f_b| <= C/gamma * |f_v0|            (resolvent stability)
  (2) |C_attach| <= 2(Delta-1)*max|f_a,f_b|*(...) , ~ (Delta/gamma) f_v0^2
  (3) R'' >= |C_attach| + remainder  (=> gap = R''+C >= 0)   [C_dense=0 for regular cores]
Run: python conjecture_B_core_gap_stability.py
"""
import numpy as np
import networkx as nx


def attach_deg2(H):
    H = nx.convert_node_labels_to_integers(H)
    m = H.number_of_nodes()
    G = nx.Graph(H); G.add_node(m); G.add_edge(m, 0); G.add_edge(m, 1)
    return G, m  # v0 = m


def analyze(H):
    G, v0lbl = attach_deg2(H)
    nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}; n = len(nodes)
    A = nx.to_numpy_array(G, nodelist=nodes); d = A.sum(1); L = np.diag(d) - A
    ev, U = np.linalg.eigh(L); lam = ev[1]; f = U[:, 1]; f = f / np.linalg.norm(f)
    v0 = idx[v0lbl]
    if f[v0] < 0:
        f = -f
    m = G.number_of_edges(); S = float(d @ f); fDf = float(d @ (f * f))
    a, b = idx[0], idx[1]
    fa, fb, fv0 = float(f[a]), float(f[b]), float(f[v0])
    # core spectral gap and degree range
    Hc = nx.convert_node_labels_to_integers(H)
    evH = np.linalg.eigvalsh(nx.laplacian_matrix(Hc, nodelist=list(Hc.nodes()))
                             .toarray().astype(float))
    gamma = float(evH[1])
    dcore = np.array([d[idx[u]] - (1 if u in (0, 1) else 0) for u in range(v0lbl)])  # core degrees
    delta, Delta = float(dcore.min()), float(dcore.max())
    # C split
    Cattach = Cdense = 0.0
    for u, v in G.edges():
        ia, ib = idx[u], idx[v]
        if d[ia] > d[ib]:
            t = (d[ia] - d[ib]) * f[ia] * (f[ia] - f[ib])
        elif d[ib] > d[ia]:
            t = (d[ib] - d[ia]) * f[ib] * (f[ib] - f[ia])
        else:
            t = 0.0
        if ia == v0 or ib == v0:
            Cattach += t
        else:
            Cdense += t
    Rpp = lam * (fDf - lam + 1 - S ** 2 / m)
    gap = Rpp + Cattach + Cdense
    # resolvent residual ||source||
    src = np.sqrt((fa - fv0) ** 2 + (fb - fv0) ** 2)
    return dict(n=n, lam=lam, gamma=gamma, delta=delta, Delta=Delta, fa=fa, fb=fb, fv0=fv0,
                Rpp=Rpp, Cattach=Cattach, Cdense=Cdense, gap=gap, src=src,
                regular=bool(np.allclose(dcore, dcore[0])))


def cores():
    out = []
    for m in [100, 300]:
        out.append((f"K_{m}", nx.complete_graph(m)))
        for q in [0.3, 0.5, 0.65, 0.9]:
            out.append((f"gnp({m},{q})", nx.gnp_random_graph(m, q, seed=1)))
        r = max(3, int(0.3 * m))
        out.append((f"randreg({m},{r})", nx.random_regular_graph(r, m, seed=1)))
        out.append((f"circ({m},±1..{m//4})", nx.circulant_graph(m, list(range(1, m // 4)))))
        out.append((f"cycle_{m}", nx.cycle_graph(m)))               # poor expander control
    return out


def main():
    data = []
    for name, H in cores():
        if not nx.is_connected(H):
            continue
        data.append((name, analyze(H)))

    print("=" * 100)
    print("core-gap stability: bounds vs core spectral gap gamma")
    print("=" * 100)
    print(f"  {'core':18s} {'gamma':>8} {'Δ':>6} {'lam2':>7} {'|fa|+|fb|':>10} {'·γ/|fv0|':>9} "
          f"{'Cattach':>9} {'·γ/(Δfv0²)':>11} {'Rpp':>8} {'gap':>9} {'Rpp-|Catt|':>10}")
    for name, q in data:
        b1 = (abs(q['fa']) + abs(q['fb'])) * q['gamma'] / abs(q['fv0'])
        b2 = abs(q['Cattach']) * q['gamma'] / (q['Delta'] * q['fv0'] ** 2)
        rem = q['Rpp'] - abs(q['Cattach'])
        print(f"  {name:18s} {q['gamma']:8.3f} {q['Delta']:6.0f} {q['lam']:7.4f} "
              f"{abs(q['fa'])+abs(q['fb']):10.5f} {b1:9.3f} {q['Cattach']:9.4f} {b2:11.3f} "
              f"{q['Rpp']:8.4f} {q['gap']:9.5f} {rem:10.5f}")

    print("\n" + "=" * 100)
    print("BOUND CHECKS")
    print("=" * 100)
    # (1) resolvent: (|fa|+|fb|)*gamma/|fv0| bounded?
    b1s = [(abs(q['fa']) + abs(q['fb'])) * q['gamma'] / abs(q['fv0']) for _, q in data]
    print(f"  (1) (|fa|+|fb|)·γ/|fv0| : min={min(b1s):.3f} median={np.median(b1s):.3f} "
          f"max={max(b1s):.3f}  (bounded => |fa|+|fb| <= C/γ |fv0|)")
    # resolvent residual form: ||f_H_perp|| <= ||src||/(gamma-lam) -- check |fa-c| <= src/(gamma-lam)
    okres = 0
    for _, q in data:
        c = -q['fv0'] / (q['n'] - 1)
        bound = q['src'] / max(q['gamma'] - q['lam'], 1e-9)
        if abs(q['fa'] - c) <= bound + 1e-9 and abs(q['fb'] - c) <= bound + 1e-9:
            okres += 1
    print(f"      resolvent |f_a - c| <= ||src||/(γ-λ): {okres}/{len(data)} (rigorous bound)")
    # (2) C_attach bound
    b2s = [abs(q['Cattach']) * q['gamma'] / (q['Delta'] * q['fv0'] ** 2) for _, q in data]
    print(f"  (2) |Cattach|·γ/(Δ fv0²) : min={min(b2s):.3f} median={np.median(b2s):.3f} "
          f"max={max(b2s):.3f}")
    # (3) R'' >= |C_attach| ?  and gap>=0
    ok3 = sum(1 for _, q in data if q['Rpp'] >= abs(q['Cattach']) - 1e-9)
    okgap = sum(1 for _, q in data if q['gap'] >= -1e-9)
    print(f"  (3) R'' >= |Cattach| : {ok3}/{len(data)};  gap=R''+C >= 0 : {okgap}/{len(data)}")
    # regular cores: C_dense=0 ?
    reg = [(n, q) for n, q in data if q['regular']]
    cd = max(abs(q['Cdense']) for _, q in reg) if reg else 0
    print(f"  regular cores ({len(reg)}): max |C_dense| = {cd:.2e} (=0 => gap=R''+Cattach)")

    print("\n" + "=" * 100)
    print("SUFFICIENT CONDITION: when does R'' >= |Cattach| hold? (relate to γ vs Δ)")
    print("=" * 100)
    for name, q in data:
        cond = "OK" if q['Rpp'] >= abs(q['Cattach']) else "FAIL"
        print(f"  {name:18s} γ/Δ={q['gamma']/q['Delta']:.3f}  R''/|Catt|="
              f"{q['Rpp']/max(abs(q['Cattach']),1e-9):7.2f}  {cond}")


if __name__ == "__main__":
    main()
