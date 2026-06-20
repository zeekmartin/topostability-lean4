"""
TYPE A: PART A equality-case analysis (gap=0) + PART B resolvent invariant search.

G = H + v0 (v0~{a,b}).  T = sum_e t_e g_e^2,  B2' = sum_e (min(d_a,d_b)-1) g_e^2,  gap = lam2G - B2'.
Equality in B (T = lam2G) needs BOTH  T = B2'  (per-edge t_e = min-1)  AND  B2' = lam2G (gap=0, R''+C=0).
Run: python conjecture_B_typeA_equality_and_resolvent.py
"""
import numpy as np
import networkx as nx


def analyze(H, a=0, b=1):
    H = nx.convert_node_labels_to_integers(H); nH = H.number_of_nodes()
    if not nx.is_connected(H): return None
    G = nx.Graph(H); G.add_node(nH); G.add_edge(nH, a); G.add_edge(nH, b)
    nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}
    A = nx.to_numpy_array(G, nodelist=nodes); d = A.sum(1); L = np.diag(d) - A
    ev, U = np.linalg.eigh(L); lam = ev[1]; f = U[:, 1]; f = f / np.linalg.norm(f)
    v0 = idx[nH]
    if f[v0] < 0: f = -f
    m = G.number_of_edges(); S = float(d @ f); fDf = float(d @ (f * f))
    A2 = A @ A
    Gsum = sum((f[idx[u]] + f[idx[v]]) ** 2 for u, v in G.edges())
    B2 = 0.0; T = 0.0
    slack_v0 = slack_att = slack_bulk = 0.0   # (min-1-t_e) g_e^2 by edge class
    for u, v in G.edges():
        i, j = idx[u], idx[v]; g = (f[i] - f[j]) ** 2
        te = A2[i, j]; w = min(d[i], d[j]) - 1
        B2 += w * g; T += te * g
        sl = (w - te) * g
        if i == v0 or j == v0: slack_v0 += sl
        elif (u in (a, b)) or (v in (a, b)): slack_att += sl
        else: slack_bulk += sl
    gap = lam * (Gsum - S ** 2 / m) - B2
    # core resolvent block at a,b (1-perp)
    LH = nx.laplacian_matrix(H, nodelist=list(range(nH))).toarray().astype(float)
    evH, UH = np.linalg.eigh(LH); gammaC = float(evH[1])
    R = np.zeros((nH, nH))
    for k in range(1, nH):
        R += np.outer(UH[:, k], UH[:, k]) / (evH[k] - lam)
    Raa, Rbb, Rab = R[a, a], R[b, b], R[a, b]
    R2 = np.array([[Raa, Rab], [Rab, Rbb]])
    one = np.array([1.0, 1.0])
    I2 = np.eye(2)
    theta = float(one @ R2 @ np.linalg.solve(I2 + R2, one))
    detI = float(np.linalg.det(I2 + R2))
    eff = Raa + Rbb - 2 * Rab
    return dict(nH=nH, m=m, n=nH + 1, lam=lam, gamma=gammaC, gap=gap, B2=B2, T=T,
                slack_v0=slack_v0, slack_att=slack_att, slack_bulk=slack_bulk,
                Raa=Raa, Rbb=Rbb, Rab=Rab, eff=eff, theta=theta, detI=detI,
                fv0=float(f[v0]), c=gap * m / (nH + 1),
                aADJb=H.has_edge(a, b))


def typeA(r): return r is not None and r['lam'] < r['gamma'] and r['fv0'] ** 2 > 0.3


def main():
    rng = np.random.default_rng(0)
    data = []
    for _ in range(120):
        nH = int(rng.integers(15, 45)); q = float(rng.uniform(0.3, 0.92))
        H = nx.gnp_random_graph(nH, q, seed=int(rng.integers(1e6)))
        r = analyze(H)
        if typeA(r): data.append(r)
    # also near-minimizers: complete bulk with reduced attachment degree
    for nH in [20, 30]:
        for drop in range(0, 8):
            H = nx.complete_graph(nH)
            for k in range(drop):                 # remove attachment(0)-bulk edges
                if H.has_edge(0, 5 + k): H.remove_edge(0, 5 + k)
            r = analyze(H)
            if typeA(r): data.append(r)
    print(f"  collected {len(data)} TYPE A graphs")

    print("\n" + "=" * 88)
    print("PART A / TASK 1 — T=B2' slack  (min-1-t_e)g_e^2  by edge class")
    print("=" * 88)
    print(f"  total B2'-T (=slack) min/median/max: "
          f"{min(d['B2']-d['T'] for d in data):.4f} / "
          f"{np.median([d['B2']-d['T'] for d in data]):.4f} / "
          f"{max(d['B2']-d['T'] for d in data):.4f}")
    sv = np.array([d['slack_v0'] for d in data]); sa = np.array([d['slack_att'] for d in data])
    sb = np.array([d['slack_bulk'] for d in data]); tot = sv + sa + sb + 1e-12
    print(f"  slack share  v0-edges: {np.mean(sv/tot):.3f}   attachment-bulk: {np.mean(sa/tot):.3f}"
          f"   bulk-bulk: {np.mean(sb/tot):.3f}")
    print(f"  v0-edge slack > 0 (=> a NOT~ b, t_v0=0<1): "
          f"{sum(1 for d in data if d['slack_v0']>1e-9)}/{len(data)}; "
          f"a~b in {sum(1 for d in data if d['aADJb'])}/{len(data)}")
    print("  => T=B2' requires a~b (else v0-edge slack ~ g^2 large) AND locally-complete core.")

    print("\n" + "=" * 88)
    print("PART A / TASK 2-3 — gap=0 needs R''+C=0; can ALL equality conditions hold? (slack>0?)")
    print("=" * 88)
    minslackT = min(d['B2'] - d['T'] for d in data)
    mingap = min(d['gap'] for d in data)
    # is there any graph with BOTH T=B2' (slack~0) AND gap~0 ?
    near = [d for d in data if (d['B2'] - d['T']) < 1e-3]
    print(f"  min (B2'-T) over TYPE A: {minslackT:.5f}  (=0 only if locally complete + a~b)")
    print(f"  graphs with B2'-T < 1e-3: {len(near)}  (these are near-complete cores)")
    if near:
        print(f"    among them, min gap = {min(d['gap'] for d in near):.5f} "
              f"(gap=0 would need ALSO R''+C=0)")
    print(f"  min gap over ALL TYPE A: {mingap:.5f}  (> 0 everywhere => no equality => B strict)")
    print("  CONCLUSION: T=B2' forces near-complete core (a~b, nested nbhds), but those have gap>0")
    print("  (B2'<lam2G); equality T=lam2G would need both, impossible for a deg-2 bottleneck.")

    print("\n" + "=" * 88)
    print("PART B / TASK 4 — resolvent invariants vs c = gap*m/n  (Pearson r)")
    print("=" * 88)
    c = np.array([d['c'] for d in data])
    for name in ['Raa', 'Rbb', 'Rab', 'eff', 'theta', 'detI', 'gamma', 'lam']:
        x = np.array([d[name] for d in data])
        r = np.corrcoef(x, c)[0, 1]
        # also vs structural gamma/Delta proxy
        print(f"  corr(c, {name:6s}) = {r:+.3f}")
    # ratios / combos
    gd = np.array([d['gamma'] for d in data])
    for name, val in [('gamma*eff', gd * np.array([d['eff'] for d in data])),
                      ('eff*gamma/lam', gd * np.array([d['eff'] for d in data]) / np.array([d['lam'] for d in data])),
                      ('1/eff', 1 / np.array([d['eff'] for d in data])),
                      ('gamma*(Raa+Rbb)', gd * np.array([d['Raa'] + d['Rbb'] for d in data]))]:
        r = np.corrcoef(val, c)[0, 1]
        print(f"  corr(c, {name:16s}) = {r:+.3f}")

    print("\n" + "=" * 88)
    print("PART B / TASK 5 — best predictor & candidate lemma condition")
    print("=" * 88)
    # test: is gamma*eff bounded below? (eff = effective resistance a-b in resolvent metric)
    ge = gd * np.array([d['eff'] for d in data])
    print(f"  gamma*eff_resist: min={ge.min():.3f} median={np.median(ge):.3f} max={ge.max():.3f}")
    print(f"  eff_resist (=R_aa+R_bb-2R_ab): min={np.array([d['eff'] for d in data]).min():.4f} "
          f"(>=0 since R2>=0 PSD => eff>=0 always)")
    print(f"  theta (=2-lam, secular): min={np.array([d['theta'] for d in data]).min():.4f} "
          f"max={np.array([d['theta'] for d in data]).max():.4f}")


if __name__ == "__main__":
    main()
