"""
STRESS TEST the carrier-surplus mechanism on multi-bottleneck / adversarial graphs.
Try to BREAK: B (T≤RHS), the regime split (sign Required), and carrier surplus.

surplus_c=λ₂mass_c−energy_c; Deficit=Σ_c surplus_c=λ₂fDf−T; Required=λ₂(λ₂+S²/m−fDf).
B ⟺ Deficit≥Required.  Carriers H={v:f_v²≥1/(2n)}; CSurplus(v)=(A·surplus)_v.
Run:  python conjecture_B_multi_bottleneck.py
"""
import numpy as np
import networkx as nx
from conjecture_B_apex_surplus import apex


def metrics(G, name):
    if not nx.is_connected(G):
        return None
    r = apex(G)
    n = r["n"]; l2 = r["l2"]; fDf = r["fDf"]; S = r["S"]; m = r["m"]
    sp = r["surplus"]; A = r["A"]; f2 = r["f2"]
    Deficit = r["Deficit"]
    Required = l2 * (l2 + S * S / m - fDf)
    T = l2 * fDf - Deficit
    RHS = l2 * (2 * fDf - l2 - S * S / m)
    CS = A @ sp
    H = np.flatnonzero(f2 >= 1.0 / (2 * n))
    total_CS = float(CS[H].sum())
    # interference: carriers sharing a neighbour
    shared = 0
    if len(H) >= 2:
        for c in range(n):
            nb_in_H = sum(1 for v in H if A[c, v] > 0.5)
            if nb_in_H >= 2:
                shared += 1
    massH = float(f2[H].sum())
    return dict(name=name, n=n, l2=l2, T=T, RHS=RHS, Bok=(T <= RHS + 1e-7),
                Deficit=Deficit, Required=Required, nH=len(H), massH=massH,
                total_CS=total_CS, shared=shared,
                defratio=(Deficit / Required if Required > 1e-9 else float('inf')),
                csratio=(total_CS / Required if Required > 1e-9 else float('inf')))


# ---------- family constructors ----------
def fam1_double(m):                       # two deg-2 vertices on one K_m
    G = nx.complete_graph(m)
    G.add_edge(m, 0); G.add_edge(m, 1)
    G.add_edge(m + 1, 2); G.add_edge(m + 1, 3)
    return G


def fam2_kbottle(m, k):                    # k deg-2 vertices on one K_m
    G = nx.complete_graph(m)
    for i in range(k):
        v = m + i
        G.add_edge(v, (2 * i) % m); G.add_edge(v, (2 * i + 1) % m)
    return G


def fam3_disjoint(m):                      # two K_m each + deg-2 vertex, bridged
    G = nx.complete_graph(m)
    G2 = nx.relabel_nodes(nx.complete_graph(m), {i: i + m for i in range(m)})
    G = nx.union(G, G2)
    G.add_edge(0, m)                       # bridge
    G.add_edge(2 * m, 1); G.add_edge(2 * m, 2)        # bottleneck on clique 1
    G.add_edge(2 * m + 1, m + 1); G.add_edge(2 * m + 1, m + 2)  # on clique 2
    return G


def fam4_barbell(m, L):                    # two K_m + path of L nodes
    return nx.barbell_graph(m, L)


def fam5_lollipop(m, L):
    return nx.lollipop_graph(m, L)


def fam6_appendices(m, k, plen):           # K_m + k pendant paths of length plen
    G = nx.complete_graph(m); nxt = m
    for i in range(k):
        prev = i % m
        for _ in range(plen):
            G.add_edge(prev, nxt); prev = nxt; nxt += 1
    return G


def fam7_caterpillar(p, cliq):             # path P_p, a K_cliq hung off each path vertex
    G = nx.path_graph(p); nxt = p
    for u in range(p):
        clique = list(range(nxt, nxt + cliq))
        for a in range(cliq):
            for b in range(a + 1, cliq):
                G.add_edge(clique[a], clique[b])
        G.add_edge(u, clique[0])           # attach clique to path vertex
        nxt += cliq
    return G


def fam8_random(n, p, kbot, seed):         # ER + planted deg-2 vertices
    rng = np.random.default_rng(seed)
    G = nx.gnp_random_graph(n - kbot, p, seed=int(rng.integers(0, 2**31)))
    base = n - kbot
    for i in range(kbot):
        v = base + i
        a, b = rng.choice(range(base), size=2, replace=False)
        G.add_edge(v, int(a)); G.add_edge(v, int(b))
    return G


def main():
    rows = []
    specs = [
        ("F1 double-bottleneck", [fam1_double(48), fam1_double(98), fam1_double(198)]),
        ("F2 k=3 bottleneck", [fam2_kbottle(47, 3), fam2_kbottle(97, 3)]),
        ("F2 k=5 bottleneck", [fam2_kbottle(45, 5), fam2_kbottle(95, 5)]),
        ("F2 k=10 bottleneck", [fam2_kbottle(40, 10), fam2_kbottle(90, 10)]),
        ("F3 disjoint bottlenecks", [fam3_disjoint(24), fam3_disjoint(49), fam3_disjoint(99)]),
        ("F4 barbell L=1", [fam4_barbell(24, 1), fam4_barbell(49, 1)]),
        ("F4 barbell L=3", [fam4_barbell(24, 3), fam4_barbell(49, 3)]),
        ("F4 barbell L=5", [fam4_barbell(24, 5), fam4_barbell(49, 5)]),
        ("F5 lollipop L=5", [fam5_lollipop(45, 5), fam5_lollipop(95, 5)]),
        ("F5 lollipop L=10", [fam5_lollipop(40, 10), fam5_lollipop(90, 10)]),
        ("F6 appendices k=2", [fam6_appendices(46, 2, 2), fam6_appendices(96, 2, 2)]),
        ("F6 appendices k=5", [fam6_appendices(40, 5, 2), fam6_appendices(90, 5, 2)]),
        ("F6 appendices k=10 len3", [fam6_appendices(20, 10, 3), fam6_appendices(40, 10, 3)]),
        ("F7 caterpillar-dense", [fam7_caterpillar(5, 8), fam7_caterpillar(6, 8)]),
        ("F8 random+planted", [fam8_random(50, 0.5, 3, 1), fam8_random(100, 0.4, 5, 2),
                               fam8_random(120, 0.3, 8, 3)]),
    ]
    for label, gs in specs:
        for G in gs:
            r = metrics(G, label)
            if r:
                rows.append(r)

    print("===== TASK 1/2: B holds (T≤RHS) and Required sign =====")
    print(f"{'family':26s} {'n':>4} {'λ₂':>6} {'T':>8} {'RHS':>8} {'B?':>3} {'Required':>9}")
    for r in rows:
        print(f"{r['name']:26s} {r['n']:4d} {r['l2']:6.3f} {r['T']:8.2f} {r['RHS']:8.2f} "
              f"{'OK' if r['Bok'] else 'FAIL':>3} {r['Required']:9.3f}")
    nfail = sum(1 for r in rows if not r["Bok"])
    print(f"  B holds on {len(rows)-nfail}/{len(rows)} graphs")

    print("\n===== TASK 3/4: carriers & carrier surplus (Required>0 cases) =====")
    print(f"{'family':26s} {'n':>4} {'#H':>3} {'massH':>6} {'Deficit':>8} {'Required':>9} "
          f"{'Def/Req':>8} {'ΣCS':>8} {'CS/Req':>7} {'shared':>6}")
    pos = [r for r in rows if r["Required"] > 1e-9]
    for r in pos:
        print(f"{r['name']:26s} {r['n']:4d} {r['nH']:3d} {r['massH']:6.3f} {r['Deficit']:8.3f} "
              f"{r['Required']:9.3f} {r['defratio']:8.3f} {r['total_CS']:8.3f} "
              f"{r['csratio']:7.3f} {r['shared']:6d}")
    print(f"  ({len(pos)}/{len(rows)} graphs have Required>0; the rest are B-trivial)")

    print("\n===== TASK 6: hardest cases =====")
    if pos:
        hd = min(pos, key=lambda r: r["defratio"])
        hc = min(pos, key=lambda r: r["csratio"])
        print(f"  smallest Deficit/Required: {hd['name']} n={hd['n']}  ratio={hd['defratio']:.3f}")
        print(f"  smallest ΣCS/Required:     {hc['name']} n={hc['n']}  ratio={hc['csratio']:.3f}")
        fail_cs = [r for r in pos if r["total_CS"] < r["Required"] - 1e-6]
        print(f"  carrier mechanism failures (ΣCS<Required): {len(fail_cs)}/{len(pos)}")
        for r in fail_cs:
            print(f"     {r['name']} n={r['n']}: ΣCS={r['total_CS']:.3f} < Required={r['Required']:.3f}")
    print(f"  B failures: {nfail}/{len(rows)}")

    print("\n===== TASK 7: regime split check =====")
    neg = [r for r in rows if r["Required"] <= 1e-9]
    print(f"  Required≤0 (B-trivial via Deficit≥0): {len(neg)}/{len(rows)} graphs; "
          f"all have Deficit≥0: {all(r['Deficit']>=-1e-7 for r in neg)}")
    print(f"  Required>0 (need carrier surplus): {len(pos)}/{len(rows)}; "
          f"all have ΣCS≥Required: {all(r['total_CS']>=r['Required']-1e-6 for r in pos)}")


if __name__ == "__main__":
    main()
