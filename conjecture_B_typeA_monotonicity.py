"""
TYPE A gap monotonicity under core edge addition/deletion.

G = H + v0 (v0~{a,b}).  gap(H) = lam2(G)*(sum_e h^2 - S^2/m) - B2'.
If gap is monotone DECREASING in the core edge set (adding a core edge lowers gap), then the
complete core minimizes gap among cores on the same vertex set; since complete core is proved
positive (gap=10(n-3)/m>0), ALL TYPE A would follow.

Tests (keeping TYPE A: lam2(G) < lam2(core), v0 the bottleneck):
  - add a random core non-edge e: is gap(H+e) <= gap(H)?
  - delete a random core edge e:  is gap(H-e) >= gap(H)?
  - monotone path sparse -> complete: is gap monotonically decreasing?
Run: python conjecture_B_typeA_monotonicity.py
"""
import numpy as np
import networkx as nx


def gap_of(H, a=0, b=1):
    """gap of G = H + v0 attached at a,b; returns (gap, lam2G, gammaCore, fv0sq) or None if disconnected."""
    H = nx.convert_node_labels_to_integers(H)
    nH = H.number_of_nodes()
    if not nx.is_connected(H):
        return None
    G = nx.Graph(H); G.add_node(nH); G.add_edge(nH, a); G.add_edge(nH, b)
    nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}
    A = nx.to_numpy_array(G, nodelist=nodes); d = A.sum(1); L = np.diag(d) - A
    ev, U = np.linalg.eigh(L); lam = ev[1]; f = U[:, 1]; f = f / np.linalg.norm(f)
    v0 = idx[nH]
    if f[v0] < 0: f = -f
    m = G.number_of_edges(); S = float(d @ f)
    Gsum = sum((f[idx[u]] + f[idx[v]]) ** 2 for u, v in G.edges())
    B2 = sum((min(d[idx[u]], d[idx[v]]) - 1) * (f[idx[u]] - f[idx[v]]) ** 2 for u, v in G.edges())
    gap = lam * (Gsum - S ** 2 / m) - B2
    LH = nx.laplacian_matrix(H, nodelist=list(range(nH))).toarray().astype(float)
    gammaC = float(np.linalg.eigvalsh(LH)[1])
    return gap, lam, gammaC, float(f[v0]) ** 2


def is_typeA(res):
    return res is not None and res[1] < res[2] and res[3] > 0.3   # lam2G<gammaCore, v0 bottleneck


def main():
    rng = np.random.default_rng(0)
    print("=" * 88)
    print("TEST 1 — add a core non-edge: gap(H+e) <= gap(H) ?   (TYPE A preserved)")
    print("=" * 88)
    add_ok = add_bad = 0; add_examples = []
    for trial in range(40):
        nH = int(rng.integers(20, 45))
        q = float(rng.uniform(0.25, 0.85))
        H = nx.gnp_random_graph(nH, q, seed=int(rng.integers(1e6)))
        r0 = gap_of(H)
        if not is_typeA(r0): continue
        nonedges = [(u, v) for u in range(nH) for v in range(u + 1, nH) if not H.has_edge(u, v)]
        if not nonedges: continue
        for _ in range(3):
            e = nonedges[int(rng.integers(len(nonedges)))]
            H2 = H.copy(); H2.add_edge(*e)
            r1 = gap_of(H2)
            if not is_typeA(r1): continue
            if r1[0] <= r0[0] + 1e-9: add_ok += 1
            else:
                add_bad += 1
                if len(add_examples) < 5:
                    add_examples.append((nH, round(q, 2), e, round(r0[0], 5), round(r1[0], 5)))
    print(f"  gap(H+e) <= gap(H): {add_ok}/{add_ok+add_bad}   violations: {add_bad}")
    for ex in add_examples:
        print(f"    VIOLATION n={ex[0]} q={ex[1]} e={ex[2]} gap(H)={ex[3]} gap(H+e)={ex[4]}")

    print("\n" + "=" * 88)
    print("TEST 2 — delete a core edge: gap(H-e) >= gap(H) ?   (TYPE A preserved, stays connected)")
    print("=" * 88)
    del_ok = del_bad = 0; del_examples = []
    for trial in range(40):
        nH = int(rng.integers(20, 45))
        q = float(rng.uniform(0.35, 0.9))
        H = nx.gnp_random_graph(nH, q, seed=int(rng.integers(1e6)))
        r0 = gap_of(H)
        if not is_typeA(r0): continue
        edges = list(H.edges())
        for _ in range(3):
            e = edges[int(rng.integers(len(edges)))]
            H2 = H.copy(); H2.remove_edge(*e)
            r1 = gap_of(H2)
            if not is_typeA(r1): continue
            if r1[0] >= r0[0] - 1e-9: del_ok += 1
            else:
                del_bad += 1
                if len(del_examples) < 5:
                    del_examples.append((nH, round(q, 2), e, round(r0[0], 5), round(r1[0], 5)))
    print(f"  gap(H-e) >= gap(H): {del_ok}/{del_ok+del_bad}   violations: {del_bad}")
    for ex in del_examples:
        print(f"    VIOLATION n={ex[0]} q={ex[1]} e={ex[2]} gap(H)={ex[3]} gap(H-e)={ex[4]}")

    print("\n" + "=" * 88)
    print("TEST 3 — monotone path sparse -> complete core: is gap monotonically DECREASING?")
    print("=" * 88)
    for nH in [25, 35]:
        H = nx.gnp_random_graph(nH, 0.3, seed=1)
        # ensure connected
        while not nx.is_connected(H):
            H = nx.gnp_random_graph(nH, 0.3, seed=int(rng.integers(1e6)))
        nonedges = [(u, v) for u in range(nH) for v in range(u + 1, nH) if not H.has_edge(u, v)]
        rng.shuffle(nonedges)
        gaps = []; typeA_flags = []
        cur = H.copy()
        r = gap_of(cur); gaps.append(r[0]); typeA_flags.append(is_typeA(r))
        for e in nonedges:
            cur.add_edge(*e)
            r = gap_of(cur)
            gaps.append(r[0] if r else np.nan); typeA_flags.append(is_typeA(r))
        gaps = np.array(gaps)
        # count monotone-decreasing steps (within TYPE A region)
        dec = sum(1 for i in range(1, len(gaps)) if gaps[i] <= gaps[i - 1] + 1e-9)
        inc = (len(gaps) - 1) - dec
        complete_gap = 10 * (nH + 1 - 3) / (nH * (nH - 1) // 2 + 2)  # n=nH+1
        print(f"  nH={nH}: {len(gaps)} cores (sparse->complete); decreasing steps {dec}/{len(gaps)-1}, "
              f"increasing {inc}")
        print(f"    gap range [{np.nanmin(gaps):.5f}, {np.nanmax(gaps):.5f}]; final(complete)="
              f"{gaps[-1]:.5f} vs 10(n-3)/m={complete_gap:.5f}; min is at complete: "
              f"{abs(np.nanmin(gaps)-gaps[-1])<1e-6}")

    print("\n" + "=" * 88)
    print("TEST 4 — is the complete core the global minimizer of gap (fixed nH)?")
    print("=" * 88)
    for nH in [20, 30]:
        comp = gap_of(nx.complete_graph(nH))
        comp_gap = comp[0]
        below = 0; tested = 0; minval = comp_gap
        for q in [0.4, 0.55, 0.7, 0.85]:
            for s in range(8):
                H = nx.gnp_random_graph(nH, q, seed=s)
                r = gap_of(H)
                if not is_typeA(r): continue
                tested += 1; minval = min(minval, r[0])
                if r[0] < comp_gap - 1e-9: below += 1
        print(f"  nH={nH}: complete-core gap={comp_gap:.5f}; cores with gap < complete: {below}/{tested}; "
              f"min gap found={minval:.5f}")

    print("\n" + "=" * 88)
    print("SUMMARY: if add=>decrease & complete=minimizer hold, TYPE A reduces to complete-core proof.")
    print("=" * 88)


if __name__ == "__main__":
    main()
