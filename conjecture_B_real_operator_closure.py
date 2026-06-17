"""
Closure analysis on the REAL-triangle operator  M = λ₂Q - L_t  (t_ab=(A²)_ab),
side-by-side with the min-degree relaxation  K = λ₂Q - L_min.
f = unit Fiedler.  Family: deg2+dense.

TASK 1: negative-cone structure of M (hub-mass, f-overlap, neg/pos) vs K.
TASK 2: hub-flatness closure on M:  neg_bound (using f_v²≤d_v/(d_v-λ₂)² on hubs) vs pos.
TASK 3: relaxation loss  W₁ - fᵀL_tf  by edge class.
TASK 4: source of the real margin fᵀMf, by edge class.
Run:  python conjecture_B_real_operator_closure.py
"""
import numpy as np
import networkx as nx


def deg2dense(n, q, seed):
    rng = np.random.default_rng(seed)
    G = nx.gnp_random_graph(n - 1, q, seed=int(rng.integers(0, 2**31)))
    G = nx.relabel_nodes(G, {i: i + 1 for i in range(n - 1)}); G.add_node(0)
    for b in rng.choice(range(1, n), size=2, replace=False):
        G.add_edge(0, int(b))
    return G


def setup(G):
    nodes = list(G.nodes()); n = len(nodes)
    L = nx.laplacian_matrix(G, nodelist=nodes).toarray().astype(float)
    d = L.diagonal().copy(); A = np.diag(d) - L; m = int(G.number_of_edges())
    ev, V = np.linalg.eigh(L); l2 = float(ev[1]); f = V[:, 1] / np.linalg.norm(V[:, 1])
    A2 = A @ A
    Wt = A * A2                          # t_ab on edges
    Lt = np.diag(Wt @ np.ones(n)) - Wt
    Wm = np.zeros((n, n))
    for i, j in np.argwhere(np.triu(A, 1) > 0.5):
        wt = min(d[i], d[j]) - 1
        Wm[i, j] = wt; Wm[j, i] = wt
    Lmin = np.diag(Wm @ np.ones(n)) - Wm
    Q = np.diag(d) + A
    M = l2 * Q - Lt
    K = l2 * Q - Lmin
    return dict(n=n, m=m, l2=l2, f=f, d=d, A=A, A2=A2, Q=Q, Lt=Lt, Lmin=Lmin,
                M=M, K=K, fDf=float((d * f * f).sum()), S=float(d @ f))


def cone(op, f, d):
    n = len(d); w, U = np.linalg.eigh(op); a = U.T @ f
    med = np.median(d)
    hub = d > med
    pos = neg = 0.0; negc = posc = 0.0
    hub_masses = []; overlaps = []; mus = []
    Hflat = float(np.sum(d[hub] / (d[hub] - 1e-9) ** 0))  # placeholder, set below
    for j in range(n):
        mu = w[j]; vj = U[:, j]; ov = a[j] ** 2
        if mu > 1e-12:
            pos += mu * ov; posc += mu * ov
        elif mu < -1e-12:
            neg += -mu * ov; negc += -mu * ov
            hub_masses.append(float(np.sum(vj[hub] ** 2)))
            overlaps.append(ov); mus.append(mu)
    return dict(w=w, U=U, a=a, pos=pos, neg=neg, hub=hub,
                hub_masses=np.array(hub_masses), overlaps=np.array(overlaps),
                mus=np.array(mus), nneg=int(np.sum(w < -1e-12)))


def task1():
    print("===== TASK 1: negative-cone structure  (M = real triangles | K = min-degree) =====")
    print("   n  | op | #neg | neg/pos | hubmass med/min | frac>0.5 | negContrib | posContrib | margin")
    for n in (50, 100, 200, 500, 1000):
        G = deg2dense(n, 0.65, seed=42 + n)
        if not nx.is_connected(G):
            continue
        s = setup(G)
        for tag, op in (("M", s["M"]), ("K", s["K"])):
            c = cone(op, s["f"], s["d"])
            hm = c["hub_masses"]
            negC = float(np.sum(-c["mus"] * c["overlaps"])) if len(c["mus"]) else 0.0
            # negContrib already = neg; posContrib = pos
            ratio = c["neg"] / c["pos"] if c["pos"] > 0 else float("nan")
            marg = (c["pos"] - c["neg"]) / c["pos"] if c["pos"] > 0 else float("nan")
            fr = float(np.mean(hm > 0.5)) if len(hm) else float("nan")
            print(f"  {n:4d} | {tag}  | {c['nneg']:4d} | {ratio:7.4f} | "
                  f"{np.median(hm):.3f}/{hm.min() if len(hm) else 0:.3f} | {fr:7.2f}  | "
                  f"{c['neg']:10.3f} | {c['pos']:10.3f} | {marg:.4f}")


def task2():
    print("\n===== TASK 2: hub-flatness closure on M  (neg_bound vs pos_actual) =====")
    print("  uses f_v² ≤ d_v/(d_v-λ₂)² on HUB coords (rigorous); low coords: Σf²≤1 (rig) or actual")
    print("   n  | op | neg_bound/pos (rigorous low≤1) | (semi-emp low=actual) | actual neg/pos")
    for n in (50, 100, 200, 500):
        G = deg2dense(n, 0.65, seed=42 + n)
        if not nx.is_connected(G):
            continue
        s = setup(G); d = s["d"]; f = s["f"]; l2 = s["l2"]
        med = np.median(d); hub = d > med; low = ~hub
        Hflat = float(np.sum(d[hub] / (d[hub] - l2) ** 2))   # ≥ Σ_hub f_v²  (hub-flatness)
        low_f_actual = float(np.sum(f[low] ** 2))
        for tag, op in (("M", s["M"]), ("K", s["K"])):
            w, U = np.linalg.eigh(op); a = U.T @ f
            nb_rig = nb_emp = pos = 0.0
            for j in range(len(d)):
                mu = w[j]; vj = U[:, j]
                if mu > 1e-12:
                    pos += mu * a[j] ** 2
                elif mu < -1e-12:
                    hmj = float(np.sum(vj[hub] ** 2)); lmj = float(np.sum(vj[low] ** 2))
                    hub_part = np.sqrt(Hflat * hmj)
                    ob_rig = (hub_part + np.sqrt(1.0 * lmj)) ** 2
                    ob_emp = (hub_part + np.sqrt(low_f_actual * lmj)) ** 2
                    nb_rig += (-mu) * ob_rig; nb_emp += (-mu) * ob_emp
            actual_neg = float(np.sum([(-w[j]) * a[j] ** 2 for j in range(len(d)) if w[j] < -1e-12]))
            print(f"  {n:4d} | {tag}  | {nb_rig/pos:24.2f} | {nb_emp/pos:21.3f} | {actual_neg/pos:.4f}")


def edge_class(d, i, j, med):
    hi = d[i] > med; hj = d[j] > med
    if hi and hj:
        return "dense-dense"
    if hi or hj:
        return "low-dense"
    return "low-low"


def task3():
    print("\n===== TASK 3: relaxation loss  W₁ - fᵀL_tf  by edge class =====")
    for n in (100, 200, 500):
        G = deg2dense(n, 0.65, seed=42 + n)
        if not nx.is_connected(G):
            continue
        s = setup(G); d = s["d"]; f = s["f"]; A2 = s["A2"]; A = s["A"]; l2 = s["l2"]
        med = np.median(d)
        cls = {}
        W1 = T = 0.0
        for i, j in np.argwhere(np.triu(A, 1) > 0.5):
            g = (f[i] - f[j]) ** 2
            t = A2[i, j]; w1 = (min(d[i], d[j]) - 1)
            c = edge_class(d, i, j, med)
            r = cls.setdefault(c, dict(W1=0.0, T=0.0, defc=0.0, gsum=0.0, cnt=0))
            r["W1"] += w1 * g; r["T"] += t * g; r["defc"] += (w1 - t)
            r["gsum"] += g; r["cnt"] += 1
            W1 += w1 * g; T += t * g
        loss = W1 - T
        fQf = 2 * s["fDf"] - l2; lift = l2 * (fQf - s["S"] ** 2 / s["m"])
        real_marg = lift - T; relaxed_marg = lift - W1
        print(f"  n={n}: T/W₁={T/W1:.3f}  loss={loss:.3f}  loss/real_marg={loss/real_marg:.2f}  "
              f"loss/|relaxed_marg|={loss/abs(relaxed_marg) if abs(relaxed_marg)>1e-9 else float('inf'):.2f}")
        print(f"     class        | W₁contrib | Tcontrib | loss  | avgDeficit | avgGrad²")
        for c in ("low-low", "low-dense", "dense-dense"):
            if c in cls:
                r = cls[c]
                print(f"     {c:12s} | {r['W1']:9.3f} | {r['T']:8.3f} | {r['W1']-r['T']:6.3f} | "
                      f"{r['defc']/r['cnt']:10.2f} | {r['gsum']/r['cnt']:.2e}  (n={r['cnt']})")


def task4():
    print("\n===== TASK 4: source of the real margin fᵀMf =====")
    for n in (100, 200, 500):
        G = deg2dense(n, 0.65, seed=42 + n)
        if not nx.is_connected(G):
            continue
        s = setup(G); d = s["d"]; f = s["f"]; A2 = s["A2"]; A = s["A"]; l2 = s["l2"]
        med = np.median(d)
        # T by class + Q-form proxy; fᵀMf = λ₂ fᵀQf - T
        fQf = 2 * s["fDf"] - l2
        T_by = {}
        for i, j in np.argwhere(np.triu(A, 1) > 0.5):
            c = edge_class(d, i, j, med)
            T_by[c] = T_by.get(c, 0.0) + A2[i, j] * (f[i] - f[j]) ** 2
        T = sum(T_by.values()); fMf = l2 * fQf - T
        print(f"  n={n}: λ₂·fᵀQf={l2*fQf:.3f}  T=fᵀL_tf={T:.3f}  fᵀMf={fMf:.3f}")
        for c in ("low-low", "low-dense", "dense-dense"):
            if c in T_by:
                print(f"     T[{c:12s}]={T_by[c]:7.3f} ({100*T_by[c]/T:4.1f}% of T)")
        # gradient suppression on dense edges: avg t_ab (big) but avg grad (small)
        dd_t = []; dd_g = []
        for i, j in np.argwhere(np.triu(A, 1) > 0.5):
            if d[i] > med and d[j] > med:
                dd_t.append(A2[i, j]); dd_g.append((f[i] - f[j]) ** 2)
        print(f"     dense-dense: avg t_ab={np.mean(dd_t):.1f} (large) but avg grad²={np.mean(dd_g):.2e} (tiny) "
              f"=> T suppressed by FLAT Fiedler on dense edges")


if __name__ == "__main__":
    task1()
    task2()
    task3()
    task4()
