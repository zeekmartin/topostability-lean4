# Conjecture B — three micro-projects: a refuted lemma, the D_v⁺ obstruction, and the tightness predictor

Three focused experiments on the lock
`W = Σ_v(d_v−δ)D_v⁺ ≤ λ₂(fᵀDf−λ₂+1−S²/m)` (unit Fiedler `f`, `D_v⁺ =
Σ_{b∼v, d_b>d_v}(f_v−f_b)²`). Code:
[`conjecture_B_three_projects.py`](../conjecture_B_three_projects.py).

**Headline.** (1) `fᵀDf ≤ d̄` is **not a theorem** — it fails on Watts–Strogatz and
adversarial graphs (v4 overstated it; corrected below). (2) Every *eigenvector-
value-based* bound on `D_v⁺` is impossible (it can be large where `f_v=0`); only
degree-based forms survive, and none closes the lock by naive summation. (3) The
predictor of tightness is sharp: on the tightest graphs the **hubs carry zero
uphill energy** (`D_v⁺·d_v ≈ 0`), because top-degree vertices have *no* higher-
degree neighbours.

---

## Project 1 — `fᵀDf ≤ d̄` (avg degree): **REFUTED**

Stress-tested the unit-Fiedler inequality (worst-case over the whole
`λ₂`-eigenspace, to be multiplicity-robust) across 7 families, **2954 graphs**:

| family | count | max ratio `fᵀDf/d̄` | mean |
|---|---|---|---|
| Erdős–Rényi `G(n,p)`, n≤100 | 1000 | 0.95 | 0.73 |
| Barabási–Albert | 500 | 0.83 | 0.61 |
| Watts–Strogatz | 498 | **1.016** ❌ | 0.94 |
| random regular | 356 | 1.000 (=d̄, equality) | 1.00 |
| bipartite random | 196 | 0.91 | 0.51 |
| near-Ramanujan (random regular) | 71 | 1.000 | 1.00 |
| **adversarial** (stars, double-brooms, barbells) | 333 | **1.153** ❌ | 0.95 |

- **118 violations.** Closest/worst: an adversarial double-broom, `n=17, m=36`,
  ratio **1.153** (`fᵀDf` exceeds average degree by 15%).
- It even fails on **triangle-rich** graphs (`T(G)` connected): 3/1310, max ratio
  1.0071 (a Watts–Strogatz graph, `n=27`). So the restriction to the lock's domain
  does **not** rescue it.
- Regular/expander graphs give exactly `1.000` (`fᵀDf=d=d̄`), the equality case.

**Verdict: `fᵀDf ≤ d̄` is false.** It held 1734/1734 in v4 only because that set was
dense `G(n,p)` (`p∈[0.45,0.97]`), where hub-flatness is strong; sparser clustered
(WS) and high-variance (broom/barbell) graphs break it. **No proof attempt** — the
statement is not a theorem.

> **Correction to v4.** The "clean corollary `fᵀDf ≤ d̄`" stated in
> `conjecture_B_proof_v4.md §A2` is **withdrawn**. The hub-flatness *correlation*
> (`corr(deg, f²) ≈ −0.8`) remains real on average, but it does **not** upgrade to
> the pointwise inequality `fᵀDf ≤ d̄`.

---

## Project 2 — bounding `D_v⁺`: the eigenvector-value forms are impossible

Tested four candidate bounds over 1308 `T(G)`-connected graphs (every vertex):

| candidate | result |
|---|---|
| **(a)** `D_v⁺ ≤ C/d_v` | ✅ finite `C = max(D_v⁺·d_v) = 66.7` (form valid; `C` large, likely grows with `n`) |
| **(b)** `D_v⁺ ≤ C·f_v²` | ❌ **no finite C** — `D_v⁺>0` while `f_v=0` on **678** vertices |
| **(c)** `D_v⁺ ≤ C·λ₂/d_v` | ✅ finite `C = max(D_v⁺·d_v/λ₂) = 6.75` (best simple form) |
| **(d)** `D_v⁺ ≤ (d_v−λ₂)²f_v²/d_v` | ❌ breaks on the same 678 vertices; ratio up to `8.5×10⁷` |

**The decisive obstruction:** `D_v⁺` can be **large where `f_v = 0`**. This happens
at symmetry-fixed vertices (an automorphism swapping the two nodal domains forces
`f_v=0`, yet the vertex still has neighbours with `f≠0`). So **any bound with an
`f_v²` factor — (b) and (d), including the eigenvector-equation form — is
impossible.** Only the *degree-based* forms (a), (c) survive.

But (a)/(c) do **not close the lock by naive summation**: with `D_v⁺ ≤ Cλ₂/d_v`,
`Σ_v(d_v−δ)D_v⁺ ≤ Cλ₂ Σ_v(1−δ/d_v) ≤ Cλ₂·n`, which far exceeds
`R'' ≈ λ₂·fᵀDf`. **No per-vertex bound on `D_v⁺` closes the lock** — the
anticorrelation must be exploited *collectively over the sum*, not vertex-by-vertex.

---

## Project 3 — what makes the 52 tightest graphs special?

`D_v⁺` at hubs (top-25% degree) vs leaves (bottom-25% degree):

| set | mean `D_v⁺` hubs | mean `D_v⁺` leaves | leaf/hub ratio | hub-flatness `max(D_v⁺·d_v)` (median) |
|---|---|---|---|---|
| **tight (52)** | **0.0046** | 2.15 | **472×** | **0.0000** |
| broad | 0.027 | 1.36 | 51× | 0.129 |

**On the tightest graphs the hubs carry essentially *zero* uphill energy**
(`max(D_v⁺·d_v)` has median **exactly 0**). Structural reason: the tightest graphs
are near-complete (`K_n−ke`), where almost all vertices share the maximum degree
`n−1`; a top-degree vertex has **no strictly-higher-degree neighbour**, so
`D_v⁺ = 0` *exactly* there. Only the two low-degree endpoints of a removed edge
contribute to `W`, and with small weight `(d−δ)` — so `W` is tiny and `(C4'')`
holds with wide margin.

**Predictor of tightness:** *the high-degree-excess vertices have no higher-degree
neighbours.* Equivalently, `W` concentrates entirely on the (few, low-weight)
bottom-degree vertices. This is a **combinatorial** statement about the degree
sequence — "you cannot be simultaneously high-degree and have many higher-degree
neighbours" — and is sharper than the f-value "flat at hubs" picture.

---

## Synthesis — the refined proof direction

The three projects converge on one message. The lock `W = Σ_v(d_v−δ)D_v⁺` should
be attacked **combinatorially via the degree sequence**, not via Fiedler values:

- value-based bounds (`f_v²`) are provably impossible (P2);
- the controlling effect is that **`d_v−δ` large ⟹ few uphill neighbours ⟹ `D_v⁺`
  small** (P3) — a constraint on the degree sequence, independent of `f`;
- and it must be summed collectively (P2), e.g. by a rearrangement / level-set
  argument over degree classes, bounding `Σ_v(d_v−δ)·(#uphill neighbours of v)·
  (local gradient)` using that the uphill-neighbour count drops as degree rises.

`fᵀDf ≤ d̄` is **not** available as a lemma (P1). The remaining lock stands, now
with a clear, value-free line of attack.

### Caveats
- `λ₂` numerical; P1 worst-case over the `λ₂`-eigenspace. Adversarial family is
  hand-built (stars/brooms/barbells). P2/P3 on `T(G)`-connected graphs (52 tight +
  ~1256 broad, n≤14).
