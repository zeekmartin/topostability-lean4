# Conjecture B — two-regime strategy ⇒ a single uniform degree-only reduction

**Main outcome: no two-regime split is needed.** The min−1 reduction (with the
*correct* lift RHS) holds **uniformly** on the entire corpus and every hard family,
giving a rigorous reduction of B to a single **degree-only** eigenvector
inequality — and **correcting** the earlier "min-degree route is dead at scale"
conclusion, which was an artifact of a *too-small* RHS. Code:
[`conjecture_B_two_regime.py`](../conjecture_B_two_regime.py).

`A := fᵀDf − λ₂`; identity `fᵀ(D+A)f = λ₂ + 2A`. `S = Σ_v d_v f_v`, `m=|E|`,
`W₁ := Σ_{ab∈E}(min(d_a,d_b)−1)(f_a−f_b)²`.

---

## The reduction (rigorous chain), and the correction

The **projected** Fiedler lift `h' = Bᵀf − (S/m)1_E ⟂ 1_E` gives (exactly):

> `λ₂(T(G)) ≤ R_T(h') = fᵀL_t f / (fᵀ(D+A)f − S²/m)`.

So **B follows from `fᵀL_t f ≤ λ₂·(fᵀ(D+A)f − S²/m)`** (the *true* lift target),
and via `t_{ab} ≤ min(d_a,d_b)−1` (Lean-verified `triCount_le_min_degree_sub_one`):

> **(B2′)  `W₁ = Σ(min(d_a,d_b)−1)(f_a−f_b)² ≤ λ₂·(fᵀ(D+A)f − S²/m)`  ⟹ B.**

**(B2′) holds on 9020/9020 corpus graphs** (worst ratio 1.0000, attained only at
`K_n`) **and on every hard family:** deg2+dense `n≤40` (worst 0.873), deg3+dense
(0.727), large Watts–Strogatz (1.000), dense ER (0.892), `K_n−e` to `n=150`
(`(n−3)/(n−2)→1`). **Zero violations.**

**Correction of the earlier "dead route".** `conjecture_B_complement_hard_cases.md`
concluded the min-degree relaxation fails at scale — but that tested the *variant*
`Σ(min−δ)(f_a−f_b)² ≤ R″` with `R″ = λ₂(fᵀDf−λ₂+1−S²/m)`. The **correct** lift RHS
is `λ₂(fᵀ(D+A)f − S²/m) = λ₂(2fᵀDf−λ₂−S²/m)`, which is **larger than `R″` by
`λ₂(fᵀDf−1)`**. Against the correct (larger) RHS — and with the weight `min−1`
(not `min−δ`) — the reduction holds everywhere. The "failure at scale" was a
too-small-RHS artifact, not a real obstruction. **The degree-only route is alive.**

(This is exactly the v2 inequality `(DEG)`; the v3→`C4`→`R″` reformulations chased a
mis-shifted RHS and wrongly reported failure.)

---

## PHASE 1 — regime characterization

**1.1 Distribution of `A`.** Over 9020 distinct corpus graphs: `A ∈ [−1, 2.43]`,
median 1.03. Histogram is **smooth — no gap at 1.5** (`[1.25,1.5): 1593`,
`[1.5,1.75): 675`). `A≥1.5`: 944 graphs; `A<1.5`: 8076. (`A=−1` only at `K_n`.)

**1.2 Bounds on `fᵀL_t f` (closure of B), `A≥1.5` regime (944 graphs):**

| bound on `fᵀL_t f` | closes B? |
|---|---|
| `(Δ−1)·λ₂` (crude, `t≤Δ−1`) | **48.6%** — graph-dependent |
| `Δ·λ₂` (`d_max`) | 9.1% |
| `3·#triangles·λ₂` (max-gradient) | 0% |
| **`W₁` (min−1)** | **100%** |

Only the min−1 bound closes uniformly. (Same picture for `A<1.5`: B1 12%, B3 1%,
B4 0%, **B2 100%**.) The tightest `fᵀL_t f / λ₂(fᵀQf)` is `0.585` for `A≥1.5` (B has
margin there) and `→1` for `A<1.5` (tight at `K_n`).

**1.3 Small-A (`A<1.5`) structure — the proposed characterizations are FALSE:**
- complement `|H|`: median 11 (range 0–21) — *not* uniformly small;
- degree spread `Δ−δ`: median 4, only **12%** are near-regular (`≤2`) — **not
  close to regular**;
- `λ₂/(d_max−1)`: median **0.45** — `λ₂` is **not** close to `d_max−1`.

So `A<1.5` is **not** a clean "near-complete / near-regular / `λ₂≈d_max−1`" regime.
This is *moot*, since B2′ needs no regime split.

---

## PHASE 2 — the regimes (both subsumed by B2′)

**REGIME A (large excess).** The crude bound `fᵀL_t f ≤ (Δ−1)λ₂` closes B iff
`Δ−1 ≤ λ₂+2A`, i.e. `A ≥ A₁* := (d_max−1−λ₂)/2`. `A₁*` has **median 1.63, max
2.90 > corpus max A (2.43)** — so the crude bound is **graph-dependent and never
uniformly closes**. The `min−1` refinement (B2′) removes this dependence: it holds
for **all** `A`.

**REGIME B (small excess).** Complement-perturbation / edge-induction is dead:
`Δ` is **not monotone** under edge addition/removal (68% of single-edge additions
*increase* `Δ`; `conjecture_B_global_variational.md`), and `Δ` does not decompose
additively over missing edges (`Δ(K_n−e)=n−2` but `Δ(K_n−△)=n−3`). So no induction
from `K_n`. Again moot — B2′ covers small-A directly (it is *tight* there, ratio→1).

---

## PHASE 3 — the threshold

**There is no threshold to find: `c` is not needed.** B2′ is uniform (holds for all
`A`, including `A=−1` at `K_n` where it is equality). The two-regime framing was
predicated on the crude bound needing `A` large; the min−1 bound makes the split
unnecessary. (If one *insisted* on the crude `(Δ−1)λ₂` bound, no finite uniform `c`
works — its threshold `A₁*` exceeds the corpus's max `A`.)

`B2′` is **tight exactly at `K_n`** (ratio 1) and approaches 1 along `K_n−e`
(`(n−3)/(n−2)`), so it is a *faithful* reduction — as tight as B itself on the
extremal family, never violated.

---

## Synthesis — the genuine open problem (degree-only)

Conjecture B reduces, rigorously and uniformly, to a **triangle-free, degree-only
eigenvector inequality**:

> **Prove:** for the unit Fiedler `f` of any connected non-bipartite `G`,
> `Σ_{ab∈E}(min(d_a,d_b)−1)(f_a−f_b)² ≤ λ₂(G)·(fᵀ(D+A)f − S²/m)`.

- **Rigorous chain:** projected lift (exact) + `t_{ab} ≤ min(d_a,d_b)−1`
  (Lean-verified). The triangle counts `t_{ab}` are eliminated.
- **Status:** holds on 9020 corpus + all hard families (deg2+dense, deg3+dense,
  WS, ER, `K_n−e` to n=150); 0 violations; tight only at `K_n`.
- **Still eigenvector-bound:** the operator `λ₂Q − L_{md}` is indefinite on `1⊥`
  (since `L_{md} ⪰ L_t` and even `λ₂Q−L_t` is indefinite — `conjecture_B_global_
  variational_search.md`), so a proof must use `L_G f = λ₂ f` (and the `−S²/m`
  term, which is `f`-specific via `S=fᵀd`). But it is now a clean degree-and-Fiedler
  statement, no longer entangled with the triangle structure.

This **reopens** the degree-based line that was previously (erroneously) closed, and
pins the remaining work to one inequality.

### Caveats
- `λ₂`, `f` numerical; B2′ verified on 9020 distinct corpus graphs (n≤9) + hard
  families (n up to 150 for `K_n−e`). The reduction `B ⟸ B2′` is rigorous (lift +
  Lean-verified `t≤min−1`); B2′ itself is empirically universal, not yet proven.
  Worst ratio 1.0 occurs at `K_n` (equality), consistent with equality⟺`K_n`.
