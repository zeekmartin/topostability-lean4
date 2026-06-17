# Conjecture B — the direct Dirichlet-energy route

Target (no B2′, no min-degree relaxation): `T = fᵀL_t f = Σ_ab t_ab(f_a−f_b)² ≤
RHS := λ₂(fᵀQf − S²/m)`, which implies B via the projected lift. Code:
[`conjecture_B_dirichlet_energy_route.py`](../conjecture_B_dirichlet_energy_route.py).

**Headline.** The route is **sound** — `T ≤ RHS` holds with a **stable margin ≈ 0.18** at
scale (deg2+dense to `n=1000`), and the apex identity `T = Σ_c E_{G[N(c)]}(f)` is exact.
The **per-edge gradient bound** (symmetric-difference Cauchy–Schwarz) is rigorous and
holds for **all** edges. But **every aggregation fails on the binding family**: the
`t_ab`-weighted product bound is loose by `10⁰–10⁷`, and the clean aggregate
triangle-Poincaré `T ≤ λ₂fᵀDf` (which holds **100%**, even where the *local* Poincaré
fails) overshoots `RHS` on deg2+dense. No elementary energy bound closes B on the binding
family — the `−S²/m` term and `λ₂`-minimality remain essential.

---

## TASK 0 — apex identity (exact, no factor-2)

`T = Σ_c E_{G[N(c)]}(f)` verified to **1.8×10⁻¹⁴**, with
`E_{G[N(c)]}(f) = Σ_{ab∈E(G[N(c)])}(f_a−f_b)²` (sum over undirected neighborhood-edges,
**no ½**). Each triangle `c–a–b` contributes `(f_a−f_b)²` once per common neighbor `c`,
recovering `Σ_ab t_ab(f_a−f_b)²`.

## TASK 1 — `T/RHS` at scale: sound, stable margin

| | max `T/RHS` | margin |
|---|---|---|
| corpus `n≤9` | 1.0000 (at `K_n`, equality) | median ratio 0.44 |
| deg2+dense `n=50` | 0.748 | 0.25 |
| deg2+dense `n=500` | 0.815 | 0.19 |
| deg2+dense `n=1000` | 0.820 | **0.18** |

`T ≤ RHS` holds everywhere; on deg2+dense the margin **stabilizes ≈ 0.18** (does not → 0,
unlike the min-degree `C+R″`). So the actual-triangle lift bound is the right, stable
target.

## TASK 2 — symmetric-difference gradient bound (rigorous, holds for all edges)

From the eigen-equation `(d_a−λ₂)f_a−(d_b−λ₂)f_b = Σ_{u∈N(a)△N(b)} ±f_u` and
Cauchy–Schwarz:

> `(f_a−f_b)² ≤ |N(a)△N(b)| · Σ_{u∈N(a)△N(b)} f_u² / (min(d_a,d_b)−λ₂)²`.

**0 violations** over 199 523 corpus edges and all deg2+dense edges (to `n=500`),
**including low-dense edges** (very unequal degrees). Tight on some edges
(max `grad²/bound = 0.999`). This is a genuine, rigorous per-edge bound (eigen-equation +
C-S, no empirical inputs).

## TASK 3 — product bound `T_bound = Σ t_ab · grad_bound`: catastrophic

| | `T_bound/RHS` |
|---|---|
| corpus `n≤9` | median **12.8**, max ∞ |
| deg2+dense `n=100` | 19.2 |
| deg2+dense `n=200` | 3.1×10⁶ |
| deg2+dense `n=500` | 3.3×10⁷ |

The per-edge bound is **tight where `t_ab` is small** (low-dense edges, where `f` varies)
and **hopelessly loose where `t_ab` is large** (dense-dense edges, where `f` is flat but
the bound `|N△|·Σ_△f²/(d−λ₂)²` is not small). Weighting by `t_ab` amplifies exactly the
loose terms. Same aggregation disaster as every prior bound: the per-edge inequality
cannot see the flatness that makes `T` small.

## TASK 4 — simpler aggregates

| bound | corpus `n≤9` | deg2+dense `n=50..1000` |
|---|---|---|
| **(a) `T ≤ λ₂fᵀDf`** | **9020/9020** | **11/11** |
| ↳ and `λ₂fᵀDf ≤ RHS`? | 9014/9020 | **0/11** |
| ↳ `[λ₂+S²/m ≤ fᵀDf]` | 9014/9020 | **0/11** |
| (b) `T ≤ λ₂fᵀQf` | 9020/9020 | 11/11 |
| (c) `T ≤ max(t)·λ₂` | 9020/9020 | 11/11 |

**The aggregate triangle-Poincaré `T ≤ λ₂fᵀDf` holds universally (100%)** — remarkably,
*even though the local Poincaré `E_{G[N(c)]}(f) ≤ λ₂ Σ_{N(c)} f²` fails on ~6% of
vertices*. The local failures wash out in the sum `Σ_c E_{N(c)} = T ≤ λ₂ Σ_c Σ_{N(c)}f² =
λ₂fᵀDf`. **But it does not close B on the binding family:** `λ₂fᵀDf ≤ RHS` requires
`λ₂+S²/m ≤ fᵀDf`, which **holds on the corpus (9014/9020) but fails on every deg2+dense
graph**. There `RHS < λ₂fᵀDf`, so `T ≤ λ₂fᵀDf` is true but too weak. (b), (c) likewise
hold but their RHS exceed the needed `RHS`. **All three close the `n≤9` corpus but break
on deg2+dense — another small-`n` mirage.**

---

## TASK 5 — the weakest closing lemma and its ingredients

**No aggregate weaker than the target closes B on the binding family.** The chain
`T ≤ λ₂fᵀDf ≤ RHS` works on the corpus but breaks on deg2+dense (where `RHS < λ₂fᵀDf`).
So the weakest sufficient lemma is the **full target itself**:

> **`T = Σ_ab t_ab(f_a−f_b)² ≤ λ₂(fᵀQf − S²/m)`**  (`fᵀQf = 2fᵀDf − λ₂`).

**Ingredients it genuinely needs (on the binding family):**
- **eigenvector equation** `Lf = λ₂f` — yes (gives the gradient identity / apex form); ✔ but insufficient alone.
- **Cauchy–Schwarz on symmetric differences** — yes for the per-edge bound, but it
  **aggregates too loosely** (TASK 3); not enough.
- **`‖f‖=1`** — implicitly (normalization of `T`, `RHS`).
- **the `−S²/m` projection term** — **essential**: the aggregate Poincaré `λ₂fᵀDf` (which
  uses no `−S²/m`) overshoots `RHS` on deg2+dense precisely by `λ₂(fᵀDf−λ₂−S²/m) > 0`. The
  condition `λ₂+S²/m ≤ fᵀDf` fails there, so the lift's `−S²/m` (and the gap between
  `fᵀQf` and `fᵀDf`) cannot be dropped.
- **minimality of `λ₂`** — **still required**: the margin is a delicate `~0.18`, and every
  bound using only `Lf=λ₂f` + C-S (gradient bound, aggregate Poincaré) is either too loose
  or too weak. The stable-but-thin margin is a Rayleigh-minimality phenomenon, consistent
  with all prior rounds.

**Note on the `+1`:** the failing condition `λ₂+S²/m ≤ fᵀDf` is exactly `R″ ≥ 0` *without*
its `+1` (`R″ = λ₂(fᵀDf−λ₂+1−S²/m)`). The min-degree relaxation's `+1` is what let `R″≥0`
survive on deg2+dense while the no-`+1` Poincaré route fails — but that `+1` is also what
made B2′ asymptotically tight. The two routes trade the same slack oppositely.

---

## Synthesis

- **The Dirichlet route is the right frame** (sound, stable margin 0.18, exact apex form),
  and it yields one genuinely clean, scale-stable, provable-looking lemma: **the aggregate
  triangle-Poincaré `T ≤ λ₂fᵀDf`** (holds 100%, repairs the 6% local-Poincaré failure by
  summation).
- **But no elementary bound closes B on deg2+dense:** the per-edge gradient bound
  aggregates catastrophically (TASK 3), and `λ₂fᵀDf` overshoots the lift `RHS` there
  (TASK 4). The `−S²/m` term and `λ₂`-minimality are unavoidable.
- **Recommended next step:** prove the clean aggregate `T ≤ λ₂fᵀDf` in Lean (it needs only
  the apex identity + a *global* — not local — Poincaré, and holds universally), as a
  second banked lemma alongside hub-flatness; then attack the residual gap
  `RHS − λ₂fᵀDf = λ₂(fᵀDf − λ₂ − S²/m)` (negative on deg2+dense) — which is where the real
  difficulty, and the minimality, lives.

### Caveats
`λ₂`, `f` numerical. TASK 0 on 4 named/random graphs; TASK 1/4 corpus (9020) + deg2+dense
to `n=1000`; TASK 2/3 corpus (199 523 edges) + deg2+dense to `n=500`. `T≤RHS`, apex
identity, gradient bound, and aggregate Poincaré are exact-checked; the `T_bound` blow-up
and the `λ₂fᵀDf>RHS` failure are the substantive negatives. B holds throughout
(margin ≥ 0.18 on the binding family).
