# Conjecture B — the three-regime proof chain and the first missing lemma in each

Conjecture B (`λ₂(T(G)) ≤ λ₂(G)`) reduces (via the projected Fiedler lift, `conjectureB_lift`) to the
**lift inequality** `T ≤ RHS`, `RHS = λ₂(fᵀQf − S²/m) = λ₂(2fᵀDf − λ₂ − S²/m)`, `T` the triangle
energy, `f` the unit Fiedler. The regime split is on `Required = λ₂(λ₂ + S²/m − fᵀDf)`. Code:
[`conjecture_B_three_regimes_chain.py`](../conjecture_B_three_regimes_chain.py), 580 graphs.

**Coverage (reconfirmed, 0 exceptions):** Regime 1 `277` + TYPE A `226` + TYPE B `77` = `580/580`;
`boundary_ratio` is **bimodal** (nothing in `(1,2]`). `T ≤ RHS` and `B2′ ≤ λ₂G` hold `580/580`.

Shared first step (all regimes): `T ≤ B2′ := Σ_e(min(d_a,d_b)−1)g_e²`, since `t_e ≤ min(d_a,d_b)−1`.
**Now formalised:** `triCount_le_min_degree_sub_one` (`|N(i)∩N(j)| ≤ min(d_i,d_j)−1`), sorry-free.

---

## REGIME 1 — `Required ≤ 0` (277 graphs)

**Chain:**
1. `T ≤ B2′` — **Lean ✓** (`triCount_le_min_degree_sub_one`, summed).
2. `B2′ ≤ λ₂G` — **MISSING** (the triangle-free degree inequality).
3. `λ₂G = RHS` — definition ✓.
4. `RHS ≥ λ₂fᵀDf` (since `Required ≤ 0 ⇒ fᵀDf ≥ λ₂+S²/m`) — algebra, in `conjectureB_lift` ✓.

**Two routes to step 2 in this regime:**
- **(a) aggregate Poincaré** `T ≤ λ₂fᵀDf` (then `≤ RHS` by step 4). Holds **277/277**. This is the
  existing sorry `aggregate_triangle_poincare`, *proved for regular* (`aggregate_triangle_poincare_regular`).
- **(b) S-procedure** `M + α(L−λ₂I) ⪰ 0` on `1⊥` with `α = Δ+λ₂−1` (`M = λ₂(D+A) − (λ₂/m)ddᵀ −
  L_min`, `gap = fᵀMf = λ₂G − B2′`). Holds **276/277** (one marginal failure; `α* ≤ 1.05(Δ+λ₂−1)`,
  `α*` min 1.4, median 6.7, max 78).

**First missing lemma (Regime 1):** `aggregate_triangle_poincare` restricted to `Required ≤ 0`, i.e.
**`T ≤ λ₂·fᵀDf`** (holds 277/277). Candidate certificate: `M + (Δ+λ₂−1)(L−λ₂I) ⪰ 0` on `1⊥` (276/277
— *not quite* universal, so the clean target is the aggregate-Poincaré form (a)).

## REGIME 2A — `Required > 0`, `boundary_ratio < 1` (TYPE A, vertex bottleneck, 226 graphs)

`B = V ∖ carrier` (carrier `C₈₀` = top-`f²` vertices holding 80% mass); `g = Fiedler(G[B])` extended
by 0. **Chain (Paper16):**
1. `gᵀL_G g = blockEnergy + boundaryEnergy` — **Lean ✓** (`lapQuadForm_edge_split`).
2. `λ₂(G)·‖g‖² ≤ blockEnergy + boundaryEnergy` — **Lean ✓** (`block_gap_lower`).
3. `blockEnergy = 2·λ₂(G[B])·‖g‖²` — **Lean ✓** (`block_fiedler_energy`, modulo the `G[B]`-Fiedler
   row equation as hypothesis).
   ⟹ `λ₂(G[B]) ≥ λ₂(G) − boundaryEnergy/‖g‖² = (1 − boundary_ratio)·λ₂(G)`. With `boundary_ratio < 1`
   this is `> 0` — **the block gap, certified** (`boundary_ratio` median `0.004`, max `0.671` here).
4. resolvent / Poincaré on the block ⟹ `f|_B ≈ uniform` — **Lean ✓** (`poincare_on_block`).
5. **`f|_B` uniform + block gap ⟹ `T ≤ RHS`.** — **MISSING.**

**First missing lemma (TYPE A) = Step 5.** It is *not* yet a Lean statement and is the genuine gap.
Its content: the block gap (a statement about the **subgraph spectrum** `λ₂(G[B])`) must be converted
into a bound on the **triangle energy** `T`. Concretely the missing inequality is

> with `f` flat on `B` (`Σ_{a,b∈B}(f_a−f_b)²` controlled by `poincare_on_block`) and the carrier of
> `O(1)` size, **`T = Σ_e t_e(f_a−f_b)² ≤ RHS`** — because the triangle energy is carried by edges
> incident to the small carrier (where `f` varies), and the block gap bounds that contribution.

Empirically TYPE A has `T/RHS`: min `0.14`, median `0.59`, **max `0.83`** — comfortable, but Step 5
has no crisp formal statement yet (the link block-gap → triangle-energy bound is unformalised).

## REGIME 2B — `Required > 0`, `boundary_ratio > 2` (TYPE B, path bottleneck, 77 graphs)

**Chain:**
1. the block (clique) is uniform under the resolvent — **Lean ✓** (`poincare_on_block`).
2. `T` comes only from block-internal edges — combinatorial, **partial** (apex identity in `Paper15`).
3. **block edges have gradient `≈ 0` ⟹ `T = O(λ₂²)`** — **MISSING in general** (proved only for
   *lollipops* via the apex identity + clique uniformity; not for general TYPE B).
4. `RHS = Θ(λ₂)` ⟹ `T/RHS → 0` — algebra.

**First missing lemma (TYPE B) = Step 3:** **`T = O(λ₂²)`** for a general path-bottleneck block (the
block-internal flatness bound). Currently only the lollipop special case is handled (clique
uniformity, exact). Empirically TYPE B has `T/RHS`: min `0.011`, median `0.039`, **max `0.176`** — far
below `0.5` (all 77), so the bound is very loose, but the *general* `T = O(λ₂²)` statement is not
formalised.

## Summary table

| regime | count | chain status | first missing lemma | margin |
|---|---|---|---|---|
| 1 (`Required ≤ 0`) | 277 | steps 1,3,4 ✓ | `T ≤ λ₂fᵀDf` (= `aggregate_triangle_poincare`; regular case ✓) | `T/λ₂fDf ≤ 1`, S-proc 276/277 |
| 2A (TYPE A) | 226 | steps 1–4 ✓ (Paper16) | **Step 5**: block-gap + flat `f|_B` ⟹ `T ≤ RHS` (unformalised) | `T/RHS ≤ 0.83` |
| 2B (TYPE B) | 77 | steps 1,4 ✓; 2 partial | **Step 3**: `T = O(λ₂²)` for general path bottleneck | `T/RHS ≤ 0.18` |

## Conclusion

- **Coverage is exact and bimodal** (277 + 226 + 77 = 580, nothing in `(1,2]`): the three regimes
  partition all graphs.
- **Regime 1** is the cleanest: it reduces to `aggregate_triangle_poincare` (`T ≤ λ₂fᵀDf`, 277/277),
  whose regular case is formalised; the S-procedure `α = Δ+λ₂−1` nearly certifies it (276/277).
- **Regime 2A** has all Paper16 block lemmas (steps 1–4) sorry-free; the single missing piece is
  **Step 5** — translating the block spectral gap into the triangle-energy bound `T ≤ RHS` (no formal
  statement yet).
- **Regime 2B** needs **`T = O(λ₂²)`** for general path bottlenecks (only lollipops done).
- **Newly formalised this round:** `triCount_le_min_degree_sub_one` — the shared first step `T ≤ B2′`,
  the reduction of the triangle inequality to the triangle-free degree-only one, valid for *all*
  regimes.

## Formalised (Lean, `ConjectureB.lean` / `Paper16.lean`, no `sorry`)
- `triCount_le_min_degree_sub_one` (**new**) — `|N(i)∩N(j)| ≤ min(d_i,d_j)−1` for `i∼j`.
- `aggregate_triangle_poincare_regular`, `B2prime_min_decomp`, `quadForm_*`, `degAssort_covariance`,
  `lagrange_identity`, `lapMatrix_*` (this file); `poincare_on_block`, `block_gap_lower`,
  `block_fiedler_energy`, `quadform_edge_split`, `lapQuadForm_edge_split` (Paper16).
- **Three remaining `sorry`s** = exactly the three first-missing-lemmas above
  (`aggregate_triangle_poincare`, `conjectureB_regime_two`, and the top-level `conjectureB`).
