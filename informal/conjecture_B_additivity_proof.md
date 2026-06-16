# Conjecture B — quantifying additivity: the proposed mechanism is refuted

Tests the hypothesis "B holds because the `T(G)`-Fiedler is never additive except
for `K_n`; the non-additive residual wastes energy." Decompose the unit
`T(G)`-Fiedler `ψ = ψ_add + ψ_perp`, `ψ_add = P_{U_d}ψ` (`U_d = range(Bᵀ|_{d⊥})`),
`α = ‖ψ_add‖²`. Over all **9,004 distinct** corpus graphs (`T(G)` connected). Code:
[`conjecture_B_additivity_proof.py`](../conjecture_B_additivity_proof.py).

**Verdict: the proposed mechanism is FALSE.** `K_n − e` has a **simple** `λ₂(T)`
with a **fully additive** Fiedler (`α = 1.0000`, eigenspace additivity `∈[1,1]`)
yet `ratio = λ₂(T)/λ₂(G) = (n−3)/(n−2) < 1`. So additivity does **not** distinguish
equality from inequality — there is *no* non-additive residual to "waste energy,"
and B still holds. The two candidate reductions (`ratio ≤ α` and
`R_T(ψ_add) ≤ λ₂(G)`) *do* hold 100%, but both **collapse to B itself** precisely
in the tight `α=1` regime, so they do not crack the proof.

---

## 1–2. The additivity fraction α

| quantity | value |
|---|---|
| `α = ‖ψ_add‖²` | min **0.430**, median **0.966**, max 1.000 |
| graphs with `α > 0.999` (≈fully additive) | **38** (only 6 are complete) |
| graphs with `λ₂(T)` simple (`ψ` well-defined) | 8930 / 9004 |

**High additivity is generic, not special to `K_n`.** The median `α` is 0.97;
the `T(G)`-Fiedler is *mostly* additive for almost all graphs. Full additivity
(`α≈1`) holds for **38** graphs, of which only **6** (the `K_n`) are equality.

## 3. The premise refuted: `K_n − e` is additive but not equality

| graph | `λ₂(T)` mult | eigenspace additivity | ratio |
|---|---|---|---|
| `K₇−e` | 1 (simple) | [1.0000, 1.0000] | 0.800 |
| `K₉−e` | 1 (simple) | [1.0000, 1.0000] | 0.857 |
| `K₁₂−e` | 1 (simple) | [1.0000, 1.0000] | 0.900 |
| `K₁₆−e` | 1 (simple) | [1.0000, 1.0000] | 0.929 |
| `K₇` | 6 | [1.0000, 1.0000] | 1.000 |

`K_n − e` has a **simple** `λ₂(T)` whose Fiedler is **exactly additive** (`α=1`,
not a degeneracy artifact), yet `ratio < 1`. **So `α=1` does NOT imply equality.**
When `α=1`, `ψ_add = ψ` and `R_T(ψ_add) = λ₂(T)`, which for `K_n−e` is `n−3 < n−2 =
λ₂(G)`. The energy "shortfall" `λ₂(G) − λ₂(T)` is **intrinsic to the lift quotient**
of the additive Fiedler, not a non-additive residual. Premise: **wrong.**

## 4. The candidate reductions hold 100% — but collapse to B when α=1

| test | holds | note |
|---|---|---|
| **(T1)** `ratio ≤ α` | **100%** | `⇒ B` (since `α≤1`); but margin `α−ratio` median 0.60, **tight only at K_n** |
| **(T2)** `R_T(ψ_add) ≤ λ₂(G)` | **100%** | the crux; `μ ≤ R_T(ψ_add) ≤ λ₂(G) ⇒ B`; max ratio 1.0 (=K_n) |
| (T3) `μ(G) ≤ λ₂(G)` | 100% | known; median `μ/λ₂(G)=0.42` |

Both T1 and T2 are *valid* (stronger-than-B when `α<1`). **But in the tight regime
they are vacuous:** for every `α=1` graph (which includes `K_n` *and* `K_n−e`, i.e.
the equality and near-equality cases), `ratio ≤ α` is just `ratio ≤ 1 = B`, and
`R_T(ψ_add) = λ₂(T)` so `R_T(ψ_add) ≤ λ₂(G)` is just `λ₂(T) ≤ λ₂(G) = B`. They add
content only when `α<1`, i.e. **away** from the cases that matter. So neither
reduces the difficulty where it counts.

- `corr(ratio, α) = +0.49`; `mean ratio/α = 0.37` — `ratio` is typically far below
  `α` (the reduction `ratio≤α` is very loose, tight only at `K_n`).

## 5. The actual equality mechanism

Equality is governed by the **value of the lift quotient on the additive subspace**,
not by additivity:
- `μ(G) = min_{φ⊥d} φᵀL_tφ/φᵀ(D+A)φ` and `λ₂(T) ≤ μ(G) ≤ λ₂(G)`.
- For `K_n`: the (fully additive) `J(n,2)`-Fiedler achieves quotient `n = λ₂(G)`, so
  `μ = λ₂(T) = λ₂(G)` — equality.
- For `K_n − e`: the Fiedler is *also* fully additive, but its quotient is
  `λ₂(T) = n−3 < n−2 = λ₂(G)` — strict.

So `α=1` (additive Fiedler) is **necessary** for the lift to capture `λ₂(T)`
exactly, but the captured value `λ₂(T)` can still fall short of `λ₂(G)`.
**Additivity is not the discriminator; the lift-quotient value is.**

## 6. Honest proof assessment

The additivity decomposition clarifies the geometry but **does not yield a proof**:
- the proposed mechanism ("non-additive residual wastes energy") is **false**
  (`K_n−e` is additive, non-equality);
- `ratio ≤ α` and `R_T(ψ_add) ≤ λ₂(G)` hold universally but **degenerate to B** in
  the `α=1` regime that contains all the tight cases;
- the genuine open content is unchanged: *why is the additive lift quotient
  `λ₂(T) = φᵀL_tφ/φᵀ(D+A)φ < λ₂(G)` for every non-complete `G`?* — the same core
  the direct attempts reached.

What the analysis *does* establish cleanly: equality `⟺ K_n` is the **only** case
where the additive lift quotient reaches `λ₂(G)`; for all others the quotient is
strictly smaller (with `K_n−e` approaching it as `(n−3)/(n−2)→1`), and this is
**independent of additivity** (which is `1` for the whole almost-complete family).

### Caveats
- `λ₂(T)` simple for 8930/9004 (and for `K_n−e`); for degenerate `λ₂(T)` (incl.
  `K_n`) `α` is computed on the eigenspace and is `1` there too. Numerical
  (`eigvalsh`, tol 1e-7); deduped by Weisfeiler–Lehman hash; `n ≤ 9` corpus +
  explicit `K_n−e` up to `n=16`.
