# Combining the two λ₂(G) lower bounds  τ/(Δ−1)  and  λ₂(T(G))

Conjectures A (`τ/(Δ−1) ≤ λ₂(G)`) and B (`λ₂(T(G)) ≤ λ₂(G)`) each hold but do not chain (see [`hierarchy_validation.md`](hierarchy_validation.md)). Here we ask whether *combining* the two quantities gives a stronger bound or a better predictor of `λ₂(G)`, over the **45196 graphs** with `T(G)` connected and `Δ ≥ 2`.

## 1 & 3. Combined lower bounds

| Candidate `LHS ≤ λ₂(G)` | Violations | Holds? | Tightest ratio LHS/λ₂(G) | Worst slack |
|---|---|---|---|---|
| `max(τ/(Δ-1), λ₂(T(G)))` | 0 | ✅ | 1.0000 | -0.0000 |
| `τ/(Δ-1) + λ₂(T(G))` | 1491 | ❌ | — | -1.0000 |
| `(τ/(Δ-1) + λ₂(T(G)))/2` | 0 | ✅ | 0.6250 | +0.4935 |

- **`max(·,·)`** is the strongest bound that is *guaranteed* to hold: it is the pointwise max of two quantities each `≤ λ₂(G)`, so 0 violations is automatic. Its tightest ratio is the better (larger) of A's and B's individual tightness — driven to **1.0** by regular graphs where `λ₂(T(G)) = λ₂(G)`. So `max` recovers `λ₂(G)` exactly on the regular case but adds nothing beyond `λ₂(T(G))` there.
- **The sum** overshoots (both terms are positive and each can approach `λ₂(G)`), so it is not a valid lower bound.
- **The average** is guaranteed valid (mean of two values `≤ λ₂(G)`), but is looser than `max`.

## 2. Linear regression  λ₂(G) ~ a·(τ/(Δ−1)) + b·λ₂(T(G))

- **Two-variable model:** `λ₂(G) ≈ +2.1051 -1.4536·(τ/(Δ−1)) +1.0267·λ₂(T(G))`,  **R² = 0.9294**.
- Single-variable `λ₂(G) ~ τ/(Δ−1)`:  slope a = +6.2717, intercept +1.5060,  **R² = 0.7848**.
- Single-variable `λ₂(G) ~ λ₂(T(G))`: slope b = +0.8545, intercept +1.9398,  **R² = 0.9249**.
- The pair improves on the best single predictor (`λ₂(T(G))`, R²=0.9249) by **ΔR² = +0.0046**.

## 4. Variance decomposition (commonality analysis)

- `τ/(Δ−1)` alone explains  **78.48%** of the variance of `λ₂(G)`.
- `λ₂(T(G))` alone explains **92.49%**.
- The **pair together** explains **92.94%**.
- **Unique** to `τ/(Δ−1)` (semipartial): 0.46%.
- **Unique** to `λ₂(T(G))`:             14.47%.
- **Shared** (common) variance:          78.02%.

- **Significant unique variance?**  `τ/(Δ−1)`: negligible (0.46%);  `λ₂(T(G))`: YES (14.47%).
  `λ₂(T(G))` dominates; `τ/(Δ−1)` adds little unique signal once `λ₂(T(G))` is known.

## Bottom line

- **`max(τ/(Δ−1), λ₂(T(G)))` is the bound to use.** It is valid (0 violations) and pointwise dominates *both* individual bounds: it is strictly tighter than `λ₂(T(G))` on the **421** graphs where the link fails (`τ/(Δ−1) > λ₂(T(G))`), and tighter than `τ/(Δ−1)` everywhere else.
- **But the gain is small on average.** Regression/commonality say `λ₂(T(G))` already captures ~92% of `λ₂(G)`'s variance and `τ/(Δ−1)` adds only ~0.5% unique — the two are ~78% redundant, and the two-variable fit even gives `τ/(Δ−1)` a negative weight (suppression). These views are consistent: `max` helps *pointwise on a small minority* of graphs, while variance is an *average* over all graphs.
- **Research implication:** if both A and B get proved, `λ₂(G) ≥ max(τ/(Δ−1), λ₂(T(G)))` is the combined corollary — but the real prize is **λ₂(T(G)) itself** (Conjecture B), which is the dominant, near-exact predictor. `τ/(Δ−1)` is a cheap, weaker fallback that matters only when `T(G)`'s own gap is unusually small.

## Caveats

- Over the 45196 graphs with `T(G)` connected and `Δ ≥ 2` (n≤7 exhaustive, n=8,9 sampled).
- OLS R² with intercept; `λ₂` computed numerically. Empirical, not proofs.

