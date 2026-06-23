# Conjecture B — the energy-weighted covariance route

Express the aggregate `E_μ[t_e] ≤ d_eff` (`μ(e) = g_e²/λ`, normalized, `E_μ[t] = T/λ`) via the
covariance identity. **Result: the identity `E_μ[t] = t_bar + m·Cov(t,g²)/λ` is exact; the
anti-correlation `(a) Cov(t,g²) ≤ 0` is UNIVERSAL (50/50, `= 0` at regular); but `(b) t_bar ≤ d_eff`
FAILS (26/50) — on bottleneck graphs `t_bar/d_eff` reaches 19.8. So the clean split `(a)∧(b)` does NOT
prove the aggregate; it needs the quantitative bound `Cov ≤ (λ/m)(d_eff − t_bar)`, which on bottlenecks
(`t_bar ≫ d_eff`) requires `Cov` *very* negative — the aggregate restated, not simpler. The positive
take-away: the anti-correlation never reverses.** Code:
[`conjecture_B_covariance_route.py`](../conjecture_B_covariance_route.py).

## TASK 2 — the covariance identity (exact)

With `μ(e) = g_e²/λ` (`Σμ = 1`, `λ = Σ_e g_e²`), `t_bar = (1/m)Σ t_e`, `Cov(t,g²) = (1/m)Σ t_e g_e² −
t_bar·(λ/m)`:

> **`E_μ[t] = t_bar + m·Cov(t,g²)/λ`** (verified, err `10⁻¹⁴`).

Hence `E_μ[t] ≤ d_eff ⟺ Cov(t,g²) ≤ (λ/m)(d_eff − t_bar)`.

## TASK 5 — (a) and (b) separately

| | statement | holds |
|---|---|---|
| **(a)** | `Cov(t_e, g_e²) ≤ 0` (anti-correlation) | **50/50** |
| **(b)** | `t_bar ≤ d_eff` | **26/50** |
| (a)∧(b) | | 26/50 |

> **(a) is UNIVERSAL** — `Cov(t,g²) ≤ 0` on every graph (`= 0` exactly at regular, where all `g²` equal).
> The high-triangle edges *always* carry below-average gradient energy; the anti-correlation never
> reverses. **(b) FAILS** on every bottleneck graph.

## TASK 6 — where they fail

- **(a) Cov > 0:** *none* (0 failures). Anti-correlation is universal.
- **(b) t_bar > d_eff:** all bottleneck graphs (deg2+dense, twin-port). Sample:

| graph | `t_bar` | `d_eff` | `t_bar/d_eff` | `E_μ[t]` |
|---|---|---|---|---|
| deg2+dense(80,.85) | 56.1 | 2.83 | **19.8** | 1.83 ✓ |
| twin-port `K₈₀` d4 | 77.8 | 4.32 | 18.0 | 1.81 ✓ |
| deg2+dense(80,.6) | 29.0 | 2.61 | 11.1 | 1.60 ✓ |

> The dense core makes `t_bar` huge, while the localized Fiedler makes `d_eff` tiny — so `t_bar ≫ d_eff`.
> Yet the aggregate holds (`E_μ[t] ≈ 1.8 ≤ d_eff ≈ 2.8`): the μ-weight concentrates on the *low-t*
> bottleneck edges, pulling the weighted mean far below `t_bar`. The anti-correlation magnitude (not just
> sign) does all the work.

## TASK 3 — the quantitative covariance bound

`Cov ≤ (λ/m)(d_eff − t_bar)`. When `t_bar > d_eff` (bottleneck), the RHS is **negative**, so the bound
demands `Cov` sufficiently negative — strictly stronger than `(a) Cov ≤ 0`. On `K_n`: `Cov = 0`, RHS `=
(λ/m)·1 = 4/n → 0⁺`, holds tightly. On gnp: `Cov ≈ −0.11`, RHS `≈ +0.14` (`d_eff > t_bar`), holds with
room. The bound is the aggregate verbatim — not a simplification.

## TASK 4 — why the clean split is not enough

`E_μ[t] = t_bar + m·Cov/λ ≤ t_bar` (from (a)) `≤ d_eff` (from (b)) would prove it — **but (b) is false**.
On bottleneck graphs `t_bar ≫ d_eff`, so `E_μ[t] ≤ t_bar` is useless; the aggregate holds only because
`m·Cov/λ` is *very* negative (`E_μ[t] = 56 + (huge negative) = 1.8`). The proof must quantify the
anti-correlation, which is the eigenspace/block-flatness content (`aggregate_triangle_slack_global.md`,
`aggregate_typeA_scalar.md`).

## The universal sub-fact (a)

`Cov(t,g²) ≤ 0 ⟺ m·Σ_e t_e g_e² ≤ (Σ_e t_e)(Σ_e g_e²)` — a **Chebyshev-type** inequality. It holds 50/50
but is NOT a pure sorting inequality (it needs the *Fiedler* anti-correlation: the eigenvector is flat on
dense/high-triangle regions). So even (a), while universal, is spectral — its proof is the same
mechanism as the aggregate, just qualitative (sign) rather than quantitative (magnitude).

## Conclusion

- **Identity exact:** `E_μ[t] = t_bar + m·Cov(t,g²)/λ`.
- **(a) `Cov(t,g²) ≤ 0` UNIVERSAL** (50/50, `=0` at regular) — the anti-correlation never reverses; a
  clean true sub-fact (`m·Σ t g² ≤ (Σt)(Σg²)`, Chebyshev-type but Fiedler-driven).
- **(b) `t_bar ≤ d_eff` FAILS** (26/50; `t_bar/d_eff` up to 19.8 on bottlenecks).
- **The clean split fails;** the aggregate needs the quantitative `Cov ≤ (λ/m)(d_eff − t_bar)` (very
  negative on bottlenecks) = the aggregate restated. The anti-correlation *magnitude* is the irreducible
  content.

## Lean
No code change: (a) alone does not close the aggregate (b fails on bottlenecks), and (a) itself is a
spectral sub-conjecture (not a sorting inequality). The aggregate remains the direct sorry
(`aggregate_triangle_poincare`); this round identifies the universal anti-correlation (`Cov ≤ 0`) as the
qualitative mechanism, with the magnitude (eigenspace-PSD / block flatness) the open quantitative core.
3 sorrys unchanged.
