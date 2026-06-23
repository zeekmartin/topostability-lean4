# Block resolvent Lean formalization — STOPPED at TASK 1 (false premise caught)

Attempt to formalize the block resolvent bound to close `typeA_slack_ge_required` (line 1034). **Result:
the mandatory TASK 1 Python verification CAUGHT A FALSE PREMISE — the identity `‖s‖² = D_port` (asserted
in commit `c34041c`) holds only 8/17, not 17/17. Per the explicit "if any graph fails, STOP" constraint,
the Lean formalization was halted: `source_norm_eq_Dport` would formalize a false statement. The
underlying closure is still valid — `D_core ≤ λ_max(M_∂∂)·‖s‖²` with the ACTUAL source norm `‖s‖²` closes
`hcond` 17/17 (0.952) — but it must use `‖s‖²` as its own quantity, NOT `D_port`. No Lean change; build
stays green at 3 sorrys.** Verification: [`verify_block_resolvent.py`](../verify_block_resolvent.py).

## TASK 1 — verification (the 4 checks)

| check | result | note |
|---|---|---|
| **(a) `‖s‖² = D_port`** | **8/17 ✗** (max err 0.66) | **FALSE in general** — see below |
| (b) `D_core = sᵀM_∂∂ s` exact | **17/17 ✓** (err 6·10⁻¹⁷) | resolvent identity correct (`M = RL_HR`) |
| (c) `λ_max(M_∂∂)·D_port ≥ D_core` | 8/17 ✗ (min slack −0.02) | fails *because* (a) fails |
| (d) `2[(δ−1)D_port + maxt·λ_max(M_∂∂)·‖s‖²] ≤ RHS` | **17/17 ✓** (max 0.952) | closure with the **actual `‖s‖²`** |

### Why (a) is false

`source_v = Σ_{u∼v, u∈P}f_u − d_v^P·f_v` (port boundary). For deg2dense (single port `p`, `|∂|=2`, each
boundary vertex has ONE port neighbour): `source_v = f_p − f_v`, so
`‖s‖² = Σ_∂(f_p−f_v)² = D_port` ✓. But for **twin-port**, a core vertex `w` can be adjacent to TWO ports
`a,b`: then `source_w = f_a + f_b − 2f_w`, contributing `(f_a+f_b−2f_w)²`, whereas `D_port` contributes
`(f_a−f_w)² + (f_b−f_w)²` — **unequal** unless `f_a = f_b`. So `‖s‖² ≠ D_port` whenever a boundary vertex
has ≥ 2 port neighbours (twin with `|∂|` up to 4). **The commit-`c34041c` claim "‖s‖²=D_port exactly" was
unverified** (the print line was truncated by `tail` last round) **and is wrong.**

### What IS true

- **(b)** `D_core = sᵀ(RL_HR)s = sᵀ(RL_HR)_∂∂ s` exactly (`s` supported on `∂`; `R=(L_H−λ)⁻¹`).
- **(d)** the block bound `D_core ≤ λ_max((RL_HR)_∂∂)·‖s‖²` (valid by Cauchy interlacing) with the
  **actual `‖s‖²`** closes `hcond` 17/17 (margin 0.952). **Case 2A remains mathematically closed** — the
  fix to the prior round is only that the bound must carry `‖s‖²` (source norm), not `D_port`.

## TASK 2–4 — STOPPED (per constraint)

- **TASK 2 `source_norm_eq_Dport`:** would formalize the FALSE identity (a). **Not attempted.** The
  correct quantity is the source norm `‖s‖² = Σ_{v∈H}(Σ_{u∼v,u∈P}f_u − d_v^P f_v)²` — a different object
  from `D_port`.
- **TASK 3 `dcore_le_block_resolvent`:** still valid mathematically (`D_core ≤ λ_max(M_∂∂)·‖s‖²`), but its
  statement needs the resolvent operator `M = (L_H−λ)⁻¹L_H(L_H−λ)⁻¹` and the eigenvalue of its `∂`-block —
  Mathlib's matrix-inverse + submatrix-eigenvalue API is not available in usable form (no `(L_H−λ)⁻¹`
  spectral reasoning, no Cauchy interlacing lemma applied to a graph Laplacian block). **Not attempted**
  (also blocked by the TASK 1 failure).
- **TASK 4:** the existing sorry-free bridge `triEnergy_le_of_partition` (line 981) expects
  `hcond : Cp·D_port + Cc·D_core ≤ B`. The block bound supplies `D_core ≤ λ_max(M_∂∂)·‖s‖²`, so the
  *missing* intermediate lemmas (exact Lean types) are:

```lean
-- (1) source norm as a graph quantity (NOT D_port):
def sourceNormSq (f : V → ℝ) (P : V → Prop) : ℝ :=
  ∑ v : V, (if P v then 0 else
    ((∑ u ∈ G.neighborFinset v, if P u then f u else 0)
       - (∑ u ∈ G.neighborFinset v, if P u then (1:ℝ) else 0) * f v) ^ 2)

-- (2) block resolvent bound (needs (L_core - λ)⁻¹ + ∂-block eigenvalue):
lemma dcore_le_block_resolvent (f : V → ℝ) (lam mu : ℝ) (P : V → Prop) (hμ : mu = blockResolventMax …) :
    Dcore G f P ≤ mu * sourceNormSq G f P   -- mu = λ_max((L_core-λ)⁻¹ L_core (L_core-λ)⁻¹)_∂∂

-- (3) the closed scalar (replaces the false ‖s‖²=D_port route):
lemma hcond_from_block (…) :
    (δ-1) * Dport G f P + maxtCore * (mu * sourceNormSq G f P) ≤ RHS …
```

Item (2) is the blocker: it requires matrix-inverse spectral theory (resolvent of a graph-Laplacian
sub-block, plus Cauchy interlacing) absent from Mathlib in usable form.

## TASK 5 — report

- **(a) sorry-free lemmas added:** NONE (formalization halted at TASK 1 false premise; no Lean change).
- **(b) `typeA_slack_ge_required` (line 1034):** still **SORRY** (unchanged).
- **(c) remaining gaps (exact Lean types):** the three signatures above — `sourceNormSq` (definable now),
  `dcore_le_block_resolvent` (blocked: needs `(L_core−λ)⁻¹` spectral API + Cauchy interlacing), and the
  scalar assembly. The prior `source_norm_eq_Dport` target is **withdrawn** (false).
- **(d) build status:** **GREEN** (no Lean change; 3 sorrys: `aggregate_triangle_poincare` 854,
  `typeA_slack_ge_required` 1034, `conjectureB` chain 1117).

## Conclusion / correction

- **The verification did its job:** it caught that `‖s‖² = D_port` (commit `c34041c`) is FALSE (8/17) —
  true only when every boundary vertex has a single port neighbour (deg2dense), false for twin.
- **Case 2A is still mathematically closed** via `D_core ≤ λ_max(M_∂∂)·‖s‖²` with the *actual* source
  norm `‖s‖²` (closure 17/17, 0.952) — the correction is `‖s‖²`, not `D_port`.
- **Lean is blocked** at the resolvent-block eigenvalue (matrix-inverse spectral API). The honest path
  forward is either (i) build the `(L_core−λ)⁻¹` block-eigenvalue + Cauchy-interlacing API in Mathlib, or
  (ii) find a `D_core` bound expressible without the matrix inverse.
- **No Lean change; build green; `typeA_slack_ge_required` stays sorry.**
