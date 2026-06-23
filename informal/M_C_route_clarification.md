# Clarification: what the "`M_C + L` route" is — a ruled-out prior attempt

**Date:** 2026-06-23 · topostability-lean4 · report only, no Lean changes, no new proof attempts.

This note answers a query about the "`M_C + L` route" phrase used in
`informal/bottleneck_slack_anatomy.md`. **References exist** — `M_C + L` is a *prior,
tested, doubly-failed* route, **not** a new or viable one. Two of my own earlier notes
loosely called it "the route" to prove the aggregate; that was misleading and is corrected
below.

## TASK 1 — search results (references DO exist)

`M_C` / `M_C+L` / signed-cancellation / covariance appear in:

| file | role |
|------|------|
| `Topostability/ConjectureB.lean` (lines 845–853, 217–249, 325–329) | docstring: `M_C+L` cited as a **failed** general quadratic form; covariance lemmas `degAssort_covariance`, `lapMatrix_mulVec_sq` |
| `informal/conjecture_B_signed_cancellation.md` | the **PSD/signed-SOS** test of `M_C+L` — FAILED (indefinite) |
| `informal/conjecture_B_variational_core.md` | the **Rayleigh-witness** test `φ=M_C f` — FAILED (overshoots) |
| `informal/CONJECTURE_B_STATUS.md` (line 144) | summary: `C ≥ −λ` false, `M_C+L` not PSD |
| `conjecture_B_signed_cancellation.py`, `conjecture_B_variational_core.py` | the numerics |
| `informal/bottleneck_slack_anatomy.md`, `informal/bypass_aggregate_analysis.md` | **my** notes (now corrected) |

## TASK 2 — the exact object, the inequality, the result, why abandoned

### The object `M_C`
`C` is the **degree/hub-correction term** in the aggregate (`B2′`) decomposition:

```
C = Σ_{edges, h=higher-deg endpoint} (d_h − d_l) · f_h (f_h − f_l)
  = ½⟨Ld, f²⟩ + N = ½·𝒜 + N            (𝒜 = Laplacian covariance Cov_L(d, f²))
```

It is a quadratic form `C = fᵀ M_C f` with two equivalent descriptions:

* **per-edge assembly** (`signed_cancellation.md`): for each edge with `δ = d_h − d_l`,
  `M_C[h,h] += δ`, `M_C[h,l] += −δ/2`;
* **operator form** (`variational_core.md`): `M_C = ½·diag(Ld) + ½·L_W`, where `Ld = L·d`
  and `L_W` is the degree-discrepancy Laplacian with weights `W_ab = |d_a − d_b|`.

### Test A — PSD / signed-SOS (`conjecture_B_signed_cancellation.md`)
* **Inequality tested:** `C ≥ −λ`, equivalently `M_C + L ⪰ 0` on `1⊥` (`λ = fᵀLf`).
  This would have certified the leaf `B2′ ≤ 2λ·degQuad`.
* **Result: FAILED, two ways.**
  1. `M_C + L` is **indefinite** — min eigenvalue **−0.131** on `deg2d80_0.1` (positive on
     gnp and `K₂₀`, which is why an early random-`f` test on gnp falsely suggested PSD).
     So there is **no graph-independent signed-SOS**.
  2. **Critically, the target is itself FALSE:** `C/λ` dips to **−1.067** (`deg2d140_0.05`),
     so `C ≥ −λ` fails, and hence `B2′ ≤ 2λ·degQuad` is FALSE (`B2′/2λ·degQuad = 1.05`
     while the *true* `T/2λ·degQuad = 0.008`). The unsound Lean leaf was reverted to the
     direct sorry on the true aggregate `T ≤ 2λ·degQuad`.

### Test B — Rayleigh witness (`conjecture_B_variational_core.md`)
* **Inequality tested:** write `gap = Q(φ) + (manifest nonneg)` with `Q(φ)=φᵀ(L−λ₂I)φ ≥ 0`
  (Rayleigh minimality) for the natural witness `φ = M_C f` (and relatives `L_W f`, `Df`,
  `√D·f`).
* **Result: FAILED.** `φ=M_C f` gives `rem ≥ 0` on only **20/566** graphs; `Q(M_C f) ~ n³`
  **overshoots** the vanishing `gap ~ n^{−0.9}` by `O(n³)`. Even the best-matched `√D·f`
  overshoots (`Q→1.9` while `gap→0`). The true witness `φ*` is `gap`-dependent (circular),
  not a fixed polynomial in `(d, f, λ₂)`.

### Why abandoned
Both directions are dead: `M_C + L` is indefinite **and** the inequality it was built for
(`C ≥ −λ` / `B2′`) is false and strictly looser than the real target. The lesson the repo
draws (`ConjectureB.lean:852`): *"the eigenvector equation is essential"* — no fixed
quadratic form reproduces the slack.

## TASK 3 — n/a (references exist).

## TASK 4 — is it a genuinely new route?  **NO.**

`M_C + L` is **not** new and **not** viable. The phrase as I used it in
`bottleneck_slack_anatomy.md` ("only a global quadratic-form argument that uses `Lu=λu`
(the `M_C+L` route) can recover it") **inverts the established result**:

* `M_C + L` is a **fixed** quadratic form that does **not** use `Lu=λu`; it is **indefinite**,
  so it certifies nothing graph-independently.
* The correct takeaway is the *opposite*: because every fixed quadratic form (`M_C+L`) and
  every natural Rayleigh witness (`M_C f`, `√D·f`, …) fails, the eigenvector equation must
  be used in a **graph-dependent** way that no closed-form quadratic certificate captures.

Both notes have been corrected to say `M_C+L` is **ruled out**.

### What the anti-correlation finding adds (and what it does *not* claim)
The measured anti-correlation `corr(t_e, g_e²) < 0` (100% of bottleneck graphs, mean −0.41;
`bottleneck_slack_anatomy.md`) **explains why** the term-wise and fixed-form routes overshoot
— the slack lives in the `t_e ↔ g_e²` cancellation, which a worst-case-`t_e` bound discards.
It is a **diagnosis**, not a certificate: it does *not* by itself prove the quantitative
anti-correlation, and no numerical test here establishes a new proof path. Honest status:
**the aggregate `T ≤ 2λ·degQuad` still has no viable formal route**; the open problem is to
exploit `Lu=λu` to bound the `t_e·g_e²` cancellation, and all fixed-quadratic-form / natural
Rayleigh attempts to date are ruled out.

### If anyone revisits a quadratic-form idea, test this FIRST
Before investing in any `M(t) := (weighted triangle Laplacian) − 2λ·D + (correction)` form,
run the **generalized-eigenvalue PSD test on `1⊥` across the sparse-core `deg2dense(n,q)`,
`q ∈ {0.05, 0.08, 0.12}` corpus** (the regime that broke `M_C+L` and `B2′`). If the min
eigenvalue is negative there — as it was for `M_C+L` (−0.13) — the form is indefinite and
the route is dead before any Lean work. This is the cheapest possible falsifier and should
gate every future fixed-form attempt.
