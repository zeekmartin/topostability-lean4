# Conjecture B — local envelope and entropic routes to the anti-correlation magnitude

Two orthogonal attacks on the *magnitude* of `Cov(t_e, g_e²) ≤ 0` (needed for the aggregate, since the
sign alone is insufficient). **Result: BOTH FAIL. PART A (local envelope `g² ≤ C/(t+1)^α`) is too loose
by 47–30000× — the envelope constant is set by the bottleneck edge and over-counts the flat interior.
PART B (entropy / Chernoff / Pinsker / transport) is direction-misaligned — these tools bound
`|deviation|` from above or give upper bounds `≥ E_μ[t]`, but the aggregate needs a *large signed
negative* deviation, which divergences cannot certify.** Code:
[`conjecture_B_local_envelope_and_entropy.py`](../conjecture_B_local_envelope_and_entropy.py).

## PART A — local envelope

`g_e² ≤ C(G)/(t_e+1)^α` (exact with `C(G) = max_e g_e²(t_e+1)^α`), giving
`T ≤ C(G)·Σ_e t_e/(t_e+1)^α`. Does this beat `2λ·d_eff`?

| α | max `T_bound / (2λ·d_eff)` over corpus |
|---|---|
| 0.0 | 29937 |
| 0.5 | 5299 |
| 1.0 | 939 |
| 1.5 | 180 |
| **2.0** (best) | **47.2** |

> **The envelope is too loose by ≥ 47×** (best α=2; never `≤ 1`). The constant `C(G) = max_e g²(t+1)^α`
> is dominated by the *bottleneck* edge (`t` small, `g²` huge); applying that max to the many *flat
> interior* edges (`g² ≈ 0`) over-counts massively. Like every `max`-based bound, the envelope discards
> the `g²` *distribution* — the very thing (concentration on low-`t` edges) that makes `T` small.

## PART B — entropic / transport (direction-misaligned)

`μ(e) = g_e²/λ` (probability on edges), `t_e` the cost. We need `E_μ[t] ≤ d_eff`, i.e. `E_μ[t] = t_bar +
(deviation)` with the deviation *large negative* (on bottlenecks `t_bar ≫ d_eff`, so need
`dev ≤ d_eff − t_bar ≪ 0`).

**B1 — entropy.** `H(μ)/log m` is low where `μ` concentrates (deg2+dense: 0.10; gnp: 0.73; `K_n`: 0.7–0.8).
Confirms `μ` is far from uniform, but a low entropy does not bound `E_μ[t]` (a concentrated `μ` could
concentrate on high-`t` *or* low-`t` edges — entropy is direction-blind).

**B2 — Chernoff.** `inf_{s>0} log M(s)/s = E_μ[t]` *exactly* (verified: `K₃₀` 28.0 = `E_μ[t]`; gnp 7.70 ≈
7.69). Since `log M(s)/s ≥ E_μ[t]` (Jensen) with infimum `E_μ[t]` as `s→0`, **Chernoff cannot beat
`E_μ[t]`** — it gives `E_μ[t] ≤ E_μ[t]`, no certificate that `E_μ[t] ≤ d_eff`.

**B4 — Pinsker.** `KL(μ‖unif)` is large, and `|dev| ≤ t_max·√(KL/2)` *upper-bounds* `|dev|`:

| graph | actual `dev` | Pinsker `|dev|` bound | need `dev ≤` |
|---|---|---|---|
| deg2+dense(80,.9) | −60.9 | **133.9** | −59.9 |
| deg2+dense(60,.9) | −44.5 | 100.8 | −43.5 |
| twin-port `K₅₀` d3 | −45.8 | 79.4 | −43.2 |

> **Pinsker is the wrong direction.** It says `dev ∈ [−134, +134]` — it *limits* how far `μ` deviates,
> but the aggregate *needs* `dev ≤ −59.9` (`μ` to deviate a LOT, in the anti-correlation direction).
> Bounding `|dev|` from above cannot certify `dev` is sufficiently negative. The KL/transport distance is
> direction-agnostic; it measures *how far* `μ` is from uniform, not *which way*. The anti-correlation
> *structure* (interior flat) is exactly what divergences discard.

**B3 — transport.** Same obstruction: `W₁(μ, unif)` (or TV) measures the *size* of the reweighting, not
its alignment with `t`. A Kantorovich bound gives `|E_μ[t] − t_bar| ≤ Lip(t)·W₁`, again an *upper* bound
on `|dev|` — useless for forcing `E_μ[t]` small.

## Why both fail (unified)

The aggregate needs `E_μ[t]` *small* = the deviation *large in a specific direction*. PART A (envelope,
`max`-based) and PART B (divergence, direction-agnostic) both discard the **joint structure** of `t` and
`g²` — that `g²` concentrates *precisely on the low-`t` edges*. Only a tool that uses the *pairing*
(`Σ t_e g²` with the actual eigenvector) can see it — i.e. the weighted/eigenspace form
`λD − L_t ⪰ 0 on E_{λ₂}` (`aggregate_triangle_slack_global.md`). Coarse-graining (max, entropy,
divergence) provably loses it.

## Conclusion

- **PART A (local envelope): FAILS** — too loose by ≥ 47× (best α=2); `max`-constant over-counts the flat
  interior.
- **PART B (entropy/Chernoff/Pinsker/transport): FAILS** — direction-misaligned; Chernoff `inf = E_μ[t]`,
  Pinsker/transport bound `|dev|` from above while the aggregate needs `dev` large-negative.
- **Unified reason:** both discard the `t`–`g²` *pairing* (the anti-correlation structure). The magnitude
  lives only in the exact weighted/eigenspace form.

## Lean
No code change: neither route yields a usable bound. `aggregate_triangle_poincare` stays the direct sorry;
the only sufficient form remains `λD − L_t ⪰ 0 on E_{λ₂}` (eigenspace-PSD). 3 sorrys unchanged.
