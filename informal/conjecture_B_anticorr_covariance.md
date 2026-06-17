# Conjecture B — anti-correlation as covariance / rearrangement bound

Over edges `e`: `t_e=(A²)_ab`, `g_e=(f_a−f_b)²`, `T=Σ t_e g_e`, `G=Σ g_e=λ₂`, `Tau=Σ t_e`.
Chebyshev's sum inequality (oppositely-sorted ⇒) gives `T ≤ (Tau/|E|)·G`. Code:
[`conjecture_B_anticorr_covariance.py`](../conjecture_B_anticorr_covariance.py).

**Headline.** The anti-correlation is **universal as a covariance**: `cov(t,g) ≤ 0` on
**100%** of 613 graphs (corr −0.21…−1.0), so the Chebyshev bound `T ≤ (Tau/|E|)·λ₂` holds
(612/613). **But it does not close B:** the intermediate `(Tau/|E|)·λ₂` **overshoots RHS on
the dense graphs** (fails 32/613, worst **40×**). Chebyshev uses only the *sign* of the
anti-correlation (anti-sorting), not its *magnitude* — and the magnitude (high-`t` edges
have `g ≪ mean-g`) is exactly what makes `T` small but is invisible to rearrangement. No
threshold split or hard separator closes B either.

---

## TASK 1 — covariance diagnostics (family medians)

| family | # | `corr(t,g)` | `T/((Tau/\|E\|)·λ₂)` | `T/RHS` | `Def/Req` | `cov≤0` |
|---|---|---|---|---|---|---|
| corpus | 600 | −0.61 | 0.78 | 0.46 | (Req≤0) | **100%** |
| deg2+dense | 3 | −0.21 | **0.04** | 0.77 | 1.91 | 100% |
| lollipop | 4 | −0.86 | 0.007 | 0.06 | 3.41 | 100% |
| circulant | 2 | −0.61 | 0.81 | 0.18 | (Req≤0) | 100% |
| ER / WS | 3 | −0.3 | 0.5–0.8 | 0.1–0.4 | (Req≤0) | 100% |
| chain | 1 | **−1.00** | 0.06 | 0.03 | (Req≤0) | 100% |

`cov(t,g) ≤ 0` everywhere, so `T ≤ (Tau/|E|)·λ₂` (Chebyshev) always holds. On dense
deg2+dense the ratio is `0.04` (T is *far* below the mean-product bound), reflecting strong
anti-correlation.

## TASK 2 — quantile overlap (high-`t` ∩ high-`g`)

| family | q90 overlap-mass / T | q95 / q99 |
|---|---|---|
| deg2+dense (n=200) | 0.004 | **0 / 0** |
| circulant, ER | 0 | 0 |
| lollipop | 1.0* | — |

High-`t` ∩ high-`g` is **empty at q95+** (deg2+dense: 16 edges / 0.4% at q90, 0 above). So
the strongest edges of each type don't overlap. (*lollipop's "1.0" is degenerate: `T` lives
on a couple of edges, and the q90 thresholds collapse — not a real overlap.) The overlap is
*small but nonzero* at q90 — the anti-correlation is statistical, not a perfect partition.

## TASK 3 — candidate global inequalities

| candidate | valid (upper bound)? | closes (`≤ RHS`)? |
|---|---|---|
| **(i) Chebyshev `T ≤ (Tau/\|E\|)·λ₂`** | **612/613** (`cov≤0`) | `(Tau/\|E\|)·λ₂ ≤ RHS`: **581/613**; worst **40×** |
| (ii) threshold split `τ·λ₂ + g_hi·Tau` | (valid where checked) | **362/613** |

- **(i)** is valid (the anti-correlation guarantees it) but the bound `(Tau/|E|)·λ₂`
  **overshoots RHS on the 32 dense graphs** (deg2+dense, dense corpus), by up to **40×**.
  Reason: `(Tau/|E|)` is the *mean* triangle count, which is large on dense graphs, while
  the actual `T` is small only because the high-`t` edges carry tiny `g`. Chebyshev replaces
  every `g_e` by the global mean `λ₂/|E|`, discarding exactly that.
- **(ii)** the threshold split is weaker (closes 59%).

**No global rearrangement bound closes B.**

## TASK 4 — structural separator (no clean rule)

| family | high-`t` edges: max `g` | high-`g` edges: max `t` |
|---|---|---|
| deg2+dense | 2.3×10⁻⁴ (g-q90 = 2.8×10⁻⁷) | **52** (t-q90 = 47) |
| lollipop | 1.2×10⁻⁵ | 33 |
| circulant | 9.3×10⁻⁴ | 1.5 |
| ER | 1.9×10⁻² | 16.5 |

Neither implication is a hard rule: a high-`g` edge can have `t = 52` (near-max) on
deg2+dense, and high-`t` edges can have `g` above the 90th percentile. So "`t` large ⇒ `g`
small" and "`g` large ⇒ `t` small" hold only *on average* (cov<0), not as a threshold
separator. The exceptions are the **bottleneck-adjacent dense edges** (some triangles *and*
some gradient), which is exactly where the per-edge gradient bound is unequal-degree and
fails.

---

## Synthesis — covariance route confirms the anti-correlation but cannot close B

- **`cov(t,g) ≤ 0` is a genuine universal invariant** (100%/613) — the cleanest statement
  of why `T` is small, and it makes Chebyshev `T ≤ (Tau/|E|)·λ₂` rigorous.
- **But rearrangement is too weak**: it captures only the *sign* of the anti-correlation.
  On dense graphs the mean triangle count `Tau/|E|` is large, so `(Tau/|E|)·λ₂` blows past
  `RHS` (40×), even though the true `T` is tiny. To close B one must use the *magnitude* —
  that high-`t` edges have `g ≈ 0` — which is the per-edge gradient/hub-flatness bound, and
  that bound is invalid on the unequal-degree bottleneck edges (prior round).
- **No hard separator** `t≥τ ⇒ g≤b` exists; the anti-correlation is statistical, with
  bottleneck-adjacent edges as exceptions.

This closes the covariance/rearrangement family. Combined with the failures of the per-apex
spectral, the hybrid gradient, and the carrier mechanisms, the picture is now complete and
consistent: **every bound that factors through edge/apex-local quantities or through the
sign-only anti-correlation is either invalid on bottleneck edges or too loose on dense
edges.** The only invariants that survive universally are the *global* ones —
`cov(t,g)≤0`, `Deficit ≥ Required` (margin ≥ 1.7), and the `sign(Required)` regime split —
none of which has yet been converted into a closed-form proof of the `Required > 0` regime.

### Caveats
`λ₂`, `f` numerical. 613 graphs (corpus n≤9 + deg2+dense to n=200 + lollipop/circulant/
ER/WS/chain). `cov≤0` exact-checked (612/613 valid; 1 numerical). Chebyshev validity and
the `(Tau/|E|)·λ₂ ≤ RHS` failures are exact; `T ≤ RHS` (B) holds throughout.
