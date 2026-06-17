# Conjecture B — complete classification of the `Required > 0` regime by boundary mechanism

Classify every `Required > 0` graph by `boundary_ratio = boundary_term/(‖g_B‖²·λ₂(G))`, where
`g_B` = Fiedler of `G[B]` extended by `0` on the carriers `C₈₀`. Code:
[`conjecture_B_final_classification.py`](../conjecture_B_final_classification.py). Corpus:
1296 `Required > 0` graphs.

**Headline — a clean, exhaustive two-way split.** `boundary_ratio` is **bimodal** (`< 1` or
`> 2`, *nothing in between*), and the two types are closed by two distinct mechanisms with
**100% coverage and zero exceptions**:
- **TYPE A (70.4%, `boundary_ratio < 1`, vertex bottlenecks):** Courant–Fischer gives
  `λ₂(G[B]) ≥ (1 − boundary_ratio)·λ₂(G)`, with median certified bound `0.997·λ₂(G)` — the
  block gap is proven, then Poincaré-on-block + the deg2+dense mechanism close B.
- **TYPE B (29.6%, `boundary_ratio > 2`, path bottlenecks):** `T/RHS ≤ 0.177` (median 0.024) —
  B holds directly by T-smallness, with `T` concentrated `93.7%` on the flat block-internal
  (clique) edges.

**Every `Required > 0` graph is closed by A or B (0 in neither).** One caveat: Type B's
T-smallness is driven by *block-internal flatness*, **not** by triangle-poor carriers (only
43.6% have triangle-free carrier edges) — so the "carrier edges triangle-poor" hypothesis is
only half-right.

---

## Classification by threshold

`B` holds (`T ≤ RHS`) on **100%**; max `T/RHS = 0.882`.

| `τ` | #A (`≤τ`) | #B (`>τ`) | A: actual ratio `≥ 1−τ` | B: max `T/RHS` | B: median `mean_t_carrier` |
|---|---|---|---|---|---|
| 0.25 | 892 | 404 | 100% (LB 0.75) | 0.812 | 9.27 |
| 0.50 | 910 | 386 | 100% (LB 0.50) | 0.613 | 11.80 |
| 1.00 | 913 | 383 | — | 0.177 | 11.81 |
| 2.00 | 913 | 383 | — | 0.177 | 11.81 |

**The split is bimodal and clean:** `#B` is identical (383) at `τ = 1` and `τ = 2`, so **no
graph has `boundary_ratio ∈ (1, 2]`**. Boundary ratios cluster at `< 1` (Type A) or `> 2`
(Type B) — the two mechanisms are sharply separated, not a continuum.

## TYPE A — vertex bottlenecks, closed by Courant–Fischer

`boundary_ratio < 1`: **913/1296 (70.4%)**, families deg2dense 544, degk 321, + lollipop 18,
pathend 30 (short-path cases that behave like vertex bottlenecks).

> Minimality: `λ₂(G[B]) = R_G(g_B) − boundary ≥ λ₂(G) − boundary_ratio·λ₂(G) =
> (1 − boundary_ratio)·λ₂(G)`.

- **actual ratio `≥` certified `(1 − boundary_ratio)`: 100%**, median certified LB **0.997**.
  So for the vertex-bottleneck majority the boundary term is `≈ 0`, and Courant–Fischer
  *directly proves* `λ₂(G[B]) ≳ λ₂(G)` — a positive, near-`1` block gap. Combined with the
  rigorous Poincaré-on-block bound and the deg2+dense mechanism (`Σ_B d_v f_v²` large), B is
  closed for these graphs by a clean spectral argument.

## TYPE B — path bottlenecks, closed by T-smallness

`boundary_ratio > 1`: **383/1296 (29.6%)**, families **lollipop 315, pathend 68 only** (purely
path bottlenecks — no deg2dense/degk).

| quantity | value |
|---|---|
| `T/RHS` | max **0.177**, median 0.024 (B holds 100%) |
| T decomposition | carrier-internal 0.000, boundary 0.062, **block-internal 0.937** |
| `mean_t_carrier` | `= 0` for 43.6%, `< 0.5` for 43.6%, median 11.8, max 50 |

- **`T` is tiny** (`T/RHS ≤ 0.177`), so B holds with a wide margin directly — no block-gap
  argument needed. This is the lollipop mechanism (`T = (m−1)(m−2)λ₂²u² = O(λ₂²) ≪ RHS =
  O(λ₂)`).
- **`T` lives 93.7% on block-internal (clique) edges**, where the triangle count is large but
  the Fiedler is flat (clique uniformity), so the contribution is small in absolute terms. Only
  6.2% is on the boundary, ~0% on carrier-internal edges.
- **Correction to the hypothesis:** Type B does **not** always have triangle-poor carrier
  edges — `mean_t_carrier = 0` for only 43.6% (the long-path lollipops where `C₈₀ ⊂` path,
  triangle-free), while for the rest `C₈₀` dips into the clique and `mean_t_carrier` is large
  (median 11.8). The T-smallness is therefore **not** explained by carrier triangle-poorness;
  it is explained by **block-internal flatness** (the clique part of `f` is uniform), which
  holds regardless of where the carriers sit. The earlier "triangle-poor carriers" intuition is
  only correct for the long-path subcase.

## Coverage — no graph escapes

| check | result |
|---|---|
| closed by A (`boundary < 1`) **or** B (`T/RHS < 1`) | **100.0%** |
| neither (boundary `≥ 1` **and** carriers triangle-rich **and** `T/RHS > 0.9`) | **0** |

**Every `Required > 0` graph is closed by exactly one of the two mechanisms.** The bimodality
means the assignment is unambiguous: `boundary_ratio < 1` ⟹ Type A (Courant–Fischer gap),
`boundary_ratio > 2` ⟹ Type B (T-smallness). There is no graph that is both
large-boundary *and* T-large, and none with an intermediate boundary ratio.

---

## Synthesis — the `Required > 0` regime is structurally complete

The whole investigation converges here: the open `Required > 0` regime splits, with **0
exceptions over 1296 graphs**, into two mechanisms that mirror the two closed families:

| | TYPE A | TYPE B |
|---|---|---|
| signature | `boundary_ratio < 1` | `boundary_ratio > 2` |
| bottleneck | vertex (deg2+dense-like) | path (lollipop-like) |
| share | 70.4% | 29.6% |
| closing mechanism | **Courant–Fischer**: `λ₂(G[B]) ≥ (1−boundary)λ₂(G) ≈ λ₂(G)`, then Poincaré-on-block + mass bound | **T-smallness**: `T = O(λ₂²) ≪ RHS`, from block-internal (clique) flatness |
| rigorous pieces | minimality (exact), Poincaré-on-block (exact) | apex identity + clique uniformity (exact for lollipop) |
| residual | prove `boundary_ratio < 1` for vertex bottlenecks | prove `T = O(λ₂²)` for general path bottlenecks |

**What is established:** a complete, exhaustive structural classification of `Required > 0`.
The bimodal boundary ratio is the discriminant; each side has a mechanism that is rigorous on
its core family (deg2+dense for A, lollipop for B) and verified to close B on 100% of the
broader corpus. **What remains:** turning each mechanism into a family-independent theorem —
for A, that the vertex-bottleneck boundary term is provably `< λ₂(G)` (needs `|∂(B,C)|` small
and `f_B` small at the boundary); for B, that the path-bottleneck `T` is provably `O(λ₂²)`
(needs the block-internal flatness in general, not just the clique closed form). Both residuals
are the same vertex-vs-path dichotomy that has structured the entire problem, now pinned to two
concrete, complementary inequalities with no graph falling outside them.

### Caveats
`λ₂`, `f`, `f_B` numerical; N = 1296 `Required > 0` graphs (deg2dense, degk, lollipop, pathend,
two-cycles; two-cycles contributed no `Required > 0` here). `boundary_ratio` uses the exact
block-Fiedler. The Courant–Fischer bound for Type A is exact minimality; "closed" still relies
on the (asymptotic) mechanism step to B. Type B "closed" = `T/RHS < 1` (B holds) with the
mechanism understood in closed form only for lollipops. The 100% A-or-B coverage and the
bimodality (gap in `(1,2]`) are empirical over this corpus; the classification is structural,
not a completed proof.
