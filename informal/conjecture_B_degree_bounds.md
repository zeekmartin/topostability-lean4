# Conjecture B — degree-based spectral bounds do not close the block lemma

**Target.** Certify `λ₂(G[B]) ≥ c·λ₂(G)` (`B` = p=80% block; empirically `ratio ≥ 2.51` on
1962 graphs) via a classical degree-sequence lower bound on `λ₂(G[B])`. Code:
[`conjecture_B_degree_bounds.py`](../conjecture_B_degree_bounds.py).

**Headline (negative, with one clean positive).** No classical degree-based bound closes the
lemma:
- **TRACK A:** the valid degree bounds (Brouwer–Haemers, Kirkland, simple `2δ−b+2`) are
  *usually negative* on the p=80% block; Lu–Man–Kahn is only **72% valid**. Their **combined**
  coverage certifies `ratio ≥ 2` on only **51%** of graphs.
- **TRACK B:** **71%** of p=80% blocks are *not* dense-by-half (`δ_B ≤ (|B|−2)/2`), yet *all*
  of them have actual `ratio ≥ 2.51` — so the density gate is wrong, and the simple bound
  misses the majority.
- **TRACK C (positive):** `δ_B/λ₂(G) ≥ 2.65` **universally** (median 15.7) — the block's
  minimum internal degree is `≥ 2.65·λ₂(G)`, a clean necessary condition confirming the
  *degree-scale* picture. But `δ_B` *upper*-bounds `λ₂(G[B])` (Fiedler), so it is not the gap.
- **TRACK D refuted:** the "boundary forcing is small" bypass fails — `‖g‖²/‖f_B‖²` has median
  **88.8** (the forcing is huge, not small), so the block-uniformity genuinely requires the
  large gap `(γ−λ₂)²`; it cannot be obtained from a small `‖g‖`.

The lemma remains **open**. The gap is real and degree-scaled, but it needs the block's full
*spectral expansion*, which no one-line degree-sequence inequality captures.

---

## TRACK A — classical degree bounds (validity + coverage)

For `H = G[B]` on `b` vertices with internal degrees, ratio `= bound/λ₂(G)`:

| bound | %valid | %ratio≥1 | %ratio≥2 | median ratio |
|---|---|---|---|---|
| Brouwer–Haemers `d₁+d₂−b+2` | 100% | 33.0% | 29.7% | **−6.15** |
| Kirkland `2e/(b−1)−(b−2)` | 100% | 1.8% | 1.1% | **−16.30** |
| Lu–Man–Kahn `Σ max(0,2dᵥ−b+1)/(b−1)` | **72.4%** | 78.5% | 73.5% | 8.92 |
| simple `2δ−b+2` | 100% | 27.5% | 24.8% | −8.58 |
| **combined (best valid)** | — | **56.1%** | **51.0%** | — |

- **The valid bounds go negative.** `2δ−b+2`, `d₁+d₂−b+2`, Kirkland all subtract `b`, so for a
  block of `b` vertices with degrees `< b/2` (density `< 0.5`) they are negative — useless. The
  p=80% block has density `≈ 0.55` and large `b`, so these bounds are negative on `~70%`.
- **Lu–Man–Kahn is not a valid lower bound as stated** (violated on 27.6%): it would give
  `ratio ≥ 2` on 73% *where valid*, but a bound that fails a quarter of the time is not a
  certificate. (It overcounts because `Σ max(0, 2dᵥ−b+1)` rewards high-degree vertices without
  penalty for the low-degree ones that pull `λ₂` down.)
- **Combined, the valid degree bounds certify `ratio ≥ 2` on only 51%.** Degree-sequence
  bounds do **not** close the lemma — they fail on exactly the half where the block is
  moderately (not overwhelmingly) dense.

## TRACK B — the non-dense blocks are the majority, and still have the gap

Blocks with `δ_B ≤ (|B|−2)/2` (where `2δ−b+2 ≤ 0`):

| | value |
|---|---|
| count | **1397 / 1962 (71.2%)** |
| families | deg2dense 521, lollipop 420, degk 341, pathend 115 |
| actual `ratio` | min **2.51**, median 9.29, `≥ 2.5` for **100%** |
| density / `|B|` (median) | 0.55 / 54 |

**The density-by-half gate is wrong:** 71% of p=80% blocks fail it, yet every one has
`ratio ≥ 2.51`. These are not exotic — they include 521 deg2+dense blocks (density `≈ 0.55`,
just below the `δ > (b−2)/2` line on the *minimum* degree). So the gap holds well into the
moderately-dense regime that the simple bound cannot see. A bound that closes the lemma must
be sensitive to the *whole* degree sequence / expansion, not the minimum degree vs `b/2`.

## TRACK C — the degree-scale necessary condition (clean, universal)

| quantity | min | median | `≥ 2` | `≥ 2.5` |
|---|---|---|---|---|
| `δ_B / λ₂(G)` | **2.65** | 15.7 | 100% | 100% |

The block's **minimum internal degree is at least `2.65·λ₂(G)`**, universally. Combined with
`λ₂(G) ≤ δ(G)` (Fiedler — the global min degree is the bottleneck carrier), this is the
quantitative form of the degree-scale picture: the carriers are low-degree, the block is
high-degree by a factor `≥ 2.65`. **But this is a necessary, not sufficient, condition:**
Fiedler also gives `λ₂(G[B]) ≤ δ_B`, so `δ_B ≥ 2.65 λ₂(G)` is exactly what `λ₂(G[B]) ≥ 2.5
λ₂(G)` *requires*, not what proves it. We still need a lower bound on `λ₂(G[B])` in terms of
`δ_B`, and `λ₂(H) ≥ 2δ−b+2` is too weak (TRACK A).

## TRACK D — the gap cannot be bypassed

The hope: `‖f_B − mean‖² ≤ ‖g‖²/(γ−λ₂)²`, so if `‖g‖²` is *small*, uniformity follows even
with modest `γ`. The data kills this:

| quantity | median | max | tail |
|---|---|---|---|
| actual `‖f_B−mean‖²/‖f_B‖²` | 0.129 | 0.893 | `<0.1` for 38%, `<0.3` for 86% |
| Poincaré bound `‖g‖²/((γ−λ₂)²‖f_B‖²)` | 0.293 | 4.514 | `<1` for 91% |
| **`‖g‖²/‖f_B‖²`** | **88.8** | 1986 | — |

- **`‖g‖²` is enormous**, not small — median `89×` the block mass (carriers have huge `f`, the
  block has tiny `f`, so the boundary differences `f_u − f_v` are large). The uniformity of
  `f_B` comes *entirely* from dividing by the large `(γ−λ₂)²`, i.e. from the gap. There is no
  "small forcing" shortcut.
- The Poincaré relative bound **exceeds 1 on 9%** of graphs (max 4.5) — there it is vacuous
  (does not certify `f_B` uniform). And the *actual* relative non-uniformity reaches 0.89 — on
  some graphs `f_B` is barely uniform. So even the rigorous Poincaré lemma does not, by itself,
  give strong uniformity without a guaranteed gap.

---

## Synthesis — what is closed, what remains

- **Degree-sequence bounds do not close the lemma** (TRACK A: 51% combined coverage; the valid
  bounds go negative on moderately-dense blocks, which TRACK B shows are 71% of cases).
- **The gap cannot be bypassed via small forcing** (TRACK D: `‖g‖²` is `~89×` the block mass).
- **The one clean universal fact is the necessary condition `δ_B ≥ 2.65 λ₂(G)`** (TRACK C),
  confirming degree scale but not sufficient.

**Why the simple bounds fail, and where to look next.** All the failed bounds subtract `b`
(they are tight only near `K_b`). The p=80% block is a *moderately dense expander* (density
`0.55`, conductance `≈ 0.49` from the prior round), where `λ₂(H) ≈ δ_H · λ₂^{norm}(H)` — the
combinatorial gap is the **product of the normalized gap and the degree scale**, and only the
degree scale is large (`δ_B ≥ 2.65 λ₂(G)`); the normalized gap is `O(1)` and *not* captured by
`2δ−b+2`. The promising remaining route is therefore the **normalized decomposition**:

> `λ₂(G[B]) ≥ δ_B · λ₂^{norm}(G[B])`, with `λ₂^{norm}(G[B]) ≥ c'` (the block is an expander,
> conductance bounded below) and `δ_B ≥ 2.65 λ₂(G)` (TRACK C) ⟹ `λ₂(G[B]) ≥ c·λ₂(G)`.

This needs a *conductance lower bound on the block* (the block is well-mixed, not bottlenecked
— consistent with `h(B) ≈ 0.49 ≈ h(G)` from the final-lemma round) times the degree scale. So
the gap factors as `(degree scale ≥ 2.65) × (normalized expansion = O(1))`, and the proof
obligation splits into a clean degree statement (TRACK C, essentially proved) and a normalized
expansion bound on the carrier-complement. The pure-combinatorial degree bounds tried here are
the wrong tool; the normalized factorization is the way the degree scale actually enters.

### Caveats
`λ₂`, `f` numerical; corpus = 1962 `Required > 0` graphs. Bound validity is checked against the
true `λ₂(G[B])` (Lu–Man–Kahn fails it 27.6%, so is excluded as a certificate). The combined
coverage uses only bounds that are valid on that graph. TRACK C is an exact per-graph ratio
(`δ_B`, `λ₂(G)` numerical). TRACK D's `‖g‖`, Poincaré bound are exact. No bound here closes the
lemma; the round's content is the **elimination of degree-sequence bounds** and the
identification of the **normalized-gap × degree-scale factorization** as the remaining route.
