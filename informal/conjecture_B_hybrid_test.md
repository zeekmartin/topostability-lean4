# Conjecture B — hybrid proof test (gradient bound + carrier/unequal split): FAILS

Hybrid idea: bound equal-degree edges by the sharp gradient lemma, keep unequal-degree
edges as the actual `T_uneq`. Then `T = T_eq + T_uneq ≤ T_eq_bound + T_uneq`, so B follows
*if* `T_eq_bound + T_uneq ≤ RHS = λ₂(fᵀQf − S²/m)`. Code:
[`conjecture_B_hybrid_test.py`](../conjecture_B_hybrid_test.py).

**Headline: the hybrid does NOT close B.** Across 1526 graphs (corpus + deg2+dense +
lollipop/barbell/chain/appendix + ER/WS/regular), `T_eq_bound + T_uneq ≤ RHS` is **violated
on 11 graphs** (max ratio **2.2**). The cause is that the **sharp gradient bound is too
loose on dense equal-degree edges**: on deg2+dense and on regular circulants, `T_eq_bound`
*alone* already exceeds `RHS`. The bound only helps where equal-degree triangle-rich edges
have **small exclusion sets** (lollipop clique edges, `excl = ∅`), which is *not* the dense
case.

---

## Results

| | value |
|---|---|
| B holds (`T ≤ RHS`) | **1526/1526** |
| sharp bound valid on equal-degree edges | 140/17698 "violations" — **all numerical** (see below) |
| **hybrid `T_eq_bound + T_uneq ≤ RHS`** | **holds 1515/1526; 11 VIOLATIONS** |
| hybrid/RHS | max **2.20**, median 0.47 |

**The 11 hybrid violations:**

| family | n | hybrid/RHS | `T_eq_bound` | `T_uneq` | `RHS` |
|---|---|---|---|---|---|
| deg2+dense | 200 | **2.20** | **5.84** | 3.21 | 4.11 |
| corpus (dense) | 8 | 2.16 | 48.0 | 6.0 | 25.0 |
| deg2+dense | 100 | 1.82 | 4.51 | 3.16 | 4.21 |
| deg2+dense | 50 | 1.57 | 3.88 | 3.02 | 4.41 |
| corpus | 8 | 1.33 | 48.0 | 0.0 | 36.0 |
| circulant (4-reg) | 50 | 1.15 | 2.96 | 0.0 | 2.58 |

On deg2+dense and circulant, **`T_eq_bound` alone exceeds `RHS`** (5.84 > 4.11; 2.96 >
2.58) — the gradient bound on the *equal-degree* edges already overshoots, before adding
`T_uneq`. So the hybrid cannot work on dense graphs.

## Why the gradient bound is loose on dense equal-degree edges

The sharp per-edge bound is `(f_a−f_b)² ≤ |excl|·Σ_{excl}f² / (d−λ₂+1)²`. On a **dense**
graph, an equal-degree edge `ab` has a **large** exclusion set `excl = (N(a)△N(b))∖{a,b}`
(many non-shared neighbours) and a **large** `t_ab` (many triangles). The product
`t_ab·|excl|·Σ_{excl}f²` is then sizeable even though the *actual* `(f_a−f_b)²` is tiny (the
Fiedler is flat on the dense region). Summed over the many dense equal-degree edges,
`T_eq_bound` blows past `RHS`. The lollipop success was the opposite extreme: there the
equal-degree edges are **clique** edges with `excl = ∅` (`N(a)\{b}=N(b)\{a}`), contributing
**0** to `T_eq_bound` — so the bound is exact there but does no real work.

## The 140 "validity violations" are numerical

On equal-degree edges with `excl = ∅` (twin vertices `a,b` with `N(a)\{b}=N(b)\{a}`), the
eigen-equation forces `(d−λ₂+1)(f_a−f_b)=0`, i.e. `f_a = f_b` **exactly**, so the bound
`(f_a−f_b)² ≤ 0` holds with equality. Numerically `eigh` returns `f_a−f_b ≈ 10⁻⁶` (and
degenerate-`λ₂` eigenspaces amplify this), which trips the `>0` check at tolerance `10⁻⁹`.
These 140 are **artifacts**; the bound is rigorously valid (it is the formalized
`fiedler_gradient_hub_flatness_adj_sharp`).

## By-family structure (means)

| family | # | `T_eq/T` | `T_uneq/T` | `T_eq_bound/RHS` | hybrid/RHS max |
|---|---|---|---|---|---|
| corpus | 1500 | 0.12 | 0.88 | 0.085 | **2.16** |
| deg2+dense | 3 | 0.03 | 0.97 | **1.13** | **2.20** |
| lollipop | 6 | **0.00** | 1.00 | 0.00 | 0.18 |
| barbell | 4 | 0.00 | 1.00 | 0.00 | 0.01 |
| chain | 2 | 0.00 | 1.00 | 0.00 | 0.04 |
| appendix | 2 | 0.21 | 0.79 | 0.05 | 0.20 |
| ER / WS | 4 | ~0.1 | ~0.9 | ~0.12 | 0.18–0.56 |
| circulant | 2 | **1.00** | 0.00 | **1.10** | **1.15** |

Two revealing rows:
- **lollipop/barbell/chain:** `T_eq/T = 0` — the equal-degree (clique) edges carry *none*
  of `T`; closure is due to `T_uneq` (junction edges) being small, **not** the gradient
  bound. So the earlier "gradient bound closes lollipops" was really "junction `T_uneq` is
  small".
- **circulant (regular, all edges equal-degree):** `T_eq_bound/RHS = 1.10 > 1` — the bound
  overshoots even on a clean regular graph with triangles.

---

## Synthesis — the hybrid is not a proof

- **The sharp gradient bound is too loose on dense equal-degree edges** to be summed against
  `RHS`. It is tight only when equal-degree triangle-rich edges have empty exclusion sets
  (cliques) — where it also contributes nothing. So it cannot carry a dense graph.
- **The hybrid `T_eq_bound + T_uneq ≤ RHS` fails** on the dense families (deg2+dense,
  circulant, dense corpus), with ratios up to 2.2.
- The two mechanisms remain **complementary but non-composable** via this split: on
  deg2+dense the *unequal-degree* bottleneck edges need the carrier/`β≈λ₂` argument, while
  the *equal-degree* dense edges are exactly where the gradient bound is loosest — so
  splitting by degree-equality puts the hard mass on both sides.

**What this rules out:** a proof of the `T ≤ RHS` lift by edge-wise gradient bounding of the
equal-degree part. The robust facts (B holds; `Deficit ≥ Required` with margin; the
`sign(Required)` regime split; `Q3 = ∅` anti-correlation) stand, but a single closing
lemma for the `Required > 0` regime still requires a bound that captures the **actual
Fiedler flatness on dense subgraphs** (a spectral/Poincaré statement on `G[N(c)]`), not the
combinatorial `|excl|·Σ_{excl}f²` per-edge bound, which over-counts on dense edges.

### Caveats
`λ₂`, `f`, per-edge data numerical. 1526 graphs; the 11 hybrid violations are genuine
(ratio > 1.1, not numerical), concentrated on dense graphs. The 140 equal-degree
"validity" violations are numerical (`g² ≈ 10⁻⁶` vs bound 0 on twin edges). `T ≤ RHS` (B)
holds throughout.
