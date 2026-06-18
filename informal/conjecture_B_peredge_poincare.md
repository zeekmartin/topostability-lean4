# Conjecture B — per-edge attack on the aggregate Poincaré `T ≤ λ₂·fᵀDf`

Rewrite the aggregate triangle-Poincaré as a per-edge sum: with
`T = Σ_{ab∈E} t_ab(f_a−f_b)²` and `λ₂·fᵀDf = λ₂·Σ_{ab∈E}(f_a²+f_b²)`,

`T ≤ λ₂·fᵀDf  ⟺  Σ_{ab∈E} w_ab ≤ 0,   w_ab := t_ab(f_a−f_b)² − λ₂(f_a²+f_b²).`

Test whether `w_ab ≤ 0` holds *per edge* (which would trivialise the proof). Code:
[`conjecture_B_peredge_poincare.py`](../conjecture_B_peredge_poincare.py). Corpus: 536 graphs,
221 033 edges.

**Headline (per-edge conjecture FALSE, but negatives dominate ≥ 2.33×).** The clean per-edge
bound `w_ab ≤ 0` is **false** — 8.1% of edges have `w_ab > 0` (max 0.64), and only 12.9% of
graphs have all edges `≤ 0`. But the positive edges are exactly the **triangle-rich,
tiny-gradient** ones (hub-flatness *nearly* kills them), and the **negative mass dominates the
positive by `≥ 2.33×` on every graph** (median 6.8×), so the aggregate holds with a uniform
safety factor. Triangle-free edges (`t = 0`) are negative with probability **100%** and supply
~21% of the negative mass.

---

## 7. The per-edge conjecture `w_ab ≤ 0` — false

| | value |
|---|---|
| graphs with **all** edges `w_ab ≤ 0` | 69/536 (**12.9%**) |
| max `w_ab` over all edges | **0.6433** (`> 0`) |

So `w_ab ≤ 0` does **not** hold edge-by-edge — the proof of `T ≤ λ₂·fᵀDf` cannot be a trivial
per-edge sign argument. (It would have been if true.)

## 1–2. Distribution of `w_ab`

| | value |
|---|---|
| fraction of edges with `w_ab > 0` | 8.1% (median per-graph 10.5%) |
| `w_ab` min / median / max | −6.011 / −0.0011 / **0.6433** |

The overwhelming majority of edges are negative (median `w_ab ≈ −0.001`, just below 0 for most,
strongly negative for the high-mass ones); a thin 8% tail is positive.

## 3. The positive edges — triangle-rich, gradient-flat

| feature (positive-`w` edges, n=17 999) | value |
|---|---|
| `t_ab` (median) | **16** (triangle-rich) |
| gradient `(f_a−f_b)²` (median) | 0.0012 (tiny) |
| `f_a·f_b > 0` | only 5.6% (mostly anti-correlated) |
| worst edge | `w=0.64`, `t=9`, `grad=0.216`, `mass=0.119`, `f_a f_b=−0.05`, `λ₂=11.0` |

The positive edges are exactly where the structure *fights*: **many triangles** (`t ≈ 16`) so
`t_ab(f_a−f_b)²` is non-negligible even though the **gradient is tiny** (hub-flatness makes
`(f_a−f_b)² ≈ 0.001`). Hub-flatness *almost* forces `w_ab ≤ 0` — for the vast majority of
triangle-rich edges the gradient is small enough that `t_ab(f_a−f_b)² < λ₂(f_a²+f_b²)` — but on
8% it does not quite win. The worst edge has a relatively large gradient (0.216) on a `t=9`
edge that still beats `λ₂·mass`. So **hub-flatness is the mechanism but is not pointwise tight
enough** to give `w_ab ≤ 0` everywhere.

## 4. Negatives dominate — the aggregate safety factor

| `|Σ_{w<0} w| / Σ_{w>0} w` | value |
|---|---|
| min | **2.33** |
| median | 6.79 |
| `> 1` (aggregate holds) | 100% |

The negative mass beats the positive mass by **at least 2.33×** on every graph. So even though
`w_ab` is positive on a thin triangle-rich tail, the negatives (triangle-poor and `t < λ₂`
edges, plus the high-mass low-`t` edges) dominate with a uniform margin — exactly the
`Σ w_ab ≤ 0` with safety factor ≥ 2.33 (consistent with the apex-level `surplus/excess ≥ 4.5`
from the companion round; the edge factor is smaller because the split is finer).

## 5. Triangle-free edges are unconditionally good

| | value |
|---|---|
| `t = 0` edges with `w_ab ≤ 0` | 2275/2275 (**100%**) |
| share of total negative mass from `t = 0` edges | median 21% (range 0–100%) |

For `t_ab = 0`, `w_ab = −λ₂(f_a²+f_b²) ≤ 0` **always** (trivially). These triangle-free edges
contribute a median 21% of the negative mass — substantial but not the whole story; the rest of
the negative mass comes from triangle-bearing edges with `t_ab < λ₂` or small gradient.

---

## Synthesis — the per-edge view localises the difficulty precisely

- **`w_ab ≤ 0` is false per edge** (8.1% positive), so `T ≤ λ₂·fᵀDf` is not a trivial
  edge-sign fact. The positive edges are **triangle-rich with tiny gradient** — hub-flatness
  nearly but not quite forces them negative.
- **The aggregate holds with a uniform `≥ 2.33×` negative-to-positive margin.** A proof must
  exploit that the positive (triangle-rich, gradient-flat) edges are outweighed by the negative
  (`t = 0`, `t < λ₂`, and high-mass) edges — i.e. the same global domination as the apex view,
  now expressed per edge.
- **The clean sub-results** are: (a) `t = 0 ⇒ w_ab ≤ 0` (trivial); (b) `t < λ₂ ⇒ w_ab ≤ 0`
  (since then `t(f_a−f_b)² ≤ t(f_a²+f_b²)·2 ...` — actually `w_ab = (t−λ₂)(f_a²+f_b²) −
  2t·f_a f_b`, and for `t < λ₂` with `f_a f_b ≥ 0` both terms are `≤ 0`); (c) the residual
  positive edges have `t ≥ λ₂` *and* `f_a f_b < 0` mostly, where the `−2t f_a f_b > 0` term is
  the culprit but the gradient is hub-flattened. The missing step is bounding `Σ_{t≥λ₂}
  (−2t f_a f_b)⁺` by the negative reservoir — a global anti-correlation/second-moment bound,
  the same open ingredient as `aggregate_triangle_poincare`.

### Caveats
`λ₂`, `f` numerical; 536 graphs, 221 033 edges (gnp, deg2+dense, degk, lollipop,
Watts–Strogatz). `t_ab = (A²)_{ab}` = common-neighbour count. The per-edge identity
`Σ w_ab = T − λ₂·fᵀDf` is exact. The conjecture `w_ab ≤ 0` is refuted; the `≥ 2.33×` margin and
the `t = 0 ⇒ w ≤ 0` facts are the robust positives. No proof is completed — the round shows the
per-edge decomposition does not trivialise `T ≤ λ₂·fᵀDf` and localises the hard edges
(triangle-rich, sign-anticorrelated).
