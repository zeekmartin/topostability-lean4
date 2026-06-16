# Conjecture B — profiling the Chebyshev-failure graphs

Where does the Chebyshev-sum bound `W ≤ CB = ΣH·(Σ_w g)/N` on the lock fail, and
why? Code:
[`conjecture_B_chebyshev_outliers.py`](../conjecture_B_chebyshev_outliers.py).
Dataset: 1733 `T(G)`-connected graphs (52 tight + broad + dense, n ≤ 13).

**The exact failure condition.** Over the positive-weight edges
(`w_e = min(d_a,d_b)−δ > 0`, `g_e = (f_a−f_b)²`),
`W − CB = N·Cov(w_e, g_e)`, so **`W > CB ⟺ Cov(weight, gradient) > 0`** — the
weight–gradient anticorrelation locally *reverses*.

**Tie-handling correction.** The lock `W = Σ_{ab}(min(d_a,d_b)−δ)(f_a−f_b)²`
includes **tie edges** (`d_a=d_b` with `min>δ`, weight `d_a−δ>0`). The earlier
"~5%" count came from a run that put tie gradients into `W` but not into `CB`;
with the consistent edge set `{min(d_a,d_b)>δ}` the true failure rate is
**148/1733 = 8.5%**.

**Headline.** The outliers have **no clean structural signature** — they are *not*
quasi-regular (the opposite of the natural guess), not symmetric, with simple
`λ₂`. Crucially, `ρ = W/ΣH` is **the same on outliers as on the rest** (`≤0.10λ₂`,
median `~0.01λ₂`) and the lock `W ≤ R''` holds **148/148** with full margin. So
Chebyshev failure is a **weakness of the bounding method, not a sign of near-
violation** — a case split is neither possible nor needed.

---

## 1. Structural profile (outliers vs the rest)

| feature | outliers (148) | rest (1585) |
|---|---|---|
| degree spread `Δ−δ` (mean) | **4.45** | 3.55 |
| quasi-regular `Δ−δ ≤ 2` | **4%** | 23% |
| # distinct degree classes | 4.71 | 4.23 |
| `λ₂` multiplicity | **1.00** | 1.12 |
| vertex-transitive | **0%** | — |
| `|Aut(G)|` (sampled outliers) | 1–4 (tiny) | — |

- **Quasi-regularity is *refuted* as the cause:** outliers are *less* quasi-regular
  than average (4% vs 23%) and have *larger* degree spread. The natural "weights
  nearly constant → noisy sign" guess is wrong.
- Outliers have **simple `λ₂` (multiplicity 1) and trivial symmetry** (`|Aut|≤4`,
  none vertex-transitive). The failure is a **generic, low-symmetry** phenomenon —
  not driven by degeneracy or symmetry.
- Spread distribution among outliers: `Δ−δ ∈ {2:6, 3:37, 4:43, 5:25, 6:23, 7:12,
  8:2}` — spread across the board, only 6/148 are quasi-regular. No threshold
  separates outliers from the rest.

## 2. The ordering failure — which edges break it

Among the **1393 breaking edges** (high weight *and* high gradient) across all
outliers:

- **76%** join vertices of **similar degree** (`|d_a−d_b| ≤ 1`) — and both are
  *above* `δ` (so `w_e` is large);
- **73%** are **sign-cut edges** (`f_a f_b < 0`, crossing the Fiedler partition).

So the breaking edges are exactly where **the Fiedler cut passes through the
high-degree bulk**: an edge between two similar, above-minimum-degree vertices
that also straddles the nodal partition has *both* large weight *and* large
gradient. That co-occurrence is the positive covariance. Per-graph `corr(w,g)`
on outliers ranges from `+0.01` to `+0.37` (mostly mild).

## 3. `ρ = W/ΣH` on outliers vs the rest — essentially identical

| | max `ρ/λ₂` | median `ρ/λ₂` |
|---|---|---|
| **outliers** | 0.1035 | 0.0114 |
| rest | 0.1044 | 0.0088 |

The average uphill gradient `ρ` is **just as small on the outliers** (`≤0.10λ₂`)
as everywhere else. The lock `W ≤ R''` holds on **148/148** outliers. **Chebyshev
failure does not make the lock tight** — `W` stays far below `R''`; only the
*Chebyshev estimate* of `W` is exceeded.

## 4. Is there a single predictor? Can the proof case-split?

**No single structural predictor.** Quasi-regularity is refuted; degree spread,
class count, multiplicity, and symmetry all *overlap* heavily between outliers and
rest. The only exact characterization is the analytic one — `Cov(w,g) > 0` — which
is not a clean graph class. The 8.5% are scattered generic graphs.

**A case split is therefore neither viable nor necessary.** Not viable: there is
no structural class to split on. Not necessary: on the outliers `ρ` is small and
the lock holds with margin, so they are not a hard sub-case — they are merely
where *this particular bound* (uniform-weight Chebyshev, which requires monotone
opposite ordering) is too crude.

**Implication for the proof.** Replace Chebyshev's *monotonicity* requirement,
which is what the 8.5% violate, with a **rearrangement / sorted** argument: order
the positive-weight edges by weight and bound the gradient on the heavy tail
directly (the breaking edges are few and carry small gradient — `ρ ≤ 0.10λ₂`
*uniformly*, outliers included). Equivalently, target a **monotonicity-free
uniform bound** `ρ = W/ΣH ≤ c·λ₂` (empirically `c ≤ 0.104` over all 1733 graphs)
and combine with `ΣH ≤ ½Σd²−mδ`. The uniform smallness of `ρ` — which holds on
outliers too — is the robust fact to prove, not a partition of cases.

### Caveats
- `λ₂`, `f` numerical; `|Aut|` capped at 2·10⁵ (no outlier hit the cap). Edge set
  `{min(d_a,d_b) > δ}` (positive lock weight). `T(G)`-connected graphs, n ≤ 13.
- The 8.5% figure is the corrected rate (consistent tie handling); the lock itself
  holds on 1732/1733 here (one near-zero-`λ₂` numerical miss), and on all prior
  censuses.
