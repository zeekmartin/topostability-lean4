# Conjecture B — anatomy of the local Poincaré failures (aggregate `T ≤ λ₂·fᵀDf`)

The aggregate triangle-Poincaré `T = Σ_c energy_c ≤ λ₂·fᵀDf = Σ_c λ₂·mass_c` holds with **0
violations**, but the *per-apex* local inequality `energy_c ≤ λ₂·mass_c` fails on a sizeable
fraction of vertices. Here `energy_c =` Dirichlet energy of the Fiedler `f` on `G[N(c)]`,
`mass_c = Σ_{v∈N(c)} f_v²`. We characterise the failing apices and quantify why the aggregate
nonetheless holds. Code: [`conjecture_B_poincare_6pct.py`](../conjecture_B_poincare_6pct.py).
Corpus: 415 graphs (gnp, deg2+dense, degk, lollipop, Watts–Strogatz), 13 162 apices.

**Headline (surprising — failures are in the dense bulk, not the bottleneck).** The failing
apices are **high-degree, low-Fiedler-value bulk vertices**, essentially never adjacent to a
carrier; the aggregate holds because the **surplus from the non-failing apices dominates the
excess by `≥ 4.5×` on every graph**, and the per-apex excess is bounded by a hub-flatness term
`excess_c ≤ 2.25·d_c·f_max²`. So the local failures are a benign, dense-bulk phenomenon fully
absorbed in aggregate — not a bottleneck effect.

---

## 1. The failing set

| | value |
|---|---|
| aggregate `T ≤ λ₂·fᵀDf` holds | **415/415 (100%)** |
| failing apices `F = {energy_c > λ₂·mass_c}` | **3883 / 13162 (29.5%)** |

(The 29.5% is corpus-dependent — earlier denser-gnp corpora gave ≈6% — but the *characterisation*
below is robust across the families.)

## 2. Characterising `F` — high-degree, low-`f`, not carriers

| feature | failing `F` | non-failing |
|---|---|---|
| degree (median / mean) | **29.0 / 29.0** | 18.0 / 19.0 |
| `f_c²` (median) | **0.0004** | 0.0020 |
| adjacent to a carrier (p=80%) | **0.4%** | — |

The failing apices are the **opposite of bottleneck vertices**:
- **High degree** (median 29 vs 18) — they are dense-bulk hubs, not the low-degree carriers.
- **Low `f_c²`** (5× smaller than non-failing) — they sit deep inside a nodal domain where the
  Fiedler is small, not where it concentrates.
- **Essentially never adjacent to a carrier** (0.4%) — the failures are not a boundary/cut
  phenomenon. A high-degree apex `c` has a large, dense neighbourhood `G[N(c)]` with many edges;
  even with small per-edge gradients the summed `energy_c` can exceed the local budget
  `λ₂·mass_c`, because `λ₂` is a *global* constant much smaller than the local connectivity of a
  dense neighbourhood. This is exactly the mechanism the spectral-neighborhood round flagged
  (Rayleigh over-charges dense apices), now localised to the high-degree bulk.

## 3. Excess vs surplus — robust aggregate cancellation

`excess_c = energy_c − λ₂·mass_c` (`> 0` on `F`), `surplus_c = λ₂·mass_c − energy_c` (`> 0`
off `F`). The aggregate `T ≤ λ₂·fᵀDf` is `Σ surplus ≥ Σ excess`.

| | value |
|---|---|
| `Total_surplus / Total_excess` | min **4.51**, median 15.68 |
| `> 1` (aggregate holds) | 100% |

**The surplus dominates the excess by at least `4.5×` on every graph** (median `16×`). The
aggregate is not marginal — it has a wide, uniform safety factor. The surplus comes from the
many low-degree / high-`f` apices (carriers and their neighbours), where `energy_c ≪ λ₂·mass_c`.

## 4. Hub-flatness bound on the excess

For each failing apex, `excess_c` against `d_c·f_max²` (`f_max² = max_{v∈N(c)} f_v²`):

| `excess_c / (d_c·f_max²)` | value |
|---|---|
| median | 0.53 |
| p95 | 1.23 |
| **max** | **2.25** |

So **`excess_c ≤ 2.25·d_c·f_max²` universally** — the per-apex excess is controlled by a single
hub-flatness term (degree × largest neighbour Fiedler-value²). Combined with the value
hub-flatness bound `f_max² ≤ d_max/(d_max−λ₂)²`, the total excess is bounded by a sum of
hub-flatness quantities.

## 5–6. Toward a direct proof of `T ≤ λ₂·fᵀDf`

Two routes assessed:

**(5) Per-vertex → global.** We have `excess_c ≤ 2.25·d_c·f_max²` (bounded) and `Σ surplus ≥
4.5·Σ excess` (verified). But converting this into a *proof* still needs the surplus to
provably dominate — the surplus lives on the low-degree/high-`f` apices and the excess on the
high-degree/low-`f` ones, an anti-correlation between `excess` and `f_c²` (the failing apices
have `f_c²` 5× smaller). A clean lemma would pair each unit of high-degree excess with the
larger low-degree surplus, but no per-vertex pairing is uniform (the counts differ per graph).

**(6) Direct, bypassing apices.** Using `L_G f = λ₂ f`, `fᵀDf = λ₂ + fᵀAf`, so
`λ₂·fᵀDf = λ₂² + λ₂·fᵀAf`, and the target is `T ≤ λ₂² + λ₂·fᵀAf`. The ingredients available are
`cov(t,g) ≤ 0` (universal, anticorr round), the eigen-equation, and hub-flatness. The covariance
bound gives `T ≤ (τ/m)·λ₂` (Chebyshev) which is too loose on dense graphs (the prior anticorr
round); hub-flatness controls the per-apex excess (this round, `C = 2.25`). Neither alone
closes it; the missing piece is a *global* statement that the dense-apex excess (where `f` is
small) is outweighed by the bulk surplus — i.e. a second-moment bound tying `Σ_{high-deg} d_c
f_max²` to `λ₂·fᵀDf`. This is the same delocalization-flavoured gap that the whole `Required ≤
0` aggregate Poincaré rests on.

---

## Synthesis

- **The local Poincaré failures are benign and dense-bulk-localised.** Failing apices are
  high-degree (median 29 vs 18), low-`f` (5× smaller `f_c²`), and essentially never adjacent to
  carriers (0.4%). They fail because a dense neighbourhood out-connects the global `λ₂`, not
  because of any bottleneck structure.
- **The aggregate holds with a uniform `≥ 4.5×` safety factor** (`Σ surplus / Σ excess`), and
  the per-apex excess is hub-flatness-bounded (`excess_c ≤ 2.25·d_c·f_max²`).
- **A direct proof of `T ≤ λ₂·fᵀDf` still needs the global second-moment/delocalization step** —
  the excess (dense, low-`f`) is dominated by the surplus (sparse, high-`f`), but no uniform
  per-vertex pairing or single classical inequality captures the domination. This is precisely
  the `aggregate_triangle_poincare` lemma left open in `ConjectureB.lean`; this round localises
  *where* it bites (the high-degree bulk) and bounds *how much* (hub-flatness, `C = 2.25`).

### Caveats
`λ₂`, `f` numerical; 415 graphs, 13 162 apices. The failing fraction (29.5%) is
corpus-dependent; the characterisation (high-degree, low-`f`, non-carrier) and the quantitative
bounds (`surplus/excess ≥ 4.51`, `excess_c ≤ 2.25·d_c·f_max²`) are the robust outputs. `energy_c`
is the exact induced-subgraph Dirichlet energy; `mass_c = Σ_{N(c)} f_v²`. Carriers = p=80%
Fiedler set. No proof is completed; the round is a structural/quantitative anatomy of the open
aggregate-Poincaré lemma.
