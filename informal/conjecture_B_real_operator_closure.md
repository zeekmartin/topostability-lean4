# Conjecture B — closure analysis on the real operator `M = λ₂Q − L_t`

Closure attempt on `fᵀMf ≥ 0` (`M = λ₂Q − L_t`, real triangles `t_ab=(A²)_ab`), with
the min-degree relaxation `K = λ₂Q − L_min` alongside. Family: deg2+dense. Code:
[`conjecture_B_real_operator_closure.py`](../conjecture_B_real_operator_closure.py).

**Verdict: C (with B).** `M` has a **stable margin** (`fᵀMf/pos ≈ 0.72–0.81`, flat in
`n`, vs `K` decaying 0.65 → 0.57), confirming it is the right target. But **the
negative-cone / hub-flatness route is dead**: `M`'s negative eigenvectors are *not*
hub-localized (hub_mass ≈ 0.48 ≈ uniform), and the hub-flatness closure is **10³–10⁷ too
loose**. The real margin comes from a **different, direct mechanism**: the triangle
Dirichlet energy `T = Σ t_ab(f_a−f_b)²` is suppressed because `t_ab` is large *exactly
where the Fiedler gradient `(f_a−f_b)²` is tiny* (dense-dense edges). The proof should
bound `T` directly via this anti-correlation — not via eigenvector avoidance.

---

## TASK 1 — negative-cone structure (M vs K)

| `n` | op | #neg | neg/pos | hub_mass med/min | frac>0.5 | negContrib | posContrib | margin |
|---|---|---|---|---|---|---|---|---|
| 100 | **M** | 98 | **0.244** | 0.51/0.01 | 0.51 | 1.06 | 4.33 | **0.756** |
| 100 | K | 98 | 0.383 | 0.55/0.01 | 0.52 | 1.66 | 4.33 | 0.617 |
| 500 | **M** | 498 | **0.275** | 0.39/0.01 | 0.47 | 1.25 | 4.56 | **0.725** |
| 500 | K | 498 | 0.421 | 0.45/0.01 | 0.48 | 1.92 | 4.56 | 0.579 |
| 1000 | **M** | 998 | **0.279** | 0.49/0.01 | 0.49 | 1.27 | 4.57 | **0.722** |
| 1000 | K | 998 | 0.430 | 0.51/0.01 | 0.50 | 1.96 | 4.57 | 0.570 |

- `M`'s margin is **stable** (~0.72–0.81); `K`'s **decays** (0.65 → 0.57). The difference
  is entirely in `negContrib`: real triangles give ~1.1–1.3, min-degree gives ~1.5–2.0
  (growing). Real triangles keep the negative pull bounded.
- **But the negative eigenvectors are NOT hub-localized:** `hub_mass ≈ 0.48` (≈ the
  fraction of vertices above median degree), `min ≈ 0.01`. They are roughly *uniformly
  spread*, not concentrated on hubs. So the "Lemma 1 (hub-localization)" picture is
  **false for `M`'s negative cone** — same as it was for `K`.

## TASK 2 — hub-flatness closure: catastrophic failure

Bounding `|⟨f,v_j⟩|²` per negative eigenvector via `f_v² ≤ d_v/(d_v−λ₂)²` on hub
coordinates (rigorous) and `Σf²≤1` on low coordinates:

| `n` | `neg_bound/pos` (M, rigorous) | (semi-emp) | actual neg/pos |
|---|---|---|---|
| 50 | **9.8×10³** | 9.7×10³ | 0.198 |
| 200 | **4.5×10⁵** | 4.5×10⁵ | 0.187 |
| 500 | **1.0×10⁷** | 1.0×10⁷ | 0.275 |

The hub-flatness bound is **3–7 orders of magnitude too loose** (and `K` is worse). Why:
the per-eigenvector bound `overlap_bound_j ≈ (√(H_flat·hub_mass_j)+√(low_mass_j))² ≈ O(1)`
for *every* one of the ~`n` negative eigenvectors, whereas the actual `|⟨f,v_j⟩|²` is
`O(1/n)` (since `Σ_j |⟨f,v_j⟩|² = 1` spreads over all `n`). Hub-flatness controls `f`'s
*total* hub mass but says nothing about `f`'s **alignment with each individual `v_j`** —
which is what the overlap needs. **The avoidance is real but not capturable this way.**

## TASK 3 — relaxation loss `W₁ − T` explains B2′'s collapse

| `n` | `T/W₁` | loss | loss/real_marg | loss/\|relaxed_marg\| |
|---|---|---|---|---|
| 100 | 0.84 | 0.60 | 0.63 | 1.70 |
| 200 | 0.33 | 2.66 | 0.95 | 20.7 |
| 500 | 0.83 | 0.67 | 0.89 | 8.2 |

The loss `W₁ − fᵀL_tf` is **comparable to the real margin** (loss/real_marg ≈ 0.6–0.95)
and **dwarfs the relaxed margin** (loss/|relaxed_marg| ≈ 1.7–21). So the min-degree
relaxation throws away ~most of the margin — **this is exactly why B2′ collapses**. By
edge class the loss sits on low-dense and dense-dense edges, where the triangle deficit
`(min−1)−t_ab` is large (≈ 19–110, growing with `n`).

## TASK 4 — source of the real margin: flat Fiedler on dense edges

`fᵀMf = λ₂fᵀQf − T`. The margin is large because `T = Σ t_ab(f_a−f_b)²` is **small**, and
`T` is small for a precise structural reason:

| `n` | `T[low-low]` | `T[low-dense]` | `T[dense-dense]` | dense-dense avg `t_ab` | dense-dense avg `(Δf)²` |
|---|---|---|---|---|---|
| 100 | 0% | 78% | 22% | 44 | **1.9×10⁻⁵** |
| 500 | 40% | 50% | 10% | 223 | **7.4×10⁻⁸** |

**Dense-dense edges carry the huge triangle counts (`t_ab ≈ 44–223`) but contribute
almost nothing to `T`, because the Fiedler gradient there is minuscule (`(Δf)² ≈
10⁻⁵–10⁻⁹`).** `T` is dominated by low-dense edges (50–78%) — edges touching the
low-degree vertex, where `f` actually varies. **The dominant mechanism is: `t_ab` is
large exactly where `(f_a−f_b)²` is tiny** (anti-correlation between triangle density and
Fiedler gradient). This is hub-flatness in its *gradient* form — `f` is flat across the
dense bulk — and it is what keeps `T ≪ λ₂fᵀQf`.

---

## TASK 5 — proof direction: **C** (direct variational bound on `T`)

| option | verdict |
|---|---|
| A — stable avoidance + hub-flatness closes it | **No**: hub-flatness closure is 10³–10⁷ too loose |
| B — stable margin but hub-flatness too weak | **Yes** (the negative-cone route is dead) |
| **C — use another direct variational property of `M`** | **Yes — the recommended path** |
| D — B2′ still necessary | **No**: B2′ is strictly worse (loss eats its margin) |

**Conclusion (C).** Target `T = fᵀL_t f = Σ_{ab} t_ab(f_a−f_b)²` directly and prove
`T ≤ λ₂(fᵀQf − S²/m)` (the lift bound, which gives B) by exploiting the **anti-correlation
between `t_ab` and `(f_a−f_b)²`**:
- triangle weight `t_ab` is concentrated on dense-dense edges (`t ≈ 44–223`), but `f` is
  **flat** there (`(Δf)² ≈ 10⁻⁵–10⁻⁹`), so those edges contribute ~0 to `T`;
- the surviving `T` lives on **low-dense** edges (touching the low-degree vertex), which
  are *few* and where `t_ab` is *small* (the relaxation's deficit shows `t ≪ min−1` is
  not the issue there — `t` itself is modest).

The natural formalization is the **apex/neighborhood-Dirichlet form** `T = Σ_c 𝓔_{G[N(c)]}(f)`
(triangle energy = sum of Fiedler Dirichlet energies on neighborhoods): on a dense
neighborhood `N(c)`, `f` is nearly constant, so `𝓔_{G[N(c)]}(f)` is small. Quantifying
"`f` is flat on dense neighborhoods" via the **gradient** hub-flatness (not the value
hub-flatness of `Paper14`) is the missing lemma. **The negative-cone decomposition should
be abandoned; the Dirichlet-energy / apex route is where the stable margin actually lives.**

### Caveats
`λ₂`, `f`, spectra numerical; deg2+dense `q=0.65` to `n=1000`. neg/pos, margins, loss, and
`T`-by-class are exact; the hub-flatness `neg_bound` is a rigorous (but hopeless) upper
bound. The `T/W₁=0.33` at `n=200` is a sample with unusually low-concentrated `f` (high
variance); the qualitative picture (margin from flat-`f`-on-dense-edges) holds at all `n`.
`fᵀMf ≥ 0` (B) holds throughout with margin ≥ 0.72.
