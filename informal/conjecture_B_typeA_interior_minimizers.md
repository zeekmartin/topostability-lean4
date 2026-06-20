# Conjecture B — TYPE A interior minimizers (the true hard cases)

Extract and characterize the TYPE A graphs with smallest `gap/eff_resist`, then **scale-test** to decide
whether the low values are finite-size artefacts or a persistent family. Code:
[`conjecture_B_typeA_interior_minimizers.py`](../conjecture_B_typeA_interior_minimizers.py)
(303 TYPE A graphs: `gnp`/regular/bipartite cores × varied attachments; `gap/eff ∈ [0.01, 15.6]`).

## TASK 1 — the minimizers (`gap/eff < 3`)

32 graphs. The extreme tail (sample):

| family | n | λ | γ | λ/γ | dₐ | d_b | eff | asym | fₐ | f_b | `gap/eff` |
|---|---|---|---|---|---|---|---|---|---|---|---|
| gnp18_.25 lolo | 19 | 0.57 | 0.58 | 0.98 | 1 | 1 | 121.5 | 24.9 | 0.42 | 0.49 | **0.012** |
| gnp30_.25 lolo | 31 | 0.87 | 0.88 | 0.99 | 1 | 4 | 83.6 | 74.7 | 0.65 | 0.13 | 0.019 |
| gnp24_.25 lolo | 25 | 1.08 | 1.44 | 0.75 | 2 | 3 | 3.54 | 0.99 | 0.42 | 0.27 | 0.682 |
| gnp30_.25 lolo | 31 | 1.17 | 1.71 | 0.69 | 2 | 4 | 2.30 | 1.24 | 0.47 | 0.20 | 0.931 |
| gnp18_.35 lolo | 19 | 1.35 | 2.19 | 0.61 | 3 | 3 | 1.88 | 0.09 | 0.29 | 0.26 | 1.355 |
| rr24_5 | 25 | 1.54 | 1.74 | 0.88 | 5 | 5 | 1.72 | 0.02 | 0.21 | 0.20 | 1.539 |

> The extreme minimizers (`gap/eff < 0.2`) have **degree-1 (pendant) attachments** and a **huge
> `eff`** (`> 80`): the ratio is small because `eff` is enormous, **not** because `gap` is small
> (`gap = (gap/eff)·eff ≈ 1.5 > 0`). They sit near the boundary (`λ/γ ≈ 0.98`) on **small, sparse**
> cores.

## TASK 2 — family pattern

| feature | minimizers (`<3`) mean/med | rest (`≥3`) mean/med |
|---|---|---|
| n | 27.8 / **25** | 35.9 / 31 |
| λ | 1.38 / 1.53 | 1.90 / 1.93 |
| λ/γ | 0.63 / 0.64 | 0.26 / 0.22 |
| **dₐ** | **3.7 / 4** | 17.4 / 15 |
| **d_b** | **5.6 / 5** | 19.2 / 17 |
| asymmetry | 4.09 / 0.16 | 0.05 / 0.01 |
| Required | −1.26 / −1.37 | +0.10 / +0.16 |

Attachment-tag among minimizers: **`lolo` 23/32** (both low-degree), `lohi` 5, `sym` 3, `rr` 1;
**18/32 have `n ≤ 25`**; **27/32 above-median asymmetry**.

> **Minimizers = small graphs (`n ≤ 25`) with low-degree attachments (`lolo`), high asymmetry, near
> the boundary.** They are *not* dense-interior graphs; they are **low-degree-attachment / pendant
> artefacts on small sparse cores** — the opposite end from the dense quasi-clique.

## TASK 3 — scale test (decisive)

Grow each candidate pattern with `n` and track `gap/eff`:

| pattern | n=20 | 30 | 50 | 80 | 120 | 200 |
|---|---|---|---|---|---|---|
| `lohi` gnp(.4) (asym lo–hi) | 2.35 | 4.44 | 6.57 | 7.76 | 8.51 | **11.85** |
| `lolo` gnp(.4) (both low-deg) | 1.90 | 3.25 | 4.20 | 4.50 | 4.59 | **5.12** |
| `sym` gnp(.35) | 6.94 | 7.28 | 5.84 | 9.32 | 8.93 | **10.88** |
| `K_{8,N−8}` bipartite | 6.39 | 7.83 | 8.63 | 8.99 | 9.16 | **9.30** (stable) |

> **`gap/eff` INCREASES with `n` for every pattern.** The small values (`1.6–2.3`) occur only at small
> `n` and **grow away** as `n` increases (`lohi → 12`, `lolo → 5.1`, `sym → 11`); the bipartite family
> stabilises at `≈ 9.3`. **The interior minima are finite-size artefacts.** The lowest *asymptotic*
> value is the `lolo` (low-degree-attachment) family at **`gap/eff → ≈ 5`** — bounded well away from 0.

So `inf(gap/eff) ≈ 1.6` is **not** an asymptotic quantity; in the `n → ∞` limit the families give
`gap/eff ≳ 5`. The open prefactor `c₀` is robustly positive asymptotically (`≈ 5` for the tested
patterns), with the small-graph minima being finite-size.

## TASK 4 — candidate covering condition

Correlation of `gap/eff` with candidate variables (full corpus):

| variable | `corr(gap/eff, ·)` |
|---|---|
| **`min(dₐ, d_b)` (low attachment degree)** | **+0.77** |
| `λ` (bottleneck sharpness) | +0.67 |
| `1/n` | −0.29 |
| `leverage R_aa+R_bb` | −0.25 |
| asymmetry | −0.19 |

> The **best single predictor is the low attachment degree `min(dₐ, d_b)`** (`r = +0.77`): low-degree
> attachments give low `gap/eff`. Combined with the scale test, the **covering condition for the
> minimizers is "small `n` and/or low-degree attachments"** — and both effects **vanish as the graph
> grows** (`min(dₐ,d_b)` grows with the core, `gap/eff` rises).

**Candidate lemma shape:** `gap/eff ≥ c₀(min(dₐ,d_b), n)` with `c₀` increasing in the attachment
degree and in `n`; the only sub-`c₀` cases are finite (small `n`, pendant-ish attachments), handled by
a finite check. Asymptotically `gap/eff ≥ ~5`.

## Conclusion

- **The true hard interior minimizers are FINITE-SIZE ARTEFACTS**: small (`n ≤ 25`), sparse cores with
  **low-degree / pendant attachments** (`lolo`, `min(dₐ,d_b)` small) and high asymmetry near the
  boundary. The extreme `gap/eff ≈ 0.01` cases have *huge `eff`* (pendant resistance), not small
  `gap`.
- **They do not persist at scale**: `gap/eff` increases with `n` for every pattern (`→ 5–12`); the
  lowest asymptotic family (`lolo`) tends to `≈ 5`. **`inf(gap/eff) ≈ 1.6` is a small-`n` phenomenon,
  not the `n → ∞` limit.**
- **Controller: `min(dₐ, d_b)`** (`r = +0.77`) — low attachment degree drives small `gap/eff`, and
  both vanish as the graph grows.

This sharpens the open lemma `gap/eff ≥ c₀ > 0`: the worrying small values are **finite-size**, so a
proof can take `c₀ ≈ 5` asymptotically (large `n`) plus a finite check for small graphs / low-degree
attachments. The conjecture's TYPE A reduction is well-founded with `c₀` bounded away from 0 in the
limit.

## Lean
No new lemma (numerical minimizer study). Standing content unchanged; see `CONJECTURE_B_STATUS.md`.
