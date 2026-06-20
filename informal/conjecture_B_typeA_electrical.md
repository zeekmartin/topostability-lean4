# Conjecture B — TYPE A: electrical-network perspective

`G = H + v₀` (`v₀~{a,b}`). `gap = λ₂G − B2′`, `c = gap·m/n`. `eff_resist(a,b) = R_aa + R_bb − 2R_ab`,
`R = (L_H − λI)^{-1}` on `1_H^⊥`. Code:
[`conjecture_B_typeA_electrical.py`](../conjecture_B_typeA_electrical.py) (complete, `gnp(0.3..0.9)`,
random-regular, circulant; `n = 30,60,120`).

## TASK 1 — the cleanest invariant

| invariant | min | median | max | spread (max/min) |
|---|---|---|---|---|
| **`gap / eff_resist`** | **3.45** | **6.47** | **9.75** | **2.8×** |
| `gap·γ` | 1.81 | 9.92 | 19.8 | 10.9× |
| `c·eff_resist` | 0.149 | 0.484 | 2.73 | 18× |
| `c/γ` | 0.081 | 0.306 | 2.78 | 34× |

> **`gap / eff_resist`** is by far the most stable invariant — bounded in `[3.4, 9.7]`, **away from 0**,
> with the **complete core at the upper extreme** (`→ 10`, since `gap = 10(n−3)/m`,
> `eff = 2/(n−3)` ⇒ `gap/eff = 5(n−3)²/m → 10`). But it is **not constant** (2.8× spread): there is no
> exact electrical closed form for `gap`. (`c·eff` and `c/γ` are *not* invariants — the earlier
> `c ∝ 1/eff` correlation `r=0.84` conflated size effects; `c·eff → 0` for the complete core.)

So `gap = (gap/eff_resist)·eff_resist` with the prefactor in `[3.4, 10]`: the electrical view pins the
**scale** of `gap` (`gap = Θ(eff_resist) = Θ(1/γ)`), not its exact value.

## TASK 2/3 — Green's-function sum rule for `eff_resist`

Spectral expansion `R = Σ_{k≥2} φ_k φ_kᵀ/(μ_k − λ)` (`μ_k, φ_k` = core Laplacian spectrum) gives, since
`e_a − e_b ⊥ 1` already:

> **`eff_resist = Σ_{k≥2} (φ_k(a) − φ_k(b))² / (μ_k − λ)`**,  with  `Σ_{k≥2} (φ_k(a)−φ_k(b))² = 2`.

Verified: `eff` (direct) `=` `eff` (spectral) to `1.7·10⁻¹⁶`; weight sum `= 2` to `1.8·10⁻¹⁵`. It is a
weighted average of `1/(μ_k − λ)` with weights summing to 2, so (verified `24/24`):

> **`2/(μ_max − λ) ≤ eff_resist ≤ 2/(γ − λ)`**,  and **`eff_resist > 0` is manifest** (every term
> `(φ_k(a)−φ_k(b))²/(μ_k − λ) > 0` because `λ < γ = μ₂`).

Hence `γ·eff_resist ∈ [0.53, 2.14]` (`eff ≈ Θ(1/γ)`): the effective resistance between the attachments
is the natural electrical scale, and its positivity is the clean Green's-function fact `R₂ ≻ 0 ⟺ λ < γ`.

## TASK 4 — rank-2 perturbation / eigenvalue shift

`G = H + v₀` borders `L_H` (a rank-2 update). The eigenvalue is fixed by the **secular equation**
`2 − λ = 𝟙ᵀ G₂ (I+G₂)⁻¹ 𝟙` (`G₂` = 2×2 core resolvent block; matrix-determinant-lemma / Schur
complement). Numerically:

- `gap·(γ−λ) ∈ [1.05, 19.5]` (complete `→ 20`); not constant.
- `gap/(2−λ)` blows up at the complete core (`2−λ → 0`) — `gap` is **not** `∝ (2−λ)`.

So the eigenvalue shift `γ−λ` sets the resolvent scale (`eff ≤ 2/(γ−λ)`), but `gap` is one order below
the shift and no rank-2 identity yields `gap > 0` directly — consistent with all prior analyses.

## TASK 5 — literature

The electrical/perturbation machinery here is **standard**; the novelty is the triangle-graph `T(G)`
positivity, for which no direct result exists.

- **Rank-one/rank-k perturbation secular for Laplacians** — *Eigenvalues of graph Laplacians via
  rank-one perturbations* (arXiv 2008.01669, QJM 2022): characteristic polynomial / secular framework
  for Laplacian rank-one updates. Our `2−λ = 𝟙ᵀG₂(I+G₂)⁻¹𝟙` is the rank-2 (bordered) instance.
- **Effective resistance via Schur complement** — *Effective resistance is more than distance:
  Laplacians, Simplices and the Schur complement* (arXiv 2010.04521): `eff_resist` as a Schur-complement
  / Green's-function object, exactly our `R₂` block.
- **Edge addition, algebraic connectivity, resistance** — *Single-Chord Augmentation of Weighted
  Cycles for Algebraic Connectivity and Network Coherence* (arXiv 2605.24479); classical interlacing
  (Cauchy) bounds `λ₂` under vertex/edge modification.
- Background: *Old and new results on algebraic connectivity of graphs* (de Abreu); Klein–Randić
  effective resistance; Fiedler.

None bounds our `gap = λ₂(T(G)) − …`. The closest leverage is the secular + Schur-complement
effective resistance, which we have used; the residual positivity prefactor is not addressed by any
known result.

## Conclusion

- The **effective resistance `eff_resist(a,b)`** is the natural electrical invariant: a Green's-function
  sum rule gives `eff_resist = Σ_{k≥2}(φ_k(a)−φ_k(b))²/(μ_k−λ) > 0` (manifest, `= R₂ ≻ 0 ⟺ λ < γ`),
  bounded `2/(μ_max−λ) ≤ eff ≤ 2/(γ−λ)`.
- **`gap = Θ(eff_resist)`**: `gap/eff_resist ∈ [3.4, 10]` is the most stable invariant, with the
  complete core at the maximum (`10`). But it is **not constant** — the electrical view fixes the
  *scale* of `gap` and gives `eff > 0`, yet the order-one prefactor `gap/eff` carries the same
  irreducible `O(1)` residual no single scalar pins down.
- `gap > 0` reduces, cleanly, to `gap/eff_resist ≥ c₀ > 0` with `eff_resist > 0` proven (Green's
  function). The remaining content is exactly the lower bound `c₀ ≈ 3.4` on the prefactor — the
  conjecture, now in its most natural (electrical) form.

This closes the exploration: the most natural framing of TYPE A is electrical — `gap ≍ eff_resist(a,b)`
in the `(L_H − λ)` metric, with manifest `eff_resist > 0`; the open core is the positive prefactor.

## Lean
No new lemma (numerical/analytical study). The clean Green's-function fact `eff_resist > 0 ⟺ R₂ ≻ 0
⟺ λ < γ` is Courant–Fischer; standing positive content unchanged (TYPE B closed, complete-core
`10(n−3)/m`).

Sources:
- [Eigenvalues of graph Laplacians via rank-one perturbations (arXiv 2008.01669)](https://arxiv.org/abs/2008.01669)
- [Effective resistance is more than distance: Laplacians, Simplices and the Schur complement (arXiv 2010.04521)](https://arxiv.org/pdf/2010.04521)
- [Single-Chord Augmentation of Weighted Cycles for Algebraic Connectivity (arXiv 2605.24479)](https://arxiv.org/html/2605.24479)
- [Old and new results on algebraic connectivity of graphs (de Abreu)](https://www.math.ucdavis.edu/~saito/data/graphlap/deabreu-algconn.pdf)
- [Algebraic connectivity (Wikipedia)](https://en.wikipedia.org/wiki/Algebraic_connectivity)
