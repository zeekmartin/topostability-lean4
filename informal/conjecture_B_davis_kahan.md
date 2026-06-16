# Conjecture B — Davis–Kahan approach: mechanism confirmed, bound too loose

Close B via `fᵀMf ≥ 0`, `M = λ₂Q − L_t`, by bounding the Fiedler's overlap with `M`'s
negative cone using eigenspace-perturbation (Davis–Kahan). Code:
[`conjecture_B_davis_kahan.py`](../conjecture_B_davis_kahan.py).

**Headline.** The *mechanism* is confirmed beautifully — `M`'s negative eigenvectors are
**high-frequency** (median high-freq mass **0.99**) and the Fiedler `f=u₂` overlaps them
**negligibly** (median `|⟨u₂,v_j⟩|² = 0.0007`, actual `neg/pos ≤ 0.09`). But **Davis–Kahan
cannot close B**: `M` is *not* a small perturbation of a function of `L` — the
perturbation `‖P‖ ≈ 12` swamps the eigengap (`L_t = (d−1)L` holds *only* for complete
graphs), so the DK bound is ~vacuous (closes only 49/1500, ~1000× looser than the true
overlap). The avoidance is exact-eigenvector structure, not perturbative stability.

---

## TASK 2 — is `M` a function of `L`? (the crux: no)

**Regular identity `L_t = (d−1)L`: holds ONLY for complete graphs.** Over the 13 regular
corpus graphs it is exact on **6/13** — exactly `K_4…K_9`. Relative residual
`‖L_t−(d−1)L‖/‖L_t‖` median **0.25**, max **1.0** (e.g. triangle-free regular graphs have
`L_t=0`). `L_t=(d−1)L` ⇔ every edge lies in `d−1` triangles ⇔ neighborhoods are cliques
⇔ `G` complete. So even on regular graphs `L_t` is *not* a polynomial in `L`.

**Consequence for the perturbation.** Writing the best affine regular-approximation
`M₀ = 2d̄λ₂·I − (λ₂+d̄−1)·L` (a function of `L`, sharing `L`'s eigenvectors), the
perturbation `P = M − M₀` has spectral norm on `1⊥`:

> `‖P‖` median **11.9**, max **18.2**.

This is **the same order as `M`'s own eigenvalues** — `M` is nowhere near a function of
`L`. Davis–Kahan needs `‖P‖ ≪ gap`; here `‖P‖` ≈ the whole spectrum.

---

## TASK 1 — `M`'s negative cone in `L`'s eigenbasis (mechanism confirmed)

Decomposing each negative `v_j = Σ_k c_k u_k`:

| quantity | result |
|---|---|
| high-freq mass `Σ_{λ_k>median} c_k²` | mean **0.82**, median **0.99**, min 0.00 (>0.5 on **84%**) |
| `\|c_2\|² = \|⟨u_2,v_j⟩\|²` | **max 0.176, median 0.00073, mean 0.0063** |
| `corr(μ_j, \|c_2\|²)` | **+0.39** (more negative ⇒ less `u_2`-overlap) |

So negative directions are overwhelmingly high-frequency and the Fiedler's overlap with
them is **minuscule** (median `7×10⁻⁴`). This is exactly the smoothness picture, now in
the cleanest form: `f` is the lowest `L`-mode, the negative cone is the high-`L`-mode
subspace, and the overlap is tiny. (16% of negative directions have high-freq mass ≤ 0.5
— the same non-localized minority as before — but their `|c_2|²` is still small.)

---

## TASK 3 — Davis–Kahan closure: FAILS (bound too loose)

The exact resolvent identity `(ν_2 − μ_j)⟨u_2,v_j⟩ = −⟨u_2, P v_j⟩` gives the DK bound
`|⟨u_2,v_j⟩|² ≤ ‖P‖² / (ν_2 − μ_j)²` (`ν_2 = M₀`-eigenvalue at `u_2`). Closure test:

| | result |
|---|---|
| DK-predicted `neg_part ≤ pos_part` | **49/1500** graphs |
| `DK_neg / pos` ratio | median **3.16**, max 10.5 (too lossy) |
| **actual** `neg / pos` ratio | median **0.018**, max **0.091** |

Because `‖P‖ ≈ 12` is comparable to `ν_2 − μ_j`, the DK bound is near-vacuous (often
capped at 1) — roughly **1000× larger** than the true overlap (`10⁻³`). The genuine
avoidance is *much* stronger than perturbation theory can certify: it comes from `f`
being an *exact* eigenvector of `L` (not a perturbed one) meeting a genuinely
high-frequency cone, a structural orthogonality that the `‖P‖/gap` mechanism throws away.

---

## TASK 4 — literature

The **Davis–Kahan sin Θ theorem** bounds the angle between eigenspaces of `M₀` and
`M=M₀+P` by `‖P‖/gap`
([Davis–Kahan for statisticians, arXiv:1405.0680](https://arxiv.org/pdf/1405.0680);
[moderate-gap variant, arXiv:2510.22393](https://arxiv.org/pdf/2510.22393);
[spectral-clustering tutorial, arXiv:0711.0189](https://arxiv.org/pdf/0711.0189)). It is
the standard tool for graph-Laplacian eigenspace stability in spectral clustering, but it
is designed for the **small-perturbation regime** (`‖P‖ ≪ gap`), which our problem
violates by an order of magnitude. The "moderate gap" extension still needs `P`
uncorrelated with the base operator — not our situation. **Mathlib4** has no Davis–Kahan
/ sin Θ theorem and no eigenspace-perturbation API (only `Matrix.PosSemidef`, the
`lapMatrix` Laplacian API, and global Rayleigh sup/inf); formalizing a DK route would
require building it, and it would not close B anyway.

---

## Synthesis

- **TASK 2 kills the DK route at the root:** `M = λ₂Q − L_t` is not close to any function
  of `L` (`L_t=(d−1)L` only at `K_n`; `‖P‖≈12`). DK's `‖P‖/gap` is vacuous.
- **TASK 1 confirms the true mechanism crisply:** `M`'s negative cone is high-frequency
  (median mass 0.99); `f`'s overlap is `~10⁻³`. The avoidance is **exact spectral
  orthogonality** between the lowest `L`-mode and the high-`L`-mode cone — not graceful
  perturbative degradation.
- **The gap between actual (`10⁻³`) and DK-certifiable (`~1`) is ~1000×**, so any proof
  must exploit that `f` is *exactly* `u₂` and that the negative cone is *genuinely*
  high-`L`-energy — i.e. a Courant–Fischer/`λ₂`-minimality argument coupling the two
  spectra directly, not a norm-of-perturbation bound. This is consistent with every prior
  round: the content is minimality, and coarse operator-stability tools discard it.

The productive direction remains: a *direct* spectral inequality
`Σ_{μ_j<0}|μ_j||⟨u_2,v_j⟩|² ≤ Σ_{μ_j≥0}μ_j|⟨u_2,v_j⟩|²` that uses the **monotone coupling**
`corr(μ_j, vᵀLv) = −0.84` (negative-M ⇔ high-L) together with `f=u₂` being the unique
lowest mode — quantitatively, not via `‖P‖`.

### Caveats
`λ₂`, `f`, `M`-spectra numerical. Regular identity over 13 regular corpus graphs; TASK
1/2/3 over a 1500-graph sample (negative directions decomposed in `L`'s eigenbasis). The
reduction `B ⟸ B2′` is rigorous; Lemma 2 (hub-flatness) is proof-ready; B itself remains
unproven. DK does not close it.
