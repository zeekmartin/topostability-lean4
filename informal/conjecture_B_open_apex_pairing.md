# Conjecture B — apex (neighbourhood) pairing of the open energy and the covariance

Target (= `−Q ≥ 0`, the conjecture): **`Open + 𝒜 ≥ λ₂·fᵀAf`**, with `Open = fᵀL_P f`,
`𝒜 = Cov_L(d, f²) = ½Σ_{ab∈E}(d_a−d_b)(f_a²−f_b²)` (see
[`conjecture_B_global_summation_parts.md`](conjecture_B_global_summation_parts.md)), and
`fᵀAf = Σ_c s_c f_c` (`s_c = (Af)_c = Σ_{v∈N(c)} f_v = (d_c−λ₂)f_c`). This note tries to localise the
target to a single apex `c` (= vertex, neighbourhood `N(c)`). Code:
[`conjecture_B_open_apex_pairing.py`](../conjecture_B_open_apex_pairing.py), 580 graphs, 20 767
apices, all residuals machine-zero.

**Apex conventions (ordered pairs `a,b∈N(c)`, `a≠b`):**
`Open_c = Σ_{a≁b}(f_a−f_b)²`, `T_c = Σ_{a~b}(f_a−f_b)²`, so `Σ_c Open_c = 2·Open`, `Σ_c T_c = 2·T`.
Write `open_c := Open_c/2` so `Σ_c open_c = Open`. `mass_c = Σ_{v∈N(c)} f_v²`.

---

## TASK 1 — apex decomposition of `Open` (exact; circular when summed)

Exact (machine-zero, 580 graphs):

> **`Open_c + T_c = Σ_{a,b∈N(c)}(f_a−f_b)² = 2·d_c·mass_c − 2·s_c²`**, and `s_c = (d_c−λ₂)f_c`, so
> `Open_c + T_c = 2 d_c·mass_c − 2(d_c−λ₂)² f_c²`.

This is the **neighbourhood variance identity** — a pure algebraic fact about `N(c)` (formalised,
see below). Summed over apices it gives `Σ_c(Open_c+T_c) = 2Σ_v σ_v f_v² − 2fᵀA²f = 2(T+Open)`:
exactly the master `A²` identity `T+Open = Σ_v[σ_v−(d_v−λ₂)²]f_v²`. So the apex split is the **same
A² identity, localised** — circular at the global level, but it produces genuinely new per-apex
objects `Open_c, T_c` (and `A_c` below).

## TASK 2 — apex decomposition of the covariance `𝒜` (exact; BOUNDARY-supported)

Using `d_a − d_b = Σ_c[1_{a∈N(c)} − 1_{b∈N(c)}]` and reordering:

> **`𝒜 = Σ_c A_c`**,  `A_c = ½ Σ_{edges (v,w): v∈N(c), w∉N(c)} (f_v² − f_w²)`   (residual `1.7·10⁻¹³`).

`A_c` is a sum over the **edge boundary** `∂N(c)` (edges leaving the neighbourhood; `in = v∈N(c)`).
This is the crux structural finding:

> **`𝒜` localises to the BOUNDARY of `N(c)`; `Open` localises to the INTERIOR (cherries within
> `N(c)`).** They do not share a per-apex support.

Diagnostics: `corr(open_c, A_c) = +0.41` (weak), `A_c < 0` on 72% of apices (the hub-flatness sign,
now apex-local). The boundary/interior split is the apex-level analogue of the global edge-vs-non-edge
mismatch found in the SBP round.

## TASK 3 — the local apex inequality FAILS

The only apex share of `λ₂fᵀAf` that sums correctly is `λ₂ s_c f_c` (since `Σ_c λ₂ s_c f_c =
λ₂Σ_c s_c f_c = λ₂fᵀAf`). Testing the per-apex pairing:

| candidate local inequality | per-apex | graphs (aggregate) |
|---|---|---|
| `open_c + A_c ≥ λ₂ s_c f_c` | **3379/20767 (16.3%)** | 580/580 |
| `open_c + A_c ≥ λ₂ mass_c` | 2944/20767 (14.2%) | 545/580 |
| `open_c + A_c ≥ (λ₂ s_c f_c)⁺` | 16.3% | 580/580 |

The aggregate `580/580` is just the global theorem; **per-apex it fails at 84% of apices**. The
boundary `A_c` and interior `open_c` cannot balance the share `λ₂ s_c f_c` locally — exactly because
they sit on disjoint supports (TASK 2). No apex-local certificate exists, consistent with every prior
localisation attempt (per-edge, per-apex Poincaré, hub-local).

## TASK 4 — Cauchy–Schwarz on open cherries (exact but wrong object)

Inside `N(c)`, the **internal-cherry** covariance `cov_c = ½Σ_{a≁b∈N(c)}(d_a−d_b)(f_a²−f_b²)` (an
inner product over open cherries) satisfies, at **every** apex (`20767/20767`):

> `|cov_c| ≤ √( Ed_c · (2·Open_c) )`,  `Ed_c = Σ_{a≁b∈N(c)}(d_a−d_b)²`  (open-cherry Dirichlet energy of `d`).

This is the desired "Open controls the degree/`f²` variation inside `N(c)`" — but it is **very loose**
(tightness `|cov_c|/√(…)` median `0.003`, max `0.515`) and, decisively, **`cov_c ≠ A_c`**: the
quantity that the cherry Cauchy–Schwarz controls is the *interior* covariance, whereas the term that
actually appears in the target is the *boundary* covariance `A_c`. So this C–S, though exact and
universal, bounds the wrong object.

## Conclusion

The apex/neighbourhood pairing yields two new **exact** identities but no local certificate:

- **Neighbourhood variance identity** (TASK 1, formalised): `Σ_{a,b∈N(c)}(f_a−f_b)² = 2d_c·mass_c −
  2s_c²` — the per-apex building block; summed = the `A²` identity (circular).
- **Apex/boundary covariance** (TASK 2): `𝒜 = Σ_c A_c` with `A_c` supported on `∂N(c)`.
- **The obstruction is a support mismatch**: `𝒜` lives on neighbourhood *boundaries*, `Open` on
  neighbourhood *interiors*. The local inequality fails at 84% of apices (TASK 3); the only exact
  cherry Cauchy–Schwarz (TASK 4) controls the interior covariance, not the boundary `A_c`.

The apex route therefore confirms, at finer resolution, the global lesson: the cancellation between
`Open` and the covariance `𝒜 = Cov_L(d,f²)` is irreducibly **non-local** — it must move energy from
neighbourhood interiors to neighbourhood boundaries across the whole graph. A working proof needs a
*non-apex-local* coupling (e.g. a global transport between `∂N(c)` and the open cherries), not any
single-neighbourhood inequality.

## Formalised (Lean, `ConjectureB.lean`, no `sorry`)
- `neighbor_dirichlet_identity` — `Σ_{a,b∈N(c)}(f_a−f_b)² = 2·d_c·(Σ_{v∈N(c)}f_v²) −
  2·(Σ_{v∈N(c)}f_v)²` (the exact neighbourhood variance identity; pure algebra, no spectral
  hypothesis). With the eigen-recursion this is the per-apex `Open_c+T_c = 2d_c·mass_c −
  2(d_c−λ₂)²f_c²`.
