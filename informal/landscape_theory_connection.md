# Tao–Filoche–Mayboroda landscape theory and `aggregate_triangle_poincare`

**Target** (undirected): `T = Σ_e t_e (f_a−f_b)² ≤ λ·degQuad`, `degQuad = Σ_v d_v f_v²`, `f` the unit
Fiedler (`L f = λ f`). Equivalently `T = fᵀ L_t f` with `L_t = D_t − A_t`, `A_t = A⊙A²` the
Hadamard (triangle-weighted) adjacency, `D_t = diag(σ_v)`, `σ_v = Σ_u t_{uv}`.

**Bottom line.** Landscape theory connects **qualitatively but not quantitatively**:

* **(a) YES, qualitatively** — the landscape `u = (L+diag(σ/maxσ))⁻¹·1` predicts Fiedler flatness:
  `corr(u, f²) > 0` (up to **0.99**), `corr(1/u, σ) > 0` (up to **0.99**). The effective potential
  `1/u` is high on the triangle-dense core, where `f` is small/flat — matching the known
  `corr(t_e, g_e²) < 0`.
* **(b) NO** — no landscape bound closes `T`; all tested candidates overshoot `λ·degQuad` by
  **30×–46000×**, and the Agmon pointwise bound is not even universally valid.
* **(c) Z-matrix YES, M-matrix NO** — the **exact** reformulation `aggregate ⟺ fᵀSf ≥ 0` holds with
  `S = ½(LD+DL) − L_t` a **Z-matrix**, but `S` is an **M-matrix (PSD) only for regular graphs** —
  exactly the already-solved case. Irregularity destroys the M-matrix property.
* **(d)** the exact theorem reduces to *Fiedler alignment*: `f` must avoid `S`'s (small) negative
  eigencone — a global spectral-localization fact, not a landscape/M-matrix positivity.

Numerics: `landscape_theory_connection.py`, 18-graph corpus (complete, cycle, torus, dumbbell,
lollipop, G(n,p), deg2d, twin, Barabási–Albert, Watts–Strogatz, Petersen).

---

## TASK 1 — Computing a landscape function

The bare Laplacian has **no non-trivial landscape**: `L` is singular with `1 ∈ ker L`, and `L u = 1`
is unsolvable (`range L = 1^⊥`, but `1_vec ∉ 1^⊥`); the projected RHS is `0`, so `L⁺·1 = 0`. The two
"regularized" fixes are degenerate because `1` is an eigenvector:

* `(L+εI)⁻¹·1 = (1/ε)·1` (constant), since `L·1 = 0`;
* `(L + J/n)⁻¹·1 = 1` (constant), since `(L+J/n)·1 = 1`.

The only non-degenerate option is a **genuine confining potential** (`1` not an eigenvector), as the
task prescribes:

```
A_land = L + diag(σ_v / max_v σ_v)          (σ_v = Σ_u t_{uv}, the triangle/triDeg potential)
u = A_land⁻¹ · 1_vec  >  0                   (A_land is a nonsingular symmetric M-matrix)
```

`A_land` is a Z-matrix (off-diagonals `−1 ≤ 0`) with positive diagonal `d_v + σ_v/maxσ`, weakly
diagonally dominant and irreducible (connected) with strict dominance wherever `σ_v > 0` ⇒
nonsingular M-matrix ⇒ `u > 0`. The effective potential is `W = 1/u`.

## TASK 2 — Correlations (the landscape DOES track triangles and Fiedler mass)

| graph | `corr(1/u, σ)` | `corr(1/u, d)` | `corr(u, f²)` | `corr(t_e, g_e²)` |
|---|---|---|---|---|
| lollipop10_8 | 0.99 | 0.98 | **0.77** | −0.86 |
| gnp40_0.5 | 0.97 | 0.95 | 0.53 | −0.34 |
| deg2d40_0.6 | 0.67 | 0.84 | **0.99** | −0.31 |
| twin30_3 | 0.98 | 0.98 | **0.89** | −0.87 |
| twin50_2 | 0.99 | 0.99 | **0.92** | −1.00 |
| BA50_3 | 0.74 | 0.51 | 0.24 | −0.12 |

Across the irregular, triangle-bearing graphs:

* `corr(1/u, σ) ≈ 0.6–0.99`: the **effective potential `1/u` is high on the triangle-dense core**;
* `corr(u, f²) ≈ 0.24–0.99` (positive everywhere): the **landscape `u` is large exactly where the
  Fiedler concentrates** — i.e. `f` lives in the wells of `1/u` (low-degree appendages), and is
  flat/small on the high-potential core. This is the FM localization picture and it **matches the
  known `corr(t_e, g_e²) < 0` mechanism**.

So the landscape gives a correct *qualitative* explanation of triangle flatness. (Note: `1/u` tracks
`d` about as strongly as `σ`; the triangle and degree potentials are collinear here, so `u` does not
clearly isolate a *triangle-specific* effect beyond degree.)

## TASK 3 — Agmon-type gradient bounds: not universally valid

The pointwise bound `|f_v| ≤ λ u_v · ‖f‖_∞` holds on most irregular graphs (`fraction = 1.00`) but
**fails on regular and bottleneck graphs** (cycle/torus/Petersen: `0.00`; lollipop: `0.40`). Reason:
on regular graphs `u` is (near) constant while `f` is spread, so the bound has no localization to
exploit. The edge-gradient version `g_e² ≤ C λ²(u_a+u_b)²` has `corr(g², (u_a+u_b)²) > 0` but the
required `C` is graph-dependent (no universal constant). FM theory bounds `|f|`, not gradients;
there is no standard Agmon gradient estimate, and the empirical one is not robust.

## TASK 4 — Direct landscape bounds on `T`: valid but hopelessly loose

| candidate `B` | `T/B` (valid upper bd if ≤1) | `B/(λ·degQuad)` (closes if ≤1) |
|---|---|---|
| `λ²·Σ σ_v u_v²` | 0.000–0.002 (valid) | **384 – 46 698** (no) |
| `λ³·Σ d_v u_v²` | 0.000–0.25 (valid) | **0.3 – 18 782** (no) |
| `λ²·Σ σ_v u_v² f_v²` | 0.003–0.10 (valid) | **0.9 – 360** (no) |

Every landscape bound is a *valid* upper bound on `T` (huge slack, `T/B ≈ 10⁻³`) but **overshoots
`λ·degQuad` by 30×–46000×**, so none closes. The product `σ_v u_v²` is large because `σ_v` peaks on
the core while `u_v` peaks on the wells — the landscape and the triangle weight live in *different*
regions, so their product is a gross over-estimate. The best candidate (`…f_v²`) reaches `≈0.9` only
on the lollipops; it exceeds 1 everywhere else.

## TASK 5 — The Z-matrix / M-matrix structure (the substantive finding)

### `M = L + A⊙A²` is not an M-matrix
`M = D − A + A_t` has off-diagonal `t_ij − 1`, which is **positive whenever an edge lies in ≥2
triangles** — true on **15/18** graphs (max off-diagonal up to `+49` on twin50). So `M` is not even a
Z-matrix; landscape theory cannot apply to it. (`L_t` itself *is* a singular M-matrix — a weighted
Laplacian — but its landscape `L_t⁻¹·1 = 0` is degenerate, same pathology as `L`.)

### `S = ½(LD+DL) − L_t` IS a Z-matrix, and reformulates the aggregate exactly
Two facts, both verified to machine precision on all 18 graphs:

1. **Exact identity** (`id.err < 1e-13`): for the Fiedler, using `Lf = λf` and symmetry,
   `fᵀ(LD)f = ⟨Lf,Df⟩ = λ·degQuad = fᵀ(DL)f`, hence
   ```
   fᵀ S f  =  λ·degQuad  −  T.        ⇒   aggregate  T ≤ λ·degQuad   ⟺   fᵀSf ≥ 0.
   ```
2. **Z-matrix**: off-diagonal `S_ij = t_ij − (d_i+d_j)/2`, and since
   `t_ij ≤ min(d_i,d_j) − 1 < (d_i+d_j)/2`, all off-diagonals are `≤ 0` (verified 18/18).
   Diagonal `S_ii = d_i² − σ_i > 0` (since `σ_i = 2τ_i ≤ d_i(d_i−1) < d_i²`).

### …but `S` is an M-matrix (PSD) **only for regular graphs**

| graph (regular) | `S` min eig | | graph (irregular) | `S` min eig |
|---|---|---|---|---|
| K8, K20 | 0.000 | | dumbbell20 | −0.121 |
| cycle20, torus6×6 | 0.000 | | lollipop15 | −0.482 |
| Petersen | 0.000 | | deg2d60 | −6.771 |
| | | | twin50 | −7.079 |

**S is PSD on exactly the 5 regular graphs and on none of the 13 irregular graphs.** For a
`d`-regular graph `S = dL − L_t`, and `S ⪰ 0 ⟺ L_t ⪯ dL` (operator) — this is precisely the *regular*
aggregate, the case already proved in Lean (`triEnergy_le_RHS_regular`). Irregularity (`D` not
scalar) breaks the PSD property, so:

> **The aggregate does NOT reduce to "`S ⪰ 0`".** `S` is a Z-matrix but not an M-matrix; it has a
> genuine (small) negative eigencone for every irregular graph. The truth of `fᵀSf ≥ 0` is a
> property of the **specific Fiedler** `f`, which must avoid that negative cone.

This pinpoints why M-matrix / landscape *positivity* tools cannot close the problem: they would prove
`fᵀSf ≥ 0` for **all** `f`, which is false. (The companion Z-matrix `S' = ½(LD+DL) − L_t` is exactly
the "`DL+LD`" comparison; its non-PSD-ness for irregular graphs is the matrix face of the Hadamard
obstruction `A⊙A²`.)

## TASK 6 — Report

**(a) Does the landscape predict Fiedler flatness on triangle-dense regions?**
**Yes, qualitatively.** `corr(u, f²) > 0` (≤0.99) and `corr(1/u, σ) > 0` (≤0.99): the Fiedler lives
in the wells of the effective potential `1/u`, which peaks on the triangle-dense core where `f` is
flat. The landscape reproduces the known anti-correlation mechanism — but it tracks degree and
triangle density about equally (collinear), so it does not isolate a *triangle-specific* potential.

**(b) Does any landscape bound close `T ≤ 2λ·degQuad`?**
**No.** All tested landscape upper bounds are valid but loose by 30×–46000× (the triangle weight `σ`
and the landscape `u` peak in disjoint regions, so `Σσu²` over-counts). The Agmon pointwise bound is
not universally valid.

**(c) Natural M-/Z-matrix formulation connecting `L_t` to landscape theory?**
**Z-matrix yes, M-matrix no.** `S = ½(LD+DL) − L_t` is a Z-matrix with the exact identity
`fᵀSf = λ·degQuad − T`, so `aggregate ⟺ fᵀSf ≥ 0`. But `S` is PSD (an M-matrix) **iff the graph is
regular** — the already-solved case. For irregular graphs `S` has negative eigenvalues, so the
inverse-positivity / landscape machinery does not apply.

**(d) If promising: the exact theorem.**
The clean target is:

> **Theorem (equivalent form).** For the Fiedler `f` of a connected `G`,
> `fᵀ S f ≥ 0` where `S = ½(LD+DL) − L_t` (a Z-matrix).

This is *equivalent* to the aggregate and is the most matrix-natural statement, but it is **not** a
matrix-positivity fact (S is not PSD when irregular). Proving it still requires showing the Fiedler's
overlap with `S`'s negative eigenspace is non-positive — i.e. the same **eigenvector-localization /
Davis–Kahan** content. Landscape theory supplies the *qualitative* localization (f in the wells of
`1/u`, away from the high-`σ` core that carries `S`'s negativity) but no quantitative closure.

**Conclusion.** The landscape connection is real but *diagnostic*, not *probative*: it confirms and
visualizes why `T` is small (Fiedler localizes off the triangle-dense, high-potential core), and it
yields the elegant Z-matrix reformulation `aggregate ⟺ fᵀSf ≥ 0`. It does **not** provide a closing
bound, because the operative matrix `S` loses M-matrix positivity exactly at irregularity — the same
Hadamard-`A⊙A²` obstruction, now seen as "Z-matrix that fails to be an M-matrix." No new
Lean-formalizable route emerges; the open content remains global eigenvector localization.
