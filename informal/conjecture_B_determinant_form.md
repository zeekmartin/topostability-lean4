# Conjecture B — the determinant `det(M_low)` decomposed

From [`conjecture_B_spectral_orthogonality.md`](conjecture_B_spectral_orthogonality.md): B ⟺ the
2×2 low-frequency block of `M = λ₂Q − L_M` (`Q = D+A`) is PSD, i.e.

> `det(M_low) = (4λ₂/n)·(m·fᵀMf − λ₂S²) ≥ 0`,  `S = Σ_v d_v f_v`, `m = |E|`.

This note decomposes `D := m·fᵀMf − λ₂S²`. Code:
[`conjecture_B_determinant_form.py`](../conjecture_B_determinant_form.py), 580 graphs, all residuals
machine-zero.

---

## The decomposition:  `D = λ₂·G − m·T`

Using `fᵀMf = λ₂·fᵀQf − T` (`T` = triangle energy, `fᵀQf = 2fᵀDf − λ₂`) and the **edge-lift**
`h = Bᵀf` (unsigned incidence `B`), `h_e = f_a + f_b` for `e = {a,b}`:

| exact identity | residual |
|---|---|
| `fᵀQf = Σ_e (f_a+f_b)²` (signless-Laplacian QF) | `9·10⁻¹⁴` |
| `⟨1_E, h⟩ = Σ_e (f_a+f_b) = Σ_v d_v f_v = S` | `1·10⁻¹³` |
| `G := m·fᵀQf − S² = m‖h‖² − ⟨1_E,h⟩² = Gram(h, 1_E)` | `6·10⁻¹⁰` |
| `G = ½ Σ_{e,e'}(h_e − h_{e'})²` (Lagrange) `= m²·Var_E(h)` | `7·10⁻¹²` |
| **`D = m·fᵀMf − λ₂S² = λ₂·G − m·T`** | `5·10⁻⁹` |

So

> **`D = λ₂·G − m·T`**, where `G = Gram(h, 1_E) = m²·Var_E(f_a+f_b) = ½Σ_{e,e'}(h_e−h_{e'})² ≥ 0`
> (Cauchy–Schwarz / Lagrange), and `T ≥ 0` is the triangle energy.

`G` is the **manifestly nonnegative** Cauchy–Schwarz / Gram-determinant term — the *variance of the
edge-lift* `h_e = f_a + f_b` over the `m` edges. Conjecture B is

> **`λ₂·G ≥ m·T`**, i.e. `T ≤ λ₂(fᵀQf − S²/m) = λ₂‖h_⊥‖²` (the projected lift bound).

## Is `D` a single covariance determinant `Var·Var − Cov²`?

**No.** `D` is `λ₂·(one Cauchy–Schwarz/variance determinant) − m·(triangle energy)`:

- the **Gram/variance part** `λ₂·G` is a genuine Cauchy–Schwarz determinant `m‖h‖² − ⟨1_E,h⟩²` of
  the edge-lift `h` against the constant `1_E` — manifestly `≥ 0` (Lagrange SOS, formalised below);
- but the **triangle energy** `m·T` is *subtracted*, not a second variance. There is no second vector
  whose Gram with `h` produces `−m·T`; `T = Σ_{ab∈E} t_ab(f_a−f_b)²` lives on the *triangle*
  (Hadamard) structure, orthogonal to the simple `{h, 1_E}` Gram.

So the determinant is **not** of the clean form `Var(X)Var(Y) − Cov(X,Y)²`. The manifestly-positive
content is the edge-lift variance `λ₂·G`; the obstruction is exactly the triangle energy eating into
it.

## Numerics: the margin

| quantity | value |
|---|---|
| `G` (Cauchy–Schwarz/variance, `≥0`) | min `24.6`, all `≥0` (`580/580`) |
| `D = λ₂·G − m·T` | min `6.57`, all `≥0` (`580/580`) |
| `m·T / (λ₂·G)` (must be `≤1`) | min `0`, median `0.249`, **max `0.829`** |

In this form the conjecture has a **healthy margin**: the triangle energy never exceeds `83%` of the
spectral edge-lift variance (`17%` slack at the tightest graph). The triangle energy `m·T` is
typically only `~25%` of `λ₂·G`.

## What this buys (and the remaining gap)

- The **Cauchy–Schwarz / Lagrange** structure `G ≥ 0` is now explicit and formalised: the
  edge-lift `h_e = f_a + f_b` has nonnegative variance, and `λ₂·G` is the spectral budget.
- The conjecture reduces to a **single scalar comparison** `m·T ≤ λ₂·G`, i.e. the triangle energy is
  bounded by `λ₂` times the edge-lift variance. Both sides are concrete: `T = Σ_{ab}t_ab(f_a−f_b)²`,
  `G = ½Σ_{e,e'}((f_a+f_b)−(f_{a'}+f_{b'}))²`.
- The gap is the same irreducible one: `T` (triangle/Hadamard energy) vs the edge-lift variance.
  No further SOS makes `λ₂G − mT` manifestly nonnegative — it is the projected lift Rayleigh bound
  `T ≤ λ₂‖h_⊥‖²`, which still requires the specific Fiedler direction (cf.
  [`conjecture_B_spectral_orthogonality.md`](conjecture_B_spectral_orthogonality.md)).

## Conclusion

`det(M_low) = (4λ₂/n)(λ₂·G − m·T)` with `G = m²·Var_E(f_a+f_b) = ½Σ_{e,e'}(h_e−h_{e'})²` a manifest
Cauchy–Schwarz/Gram determinant and `m·T` the triangle energy. The determinant is **`λ₂·(variance)
− (triangle energy)`, not a single `Var·Var − Cov²`**. The variance part is unconditionally
nonnegative (formalised via the Lagrange identity); the conjecture is the clean scalar bound
`m·T ≤ λ₂·G` (margin ≥ 17%), whose proof is the still-open `T ≤ λ₂‖h_⊥‖²`.

## Formalised (Lean, `ConjectureB.lean`, no `sorry`)
- `lagrange_identity` — `(Σ aᵢ²)(Σ bᵢ²) − (Σ aᵢbᵢ)² = ½ Σ_{i,j}(aᵢbⱼ − aⱼbᵢ)²` (generic, any
  `a,b : ι → ℝ`): the Gram determinant as a manifest sum of squares. Specialising `a = h`, `b = 1`
  gives `G = m·fᵀQf − S² = ½Σ_{e,e'}(h_e−h_{e'})² ≥ 0`, the nonnegative part of `det(M_low)`.
  (The identity `D = λ₂·G − m·T` itself is immediate algebra from `fᵀMf = λ₂fᵀQf − T`; `⟨1_E,h⟩ = S`
  is `adjMatrix_mulVec_sum`.)
