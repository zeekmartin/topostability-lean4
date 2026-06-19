# Conjecture B — the open-2-path operator P analysed directly

`P_ab = #common neighbours of a,b` for `a≁b, a≠b` (induced cherries); `A² = D + M + P`
(`M = A∘A²` triangle/closed 2-paths). `L_P = diag(p) − P`, `p_v = σ_v − d_v − τ_v`, `Open = fᵀL_P f`.
Conjecture (`= −Q ≥ 0`): `fᵀ(L_P − diag(R))f ≥ 0` for the Fiedler `f`, with
`R_v = (σ_v − d_v²) + λ₂(d_v − λ₂)`. Code:
[`conjecture_B_open2path_operator.py`](../conjecture_B_open2path_operator.py), 580 graphs.

---

## TASK 1 — spectrum of L_P

| quantity | value |
|---|---|
| `P`-graph connected (`dim ker L_P = 1`) | `455/580`; disconnected (`>1`) on `125` |
| `f`-mass in `ker L_P` (`‖proj_ker f‖`) | median `0`, **max `0.976`** |
| `λ₂(L_P)` (smallest nonzero) | min `0.020`, median `14.6` |
| **`Open ≥ λ₂(L_P)·‖f_⊥‖²`** (Rayleigh floor) | **`580/580`**, `Open/λ₂(L_P)` median `1.46` |
| `corr(λ₂(L_P), λ₂(G))` | `+0.48` |

Since `f ⊥ 1` and `1 ∈ ker L_P`, the Rayleigh floor `Open ≥ λ₂(L_P)·‖f_⊥‖²` is exact and always
holds. **But the floor is too weak to close the conjecture:**

| spectral-route test | holds |
|---|---|
| `λ₂(L_P) ≥ Σ_v R_v f_v²` (⇒ `Open ≥ λ₂(L_P) ≥ ΣRf²`) | `349/580` |
| `λ₂(L_P) ≥ max_v R_v` (stronger) | `1/580` |

So `Open` clears `λ₂(L_P)`, but `λ₂(L_P)` dominates the `R`-demand only ~60% of the time. On `125`
graphs `P` is disconnected and `f` carries kernel mass (max `0.976`) — there the floor degrades
further. **The spectral floor of `L_P` alone cannot prove the conjecture.**

## TASK 2 — is `L_P − diag(R)` PSD? (no fixed-operator certificate)

| subspace | PSD count | note |
|---|---|---|
| global (all `g`) | **`0/580`** | `λ_min` median `−22.3` |
| `1⊥` (all `g ⊥ 1`) | `323/580` | `λ_min` on `1⊥` down to `−38.7` |
| nodal `V+` submatrix | `105/580` | |
| nodal `V−` submatrix | `81/580` | |
| `(R≥0)` submatrix (drop neg-`R` hubs) | **`7/580`** | dropping hubs makes it *worse* |
| **at the Fiedler `f`: `fᵀ(L_P−diag R)f = −Q ≥ 0`** | **`580/580`** | the conjecture |

`L_P − diag(R)` is **never** globally PSD, and **fails on `1⊥` for 44%** of graphs — so the
conjecture is *not* a subspace-PSD fact; it holds specifically in the **Fiedler direction**.
Dropping the negative-`R` hubs collapses PSD-ness (`7/580`), re-confirming that the negative hub
diagonal is load-bearing (it *adds* positivity to `L_P − diag(R)`).

## TASK 3 — incidence factorisation: Open is a manifest sum of squares

Exact (residual `5·10⁻¹³`):

> **`Open = Σ_{a<b} P_ab (f_a − f_b)² = ‖B_open f‖²`**, `L_P = B_openᵀ B_open`,

with one row of `B_open` per open cherry `(a,c,b)` (`+1` at `a`, `−1` at `b`). This is the general
**weighted-Laplacian SOS** for the symmetric weight `P` (formalised below). The obstruction is the
*comparison*: `diag(R)` is sign-indefinite (`R_v < 0` on hubs), while `B_openᵀB_open` is PSD, so a
term-wise "Gram ≥ diagonal" fails — even the per-vertex `open-degree p_v ≥ R_v⁺` holds on only
`224/580`. The open-cherry support and the `R`-demand are not aligned vertex-wise.

## TASK 4 — the A² recursion on non-edges (reproduces −Q, circular)

Exact identities (residuals `≤8·10⁻¹³`):

> `A²f = A D f − λ₂(D f − λ₂ f)` (`adjSq_mulVec_fiedler`);
> **`(Pf)_v = (ADf)_v − λ₂(d_v−λ₂)f_v − d_v f_v − (Mf)_v`** (new entrywise open-operator recursion);
> `fᵀP f = fᵀADf − λ₂(fᵀDf − λ₂) − fᵀDf − fᵀMf`.

The recursion pins `fᵀPf` exactly, but `Open = p·f² − fᵀPf` re-introduces the open-degree diagonal
`p·f²`, and the projection onto non-edges only reproduces `−Q` — circular, no new sign structure
(same lesson as the global summation-by-parts round).

## Conclusion

Analysing `P` directly sharpens, but does not break, the obstruction:

- **Spectral:** `Open ≥ λ₂(L_P)·‖f_⊥‖²` is exact, but `λ₂(L_P)` dominates the `R`-demand only
  `349/580` — the open-2-path connectivity floor is too weak (and `P` is disconnected on `125`).
- **Operator:** `L_P − diag(R)` is PSD on `0/580` (global) and `323/580` (`1⊥`); the conjecture is a
  **Fiedler-direction** statement, not a subspace-PSD fact, and the negative-`R` hubs are essential.
- **SOS:** `Open = ‖B_open f‖²` exactly (formalised general lemma), but `diag(R)`'s indefiniteness
  blocks a Gram-vs-diagonal comparison; supports are vertex-wise misaligned.
- **Recursion:** the `A²` non-edge projection fixes `fᵀPf` but only reproduces `−Q`.

The open-2-path operator is the right home for the conjecture (it sees the distance-2 endpoint pairs
that `Γ₂` missed), but closing it needs to exploit the **specific Fiedler direction** against the
*signed* `diag(R)` — the floor `λ₂(L_P)` and any fixed-operator/subspace PSD certificate are
provably insufficient.

## Formalised (Lean, `ConjectureB.lean`, no `sorry`)
- `quadForm_weighted_laplacian` — for symmetric `W`, `Σ_{i,j} W_ij (f_i−f_j)² = 2[Σ_i(Σ_j W_ij)f_i²
  − Σ_{i,j} W_ij f_i f_j]` (the weighted-Laplacian SOS). Specialising `W = P` gives
  `Open = ‖B_open f‖²`; specialising `W = A²` gives the 2-path energy `T + Open`. No spectral
  hypothesis. (The entrywise `(Pf)` recursion of TASK 4 is `adjSq_mulVec_fiedler` minus the diagonal
  `D` and Hadamard `M` parts — already covered by the existing recursion lemma.)
