# Conjecture B — spectral separation: why the Fiedler avoids M's negative cone

`M = λ₂(D+A) − L_t = λ₂Q − L_M` (`Q = D+A` signless Laplacian, `L_M` triangle Laplacian).
`fᵀMf = 2λ₂fᵀDf − λ₂² − T`. `M` is indefinite, yet `fᵀMf ≥ 0` and the Fiedler `f = u₂` (with
`Lf = λ₂f`, `u₁ = const`) sits in `M`'s positive part. **Why?** Code:
[`conjecture_B_spectral_orthogonality.py`](../conjecture_B_spectral_orthogonality.py), 580 graphs.

**Headline.** It is *not* that `f` is orthogonal to `M`'s negative eigenspace (it is not — `f` keeps
up to 25% of its mass there). The exact reason is **block-diagonal**:

> **Conjecture B ⟺ the 2×2 low-frequency block of `M` in `{u₁=const, u₂=f}` is PSD** (`580/580`).

---

## TASK 1 — M's negative eigenvectors are (mostly) high-frequency

Writing each `M`-eigenvector `w_j` (`μ_j < 0`) in `L`'s eigenbasis `{u_k}`:

| quantity | value |
|---|---|
| `max_j |⟨w_j, u₂⟩|²` (overlap with Fiedler) | median `7·10⁻⁴`, **max `0.205`** |
| `min_j` high-freq mass `Σ_{k≥3}|⟨w_j,u_k⟩|²` | median `0.9987`, min `0.778` |
| `‖P_{V⁻} u₂‖²` (Fiedler mass in `M`'s negative subspace) | median `0.0026`, **max `0.255`** |
| graphs with `‖P_{V⁻}u₂‖² < 0.01` | `396/580` |

So `V⁻(M)` is **approximately** high-frequency (median 99.9% in `span{u₃,…,u_n}`), and on `396/580`
graphs `f` is essentially orthogonal to it. **But the hypothesis `V⁻(M) ⊥ u₂` is not exact** — on the
hard/near-tight graphs `f` carries up to `25%` of its mass in `V⁻(M)`.

## TASK 2 — the 2×2 Fiedler block: B is its positive-semidefiniteness  ⭐

The low-frequency block `M_low = [[⟨u₁,Mu₁⟩, ⟨u₁,Mu₂⟩],[⟨u₂,Mu₁⟩, ⟨u₂,Mu₂⟩]]` has exact entries
(residuals `≤7·10⁻¹²`):

> `⟨u₁,Mu₁⟩ = λ₂⟨u₁,Qu₁⟩ = λ₂·4m/n` (since `L_M u₁ = 0`);
> `⟨u₁,Mu₂⟩ = λ₂·2S/√n` (`S = Σ_v d_v f_v`, from `1ᵀ(D+A)f = 2S`);
> `⟨u₂,Mu₂⟩ = fᵀMf = 2λ₂fᵀDf − λ₂² − T`.

Hence `det(M_low) = (4λ₂/n)(m·fᵀMf − λ₂S²)`, so

> **`M_low ⪰ 0 ⟺ fᵀMf ≥ λ₂S²/m ⟺ T ≤ λ₂(fᵀQf − S²/m) = ` lift-B.**

Verified: `M_low PSD ⟺ lift-B`, **agree `580/580`**, `det(M_low)` min `0.018 > 0`. **The off-diagonal
coupling `⟨u₁,Mu₂⟩ = λ₂·2S/√n` between the constant and the Fiedler is exactly the source of the
`S²/m` correction** — the term that distinguishes the projected lift bound from the naïve
`fᵀMf ≥ 0`. Conjecture B is precisely the statement that this 2×2 block is positive-semidefinite.

## TASK 3 — `V⁻(M) ⊥ u₂` is false; positivity is a weighted balance

`f` *does* overlap `M`'s negative modes (`‖P_{V⁻}u₂‖²` median `0.0026`, nonzero). Decomposing
`fᵀMf = Σ_j μ_j|⟨f,w_j⟩|²`:

| | value |
|---|---|
| negative-mode contribution `Σ_{μ_j<0} μ_j|⟨f,w_j⟩|²` | median `−0.20`, min `−2.35` |
| positive-mode contribution | median `+4.47` |
| ratio `|neg|/pos` | median `0.031` |

The negative contribution is real but small (~3% of the positive). **Positivity of `fᵀMf` is a
weighted cancellation, not orthogonality** — so a clean proof must use the 2×2 block (TASK 2), not an
`V⁻(M) ⊥ u₂` claim.

## TASK 4 — M is deeply indefinite (no interlacing shortcut)

| quantity | value |
|---|---|
| `#` negative eigenvalues of `M` | min `0`, median `23`, max `158` |
| `#` positive eigenvalues | min `2`, median `4`, max `44` |
| `#neg = n−2` (only the 2 low modes nonneg) | `246/580` |
| `μ₂(M)` (2nd-smallest) | min `−6240`, median `−214` |
| graphs with `μ₂(M) ≥ 0` (`M` has `≤1` negative eig) | `2/580` |

`M = λ₂Q − L_M` is a difference of PSD matrices and is **massively indefinite** — typically `n−2`
negative eigenvalues (so only the 2 low-frequency modes carry the positive part on `246/580`). The
Weyl bound `μ₂(M) ≥ 0` is **false** (`2/580`): interlacing does *not* limit `M` to few negatives. So
B is *not* explained by "M has few negative eigenvalues"; the positive part is exactly the 2-dim
low-frequency block, and B is that block's PSD-ness.

## Conclusion

- The intuition "`f = u₂` avoids `M`'s negative cone because `V⁻(M)` is high-frequency" is
  **approximately right** (median 99.9% high-freq) but **not exact and not the proof** — `f` keeps up
  to 25% of its mass in `V⁻(M)`, and positivity is a weighted balance (TASK 1, 3).
- The **exact** statement is structural: **B ⟺ the 2×2 low-frequency block `M_low` (in
  `{const, Fiedler}`) is PSD** (TASK 2, `580/580`). The `det` condition is `m·fᵀMf ≥ λ₂S²`, and the
  `S²` comes precisely from the constant↔Fiedler off-diagonal `⟨u₁,Mu₂⟩ = λ₂·2S/√n`.
- `M` is deeply indefinite (median 23 negatives); no Weyl/interlacing argument bounds the negatives
  (TASK 4). The conjecture lives entirely in the 2-dimensional low-frequency block.

This reframes the open problem as a **2×2 PSD** condition: prove `det(M_low) = (4λ₂/n)(m·fᵀMf − λ₂S²)
≥ 0` for the Fiedler, i.e. the constant–Fiedler coupling `S` never overwhelms the diagonal product
`(λ₂·4m/n)·(fᵀMf)`. The diagonal `fᵀMf = 2λ₂fᵀDf − λ₂² − T` is the (still open) bottleneck.

## Formalised (Lean, `ConjectureB.lean`, no `sorry`)
- `adjMatrix_mulVec_sum` — `Σ_v (A f)_v = Σ_v d_v f_v` (`1ᵀAf = S`, weighted handshake). With
  `1ᵀDf = S` this gives `1ᵀ(D+A)f = 2S`, the off-diagonal block entry `⟨u₁,Mu₂⟩ = λ₂·2S/√n` that
  produces the `S²/m` correction. (The diagonal entries `⟨u₁,Mu₁⟩ = λ₂⟨u₁,Qu₁⟩` and `⟨u₂,Mu₂⟩ =
  fᵀMf` follow from `L_M·1 = 0` and `quadForm_adjMatrix_fiedler`/`triEnergy`.)
