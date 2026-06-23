# Conjecture B — vertex-edge decomposition of the λ-free slack matrix `S`

Decompose `uᵀS u` (`S = ½(LD+DL) − L_t`) into positive diagonal + negative edge parts and apply the
eigenvector equation. **Result: the decomposition is EXACT and yields the clean identity
`Σ_{edges}(d_i+d_j)u_iu_j = Σd²u² − λ·degQuad` (via `Au = (D−λ)u`), isolating the triangle term. But
recombining gives `Slack = λ·degQuad − T_unord` (circular — the aggregate), where `T_unord = uᵀL_t u =
Σ_e t_e g²` is manifestly SOS. The slack is an SOS *subtracted* from `λ·degQuad` — NOT itself an SOS — so
there is no sum-of-squares certificate and no smaller residual. `Pos` dominates `Edge` (ratio `|Edge|/Pos`
≤ 0.98, tight at lollipop), but that is just `Slack ≥ 0` restated.** Code:
[`slack_matrix_vertex_edge_decomposition.py`](../slack_matrix_vertex_edge_decomposition.py).

## TASK 2 — the eigenvector identity (clean, the one new piece)

`Σ_{edges}(d_i+d_j)u_iu_j = Σ_i d_i u_i·(Au)_i` (each edge contributes `d_i u_iu_j + d_j u_iu_j`, summed =
`Σ_i d_i u_i Σ_{j∼i}u_j`). With `Au = (D−λ)u`, i.e. `Σ_{j∼i}u_j = (d_i−λ)u_i`:

> **`Σ_{edges}(d_i+d_j)u_iu_j = Σ_i d_i(d_i−λ)u_i² = Σd_i²u_i² − λ·degQuad`** (verified, err `< 10⁻⁹`).

This puts the *degree* part of the edge term in closed form — it is fully controlled by `Au=(D−λ)u`. The
only remaining edge contribution is the **triangle term** `2Σ_{edges}t_ij u_iu_j = uᵀB u` (`B = A²⊙A`).

## TASK 1 — Pos / Edge / Slack

`Pos = Σ_v(d_v²−σ_v)u_v² ≥ 0`, `Edge = 2Σ_{edges}(t_ij−(d_i+d_j)/2)u_iu_j`, `Slack = Pos + Edge`:

| graph | `Pos` (Fiedler) | `Edge` | `Slack` | `|Edge|/Pos` | max ratio |
|---|---|---|---|---|---|
| `K₂₀` | 19.0 | **+1.0** | 20.0 | 0 | 0 |
| gnp(40,.6) | 179.0 | −29.6 | 149.4 | 0.17 | 0.18 |
| twin-port `K₅₀` d2 | 7.3 | −4.4 | 2.88 | 0.60 | 0.60 |
| **lollipop(15,12)** | 7.4 | −7.3 | **0.14** | **0.98** | 0.98 |

> `Pos` dominates `Edge` everywhere (`Slack ≥ 0`); `K_n` even has `Edge > 0`. The tight case is
> **lollipop** (`|Edge|/Pos = 0.98`, `Slack = 0.14`). But this ratio is just `Slack ≥ 0` restated — no
> independent bound.

## TASK 3 — triangle term and SOS structure

`T_unord = Σ_v σ_v u_v² − 2Σ_{edges}t_ij u_iu_j = uᵀ(diag(σ) − B)u = uᵀL_t u` (verified). And
`uᵀL_t u = ½Σ_{i,j}B_ij(u_i−u_j)² = Σ_e t_e (u_a−u_b)²` is **manifestly a sum of squares** (`≥ 0`,
nonneg terms). Combining with TASK 2:

> **`Slack = Pos + Edge = λ·degQuad − T_unord`** (verified) — back to the aggregate. The vertex-edge
> decomposition is exact but circular: the degree part cancels (`Au=(D−λ)u`), leaving `λ·degQuad − T`.

## TASK 4/5 — no SOS, no smaller residual

`T_unord = Σ_e t_e g²` is SOS, so `Slack = λ·degQuad − T_unord` is an SOS **subtracted** from
`λ·degQuad`. A difference `(positive) − (SOS)` is *not* generally an SOS (the eigenvector-specificity:
for arbitrary `v` the cubic form `> 1`). The residual is exactly `T_unord ≤ λ·degQuad` — the aggregate
itself, with `T/(λ·degQuad) ≤ 0.98` (lollipop), no smaller piece to isolate.

## Conclusion

- **Exact decomposition + clean identity:** `Σ_{edges}(d_i+d_j)u_iu_j = Σd²u² − λ·degQuad` (eigenvector,
  Lean-provable) puts the degree-edge term in closed form, isolating the triangle term `uᵀB u`.
- **But circular:** `Slack = λ·degQuad − T_unord` (the aggregate); `Pos` dominates `Edge` (ratio ≤ 0.98)
  is just `Slack ≥ 0` restated.
- **No SOS** for the slack (it is `positive − SOS`, eigenvector-specific); **no smaller residual** than
  `T ≤ λ·degQuad`.
- The triangle term `T = Σ_e t_e g²` (itself SOS) is the irreducible object; the decomposition cleanly
  separates the controllable degree part from it but cannot bound it.

## Lean
No code change: the vertex-edge decomposition is exact but circular. The clean identity
`Σ_{edges}(d_i+d_j)u_iu_j = Σd²u² − λ·degQuad` is Lean-provable (via `Au=(D−λ)u`) and could be a helper,
but the residual is the full aggregate (`T ≤ λ·degQuad`), which has no SOS / smaller form.
`aggregate_triangle_poincare` stays the direct sorry. 3 sorrys unchanged.
