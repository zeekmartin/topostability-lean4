# Conjecture B — `L_t` in the Laplacian eigenbasis: the λ-free slack matrix `S`

Study `L_t` in the Laplacian eigenbasis `U`. **Result: the per-mode inequality `B_kk ≤ λ_k H_kk`
(`B = UᵀL_tU`, `H = UᵀDU`) is the diagonal of a λ-FREE matrix `S = ½(LD+DL) − L_t` with EXACT explicit
structure (`S_ii = d_i²−σ_i`, `S_ij = t_ij−(d_i+d_j)/2` on edges, `0` off the graph), and
`u_kᵀS u_k = λ_k H_kk − B_kk` (the per-mode slack, all modes at once). `S` is NOT globally PSD (Schur
fails, 4/19) but has a LOW-RANK negative part (1–2 eigenvalues), localized on the low-degree ports —
vastly cleaner than `Q = λD−L_t` (many negatives). `B` is nearly diagonal in the L-basis (off/diag ≤
0.037), i.e. `L_t` nearly commutes with `L`.** Code:
[`triangle_poincare_eigenbasis_diagonal.py`](../triangle_poincare_eigenbasis_diagonal.py).

## TASK 2 — the exact λ-free slack identity

Since `UᵀL = ΛUᵀ`, `λ_k H_kk = (Uᵀ·½(LD+DL)·U)_kk`. So with **`S := ½(LD+DL) − L_t`**:

> **`u_kᵀ S u_k = λ_k·u_kᵀD u_k − u_kᵀL_t u_k`** (the per-mode slack), for *every* eigenmode at once.
> `S` is λ-free with explicit structure (verified, err `0`):
> `S_ii = d_i² − σ_i`, `S_ij = t_ij − (d_i+d_j)/2` (edges `i∼j`), `S_ij = 0` (non-edges).

As a vertex+edge sum, the aggregate slack at an eigenvector `u` (`Lu = λu`) is:

> **`λ·uᵀD u − uᵀL_t u = Σ_v (d_v²−σ_v)u_v² + 2·Σ_{e=(a,b)} (t_e − (d_a+d_b)/2)·u_a u_b`**

— positive vertex part (`d_v² − σ_v ≥ d_v > 0`, since `σ_v = 2·#tri ≤ d_v(d_v−1)`), negative edge part
(`t_e < (d_a+d_b)/2`). The aggregate ⟺ vertex part dominates the (negative) edge part *on eigenvectors*.

## TASK 1 — diagonal holds; `B` nearly diagonal in L-basis

| graph | `max_k B_kk/(λ_k H_kk)` | `‖off B‖/‖diag B‖` |
|---|---|---|
| twin-port `K₅₀` d2 | 0.980 | **0.008** |
| lollipop(15,12) | 0.929 | 0.027 |
| deg2+dense(40,.9) | 0.870 | 0.037 |

> Per-mode diag ratio ≤ 0.98 (19/19, margin). **`B = UᵀL_tU` is nearly diagonal** (off-diagonal ≤ 3.7%
> of the diagonal) — `L_t` *nearly commutes* with `L`. The arbitrary-vector violations (`C` up to 2.48)
> come from these small off-diagonals amplified by the `H`-weighting / Rayleigh cross-terms.

## TASK 3 — trace vs diagonal

Trace of the slack identity: `tr(S) = Σ_v(d_v²−σ_v) = Σd_v² − Σσ_v = Σd_v² − 6·num_tri ≥ 0` (the
2-path corollary). This is the *sum* of the per-mode slacks `Σ_k u_kᵀS u_k = tr(S)`. The
diagonal-by-diagonal `u_kᵀS u_k ≥ 0` is strictly stronger (the Fiedler term is what Conjecture B needs).

## TASK 4 — `S` is not globally PSD, but has a LOW-RANK negative

| graph | min eig `S` | `#neg S` | `w` low-degree conc. | diag-dom. `d²≥s` fails |
|---|---|---|---|---|
| deg2+dense(60,.9) | −13.7 | **1** | 0.49 | 32 |
| twin-port `K₅₀` d3 | −10.2 | **1** | **0.94** | 50 |
| twin-port `K₈₀` d2 | −7.6 | **1** | **0.96** | 51 |
| lollipop(15,12) | — | **2** | 0.42 | — |

> **`S ⪰ 0` globally only 4/19 — but the negative part is LOW-RANK (1, occasionally 2, eigenvalues).**
> The negative direction(s) `w` are concentrated on the **low-degree ports** (`w` low-deg mass up to 0.96
> for twin). Diagonal dominance `d_v² ≥ s_v` (`s_v` = neighbour-degree sum) fails exactly at the
> low-degree vertices (the ports: `d² = 4` but `s` huge). So the Schur product theorem does NOT apply
> (`A⊙A²` with `A` indefinite), and `S` is indefinite — but with a *tiny* (rank ≤ 2) negative cone
> localized at the bottleneck. This is far cleaner than `Q = λD − L_t` (which has `O(n)` negatives).

## TASK 5 — the Lean target

`triangle_poincare_eigenmode : Lu = λu → uᵀL_t u ≤ λ·uᵀD u` **is exactly `aggregate_triangle_poincare`**
(`triEnergy = 2·uᵀL_t u`, `degQuad = uᵀD u`, so `triEnergy ≤ 2λ·degQuad ⟺ uᵀL_t u ≤ λ·uᵀD u`). The new
structure gives the cleanest equivalent:

> **`aggregate_triangle_poincare ⟺ S ⪰ 0 on each Laplacian eigenspace`**, where `S = ½(LD+DL) − L_t` is
> the λ-free matrix `S_ii = d_i²−σ_i`, `S_ij = t_ij−(d_i+d_j)/2` (edges), `0` else — with a rank-≤2
> port-localized negative part. The aggregate is the statement that each eigenmode (in particular the
> Fiedler) dominates this tiny negative cone.

## Conclusion

- **λ-free slack matrix:** `S = ½(LD+DL) − L_t`, `u_kᵀS u_k = λ_k H_kk − B_kk`; explicit structure
  (`d²−σ` diag, `t−(d+d)/2` edges). Slack `= Σ_v(d²−σ)u² + 2Σ_e(t−(d+d)/2)u_a u_b`.
- **Low-rank negative:** `S` has 1–2 negative eigenvalues, port-localized (vs `O(n)` for `Q`); diag-dom
  fails only at low-degree ports. `B` nearly diagonal in L-basis (`L_t ≈` commutes with `L`).
- **Aggregate ⟺ `S ⪰ 0` on eigenspaces** — each eigenmode dominates the rank-≤2 port-localized negative
  cone. The cleanest operator reformulation yet (λ-free, low-rank, explicit).

## Lean
No code change: `triangle_poincare_eigenmode` = `aggregate_triangle_poincare` (same statement). The new
λ-free matrix `S` (explicit, rank-≤2 negative) is the cleanest equivalent of the open sorry — a candidate
for a future proof via the low-rank/port-localized negative structure. 3 sorrys unchanged.
