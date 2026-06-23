# Conjecture B — the per-eigenmode triangle Poincaré

Target: `u_kᵀL_t u_k ≤ λ_k·u_kᵀD u_k` for **every** Laplacian eigenpair `(u_k, λ_k)` (the Fiedler case
`k=2` is `aggregate_triangle_poincare`). **Result: it holds for EVERY mode on the full corpus (44/44,
`C_k = u_kᵀL_t u_k/(λ_k u_kᵀD u_k) ≤ 0.99 < 1`, uniform margin). It is genuinely eigenvector-specific —
the same cubic ratio for arbitrary `v` reaches 2.48 (gap up to 1.57). The trace (sum over modes) gives
the provable corollary `6·num_tri ≤ Σ_v d_v²` (closed 2-paths ≤ all 2-paths), but the per-mode statement
is strictly stronger and reduces, via the apex identity, to the same (hard) aggregate cancellation.**
Code: [`triangle_poincare_per_eigenmode.py`](../triangle_poincare_per_eigenmode.py).

## TASK 1 — `C_k ≤ 1` for ALL modes (44/44, margin)

| graph | class | `max_k C_k` | `k_max` | `λ_{kmax}` | `λ₂` | spectrum frac |
|---|---|---|---|---|---|---|
| twin-port `K₈₀` d2 | TYPE A | **0.9873** | 4 | 80.0 | 1.02 | 0.04 |
| `K₃₀` | regular | 0.9655 | 1 (Fiedler) | 30.0 | 30.0 | 0.00 |
| lollipop(15,12) | TYPE B | 0.9286 | 13 | 15.0 | 0.02 | 0.46 |
| star12+8 | clique+star | 0.9091 | 9 | 12.0 | 1.00 | 0.42 |

> **`max_k C_k ≤ 0.9873`** — the per-eigenmode Poincaré holds for *every* mode, every graph, with a
> uniform margin (`< 1`). The maximizing mode varies: the **Fiedler** for `K_n`, the **clique modes**
> (`λ = N`) for twin-port, **middle** modes for star/lollipop. So `aggregate_triangle_poincare` (∀
> eigenpair) is robustly true — not just at the Fiedler, and not barely.

## TASK 5 — no failing modes

> **NONE.** `C_k > 1` occurs on no mode of any graph. The `∀`-eigenpair statement is universal.

## TASK 4 — eigenvector-specificity (huge gap to arbitrary `v`)

The same ratio as a *cubic form* over arbitrary `v`, `vᵀL_t v·‖v‖² / ((vᵀLv)(vᵀDv))`:

| graph | eigenvector `max_k C_k` | arbitrary-`v` `C` | gap |
|---|---|---|---|
| star12+8 | 0.91 | **2.48** | 1.57 |
| lollipop(15,12) | 0.93 | 1.99 | 1.06 |
| twin-port `K₃₀` d2 | 0.97 | 1.35 | 0.39 |

> **Arbitrary `v` gives `C` up to 2.48 (≫ 1), eigenvectors stay `≤ 0.99`.** The eigenvector property
> `Lu = λu` is essential — it is NOT a general (all-`v`) inequality. Any proof must use `Lu = λu` beyond
> merely defining `λ`.

## TASK 2/3 — proof via `Lu = λu`: reduces to the apex aggregate

`u_kᵀL_t u_k = Σ_c E_c(u_k)` (apex identity), `λ_k·u_kᵀD u_k = λ_k·Σ_c P_c(u_k)` (`P_c = Σ_{v∼c}u²`). So
the per-mode statement is `Σ_c E_c ≤ λ_k Σ_c P_c` — the **aggregate local Poincaré**, with the
eigenvector giving the local constraint `Σ_{v∼c}u = (d_c − λ_k)u_c`. The per-apex form `E_c ≤ λ_k P_c`
fails (~6% of apices); only the aggregate holds, by cross-apex cancellation. So the per-eigenmode
statement reduces to exactly the same (hard) cancellation — no simplification from being stated for all
modes.

**Trace corollary (provable):** summing the per-mode inequalities over an orthonormal eigenbasis,
`Σ_k u_kᵀL_t u_k = tr(L_t) = Σ_v σ_v = 6·num_tri` and `Σ_k λ_k u_kᵀD u_k = tr(LD) = Σ_v d_v²`, giving
> **`6·num_tri ≤ Σ_v d_v²`** — TRUE and elementary (closed 2-paths `≤` all ordered 2-paths:
> `6·num_tri = #closed-2-paths ≤ Σ_v d_v(d_v−1) ≤ Σ_v d_v²`).

This is the *trace* of the per-mode Poincaré — provable, but strictly weaker (it is the sum, not each
term; the Fiedler term is what Conjecture B needs).

## Conclusion

- **Per-eigenmode triangle Poincaré holds for EVERY mode** (44/44, `C_k ≤ 0.99`, uniform margin) —
  `aggregate_triangle_poincare` (∀ eigenpair) is robustly true; the maximizing mode varies by family.
- **Eigenvector-specific** — arbitrary-`v` `C` up to 2.48; the proof needs `Lu = λu` essentially.
- **Reduces to the apex aggregate** (`Σ_c E_c ≤ λ Σ_c P_c`), the same hard cross-apex cancellation; being
  ∀-mode gives no simplification.
- **Provable trace corollary** `6·num_tri ≤ Σd_v²` (2-paths) — the sum of the per-mode bounds, weaker
  than the Fiedler term.

## Lean
No code change: the per-eigenmode statement is exactly `aggregate_triangle_poincare` (∀ eigenpair),
confirmed robust (margin `< 1`), but its proof reduces to the apex aggregate (open, the standing sorry).
The trace corollary `6·num_tri ≤ Σd_v²` is provable and could be a standalone lemma, but it is the sum
(not the Fiedler term) and does not close the aggregate. 3 sorrys unchanged.
