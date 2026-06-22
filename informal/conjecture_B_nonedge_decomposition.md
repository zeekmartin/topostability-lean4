# Conjecture B — non-edge / complement decomposition of `gap = λ₂G − T`

Goal: rewrite `gap` as a sum over *missing* edges (non-edges), since equality holds only at `K_n` (no
missing edges). **Result: a clean exact identity `gap = Σ_e deficit_e·g_e² − λ(Σ_{nonedge} h² + S²/m)`
emerges, via the complement-graph eigenvector — but it is a DIFFERENCE of two non-negative terms, not a
non-negative per-non-edge sum.** New clean identities found. Code:
[`conjecture_B_nonedge_decomposition.py`](../conjecture_B_nonedge_decomposition.py).

## TASK 1 — the complement-graph eigenvector (key new identity)

`L_Ḡ = L_{K_n} − L_G = (nI − J) − L_G`. For `f ⊥ 1` (`Jf = 0`): `L_Ḡ f = nf − L_G f = (n − λ)f`. So:

> **`f` is also a Laplacian eigenvector of the complement `Ḡ`, with eigenvalue `n − λ`**, hence
> **`Σ_{nonedge {i,j}} (f_i − f_j)² = fᵀL_Ḡf = n − λ`** (verified to machine precision).

This is the natural non-edge analogue of `Σ_{edge} g² = λ`.

## TASK 2/3 — `T` and `λ₂G` via missing edges

- **`t_ab = (n−2) − deficit_ab`**, `deficit_ab = #{c ≠ a,b : c≁a or c≁b} = mdeg_a + mdeg_b − t̄_ab`
  (`mdeg_v = ` #non-neighbours, `t̄ = ` common non-neighbours). So
  > **`T = (n−2)λ − Σ_e deficit_e·g_e²`** (verified).
- Using `2fᵀDf = 2(n−1) − 2Σ_{nonedge}(f_i²+f_j²)` and `Σ_{nonedge}(f_i²+f_j²) + 2Σ_{nonedge}f_if_j =
  Σ_{nonedge} h²`:
  > **`λ₂G = (n−2)λ − λ(Σ_{nonedge} h_ij² + S²/m)`** (verified) — the RHS in non-edge form.

## TASK 5 — the exact non-edge decomposition

Subtracting:

> **`gap = λ₂G − T = Σ_e deficit_e·g_e² − λ·(Σ_{nonedge} h_ij² + S²/m)`** (verified, all graphs).

Both pieces are **non-negative**: `deficit_e ≥ 0`, `g_e² ≥ 0`, `h_ij² ≥ 0`, `S²/m ≥ 0`. At `K_n` there
are no non-edges, so `deficit_e = 0`, `Σ_{nonedge} h² = 0`, `S = 0` ⟹ `gap = 0` (equality), as required.

| graph | gap | `Σ_e deficit·g²` (≥0) | `λ(Σ_ne h²+S²/m)` (≥0) |
|---|---|---|---|
| K₂₀−e | 18.0 | 18.0 | 0 |
| gnp(20,.5) | 21.0 | 66.2 | 45.3 |
| rr(20,6) | 21.3 | 42.4 | 21.1 |
| deg2+dense(40) | 3.3 | 72.9 | 69.6 |
| cycle₂₀ | 0.38 | 1.76 | 1.38 |

## TASK 6 — it is a DIFFERENCE, not a non-negative per-non-edge sum

> **`gap` is NOT `Σ_{nonedge} Φ_ij` with `Φ_ij ≥ 0`.** It is `(edge-deficit term) − λ(non-edge-h²
> term)` — a *difference* of two non-negative quantities. `gap ≥ 0` is therefore equivalent to

> **`Σ_e deficit_e·g_e² ≥ λ·(Σ_{nonedge} h_ij² + S²/m)`**,

which is the inequality content itself — *not* manifestly true termwise. The deficit term is an
*edge* sum (weighted by missing-adjacency counts); the `h²` term is a *non-edge* sum; they live on
different index sets and do not combine into a single sign-definite per-non-edge form. (Per-non-edge
candidates `gap/#nonedge` etc. are not uniform; `min g²_ne → 0`, so no clean per-non-edge weight.)

## Why this is consistent with the global obstruction

The decomposition makes the missing-edge structure explicit and *correctly localizes equality to `K_n`*
(everything vanishes when there are no non-edges) — but the inequality `deficit-term ≥
λ(non-edge-h² + S²/m)` is again **global** (a difference, with the bottleneck families having a *small*
margin: deg2+dense `72.9 − 69.6 = 3.3`). So the non-edge view confirms, rather than removes, the
irreducibly-global nature: there is no non-negative per-non-edge SOS, consistent with the prior rounds
(`gap = (λfDf−T) − Required`, the matrix-S-procedure circularity, and the global-maximum-at-`K_n`
finding).

## New clean identities (recordable)

1. **`Σ_{nonedge} g² = n − λ`** (complement eigenvector `L_Ḡf = (n−λ)f`).
2. **`T = (n−2)λ − Σ_e deficit_e·g_e²`**, `deficit_e = mdeg_a+mdeg_b − t̄_ab`.
3. **`λ₂G = (n−2)λ − λ(Σ_{nonedge} h² + S²/m)`**.
4. **`gap = Σ_e deficit_e·g_e² − λ(Σ_{nonedge} h² + S²/m)`**.

All exact (verified). They express the *entire* problem through the complement / missing-edge data,
with equality at `K_n` manifest.

## Conclusion

- A clean **non-edge / complement decomposition exists**: `gap = Σ_e deficit_e g_e² − λ(Σ_{nonedge}
  h² + S²/m)`, with equality at `K_n` manifest (no missing edges ⟹ gap = 0).
- But it is a **difference of two non-negative terms**, *not* a non-negative per-non-edge sum. `gap ≥ 0`
  ⟺ `Σ_e deficit_e g_e² ≥ λ(Σ_{nonedge} h² + S²/m)` — the inequality is preserved, not dissolved.
- The complement eigenvector identity `Σ_{nonedge} g² = n − λ` (`f` is `Ḡ`-Fiedler with eigenvalue
  `n−λ`) is the most useful new structural fact: it ties the problem to the complement spectrum. A
  promising *next* direction is to study `gap` jointly via `(G, Ḡ)` (`f` is a simultaneous eigenvector,
  `λ + λ_Ḡ = n`), but the present decomposition shows the inequality remains a global comparison, not a
  termwise certificate.

## Lean
No new lemma. The identities (complement eigenvector `L_Ḡf=(n−λ)f`; `gap = Σ deficit·g² − λ(Σ_ne h²
+ S²/m)`) are clean and formalizable, and would pin the equality case (`gap = 0 ⟺` no non-edges `⟺
K_n`) cleanly — but the inequality itself stays the open global comparison.
