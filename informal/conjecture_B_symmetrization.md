# Conjecture B — symmetrization route for `R = T/(λ₂G) ≤ 1` (no monotone op; clean equality)

Goal: prove `R ≤ 1` with equality only at `K_n` via a symmetrization/compression that moves `G` toward
`K_n` without decreasing `R`. **Result: NO such monotone operation exists** (edge-addition, Zykov, and
batched completion all decrease `R` on some steps), but **the equality case is clean: `R = 1 ⟺ K_n`.**
Code: [`conjecture_B_symmetrization.py`](../conjecture_B_symmetrization.py).

## TASK 1–3 — the symmetrization operations are all NON-monotone

| operation (toward `K_n`) | `R` non-decreasing? |
|---|---|
| **(a) edge addition** `G → G+e` | **89/100** — 11% of additions *lower* `R` |
| **(b) Zykov symmetrization** (`v := twin of u`, `d(u) ≥ d(v)`) | **88/160** — frequently *lowers* `R` (e.g. `0.382 → 0.376`) |
| **(c) batched completion** `G → K_n` (add all missing edges) | non-monotone (`6/64`, `20/137` steps *decrease* `R`) |

> **Every operation that moves toward `K_n` decreases `R` on a positive fraction of steps.** Even
> completing all the way to `K_n` (whose endpoint `R = 1` is the max) is non-monotone along the path. So
> there is **no monotone symmetrization route** — the Fiedler relocates discontinuously under each
> operation, so `R` is not a monotone functional of the edge set in *either* direction (cf. the
> edge-*deletion* non-monotonicity, `conjecture_B_R_edge_deletion.md`).

Zykov is the most natural candidate (it is the engine of Turán-type extremal proofs), and it **fails**
here — making two vertices twins can *lower* `R`. So the standard extremal-graph symmetrization toolkit
does not apply to `R = T/(λ₂G)`.

## TASK 5 — equality `R = 1` forces `G = K_n` (clean)

| graph | `R` | `min t_e` | `n−2` | all `t_e = n−2`? |
|---|---|---|---|---|
| `K_n` | **1.000** | `n−2` | `n−2` | **yes** |
| `K_n − 1` edge | `(n−3)/(n−2)` | `n−3` | `n−2` | no |
| `K_n − k` | `< 1` | `< n−2` | `n−2` | no |

> **`R = 1 ⟺ every edge has `t_e = n−2` ⟺ `G = K_n`.** Structural argument: `t_{ij} = |N(i)∩N(j)| = n−2`
> means `N(i)∩N(j) = V∖{i,j}`, i.e. both `i` and `j` are adjacent to *all* other vertices, so
> `d(i) = d(j) = n−1`. If this holds for *every* edge of a connected graph, every vertex (being on some
> edge) has degree `n−1` ⟹ `G = K_n`. Deleting any single edge drops `t_e` below `n−2` on the affected
> edges, and `R` drops below `1` (verified: `K_n − 1` gives `R = (n−3)/(n−2) < 1`).

So the **equality characterization is rigorous and clean**: `R(G) = 1 ⟺ G = K_n`.

## TASK 4 — Fiedler relocation under the operations

Under each operation the Fiedler `f` (and `λ₂`) move discontinuously: e.g. on `K_n − e` it localizes
on the deleted edge (`f = (e_i−e_j)/√2`, `λ₂ = n−2`); adding an edge or twinning can re-spread or
re-localize it. This discontinuity is exactly *why* `R` is non-monotone — `T`, `λ₂`, and `Gvar` all jump
when the Fiedler relocates, and their ratio is not controlled by the single edge change.

## TASK 6 — classification

> **`R ≤ 1` is a NON-MONOTONE but GLOBAL bound** with `K_n` the unique maximizer:
> - **No monotone symmetrization operation** (edge-add, Zykov, batched completion all non-monotone) —
>   the deletion direction is non-monotone too. `R` is not a monotone set-function of edges.
> - **No counterexample** (`R > 1` never occurs; `conjecture_B_R_edge_deletion.md`: 0/91+, max `0.964`).
> - **Clean equality:** `R = 1 ⟺ G = K_n` (proved: `t_e = n−2 ∀e ⟺` all degrees `n−1 ⟺ K_n`).

So `R ≤ 1` (= `triEnergy_le_RHS`, = `T ≤ λ₂G`) is a **global maximum statement saturated uniquely at
`K_n`**, provable *neither* by deletion-monotonicity *nor* by symmetrization-monotonicity. A proof must
be **global/variational** — a single inequality saturated at `K_n` — not an incremental graph-operation
induction.

## Conclusion

- **Symmetrization route FAILS** (all operations non-monotone) — confirming the deletion-route finding:
  `R` is fundamentally non-monotone under local edge operations (the Fiedler jumps).
- **The equality case is fully understood:** `R = 1 ⟺ K_n` (clean degree/triangle-count argument).
- The open `triEnergy_le_RHS` is therefore a **global variational maximum** (`R ≤ 1`, unique max `K_n`),
  not reducible to any monotone compression. The next attempt should be a global Rayleigh-type bound
  with `K_n` as the saturating case — e.g. controlling `T` and `λ₂G` simultaneously via the same test
  vector, with the complete graph forcing equality.

## Lean
No new lemma. The equality characterization `R = 1 ⟺ G = K_n` (via `t_e = n−2 ∀e ⟺` complete) is a clean
combinatorial fact that could be formalised, pinning the equality case of `triEnergy_le_RHS`. The
inequality `R ≤ 1` itself remains the open global bound (no monotone-operation proof exists).
