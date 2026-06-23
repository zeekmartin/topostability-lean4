# Wiring `triEnergy_le_RHS_exists` / `conjectureB` — status

**Date:** 2026-06-23 · topostability-lean4 · analysis + docstring only, no proof-body changes, no new sorrys.

## Goal of the task
Reduce the `ConjectureB.lean` sorry-token count 3 → 2 by wiring `triEnergy_le_RHS_exists`
and `conjectureB` to call existing lemmas instead of carrying their own `sorry`.

## Finding: 3 → 2 by wiring is NOT achievable. Count stays **3**. Here is why.

### TASK 1 — exact `sorry` tokens (literal `sorry` in body)
`grep` for literal `sorry`: **three** declarations carry one — and `triEnergy_le_RHS_exists`
is **not** among them:

| line | declaration | kind |
|------|-------------|------|
| 854  | `aggregate_triangle_poincare` | content (regime i) |
| 1038 | `typeA_slack_ge_required`      | content (regime ii TYPE A) |
| ~1137| `conjectureB`                 | graph-level lift reduction |

`triEnergy_le_RHS_exists` (1085) has **no literal `sorry`** — it is *already wired*:
its body calls `aggregate_triangle_poincare` (854) and `gapEnergy_nonneg`
(→ `typeA_extremality_gap_nonneg` → `typeA_slack_ge_required`, 1038). So **TASK 2 is
already satisfied** — nothing to do there. (Calling a `sorry`-carrying *lemma* does not put
a `sorry` token in the caller: Lean's `declaration uses 'sorry'` fires only on bodies that
contain `sorryAx` directly, not transitively.)

### TASK 3 — `conjectureB` cannot be wired from existing lemmas
`conjectureB`'s `sorry` is **genuine unformalised content**, not a wiring artefact:

* The conclusion is the *graph-level* `λ₂(T(G)) ≤ λ₂(G)`. The only formalised bridge to it
  is **`Paper13.lambda2_triangle_graph_le`** — proved sorry-free, but requiring
  `G.IsRegularOfDegree d` and `2 ≤ d`. **`conjectureB` assumes no regularity**, so this
  lemma does not apply, and no other theorem in the repo concludes
  `algebraicConnectivity (triangleGraph …) ≤ algebraicConnectivity …`
  (only `ConjectureB:1123`, `Paper13:408`, and a regular type-check `Tests:40`).
* `conjectureB_lift` (1108) returns the **existential** `∃ f, triEnergy G f ≤ RHS`, *not*
  an `algebraicConnectivity` inequality. The gap between them is the **projected
  Fiedler-lift reduction**: obtain the good Fiedler from the existential, build the
  degree-weighted edge lift `h' = Bᵀf − (S/m)1_E`, prove `h' ⊥ 1_E`, `h' ≠ 0`, then
  Courant–Fischer (`algebraicConnectivity_le_rayleigh`) on `T(G)`.
* The supporting lift lemmas exist **only for the regular case**: `edgeLift_sum_zero`,
  `edgeLift_norm_fiedler`, `triangleGraph_quadratic_bound` all take `hreg`. Only the
  numerator identity `triangleGraph_quadratic_form` (Paper13:160) is general. The
  **irregular** norm / perpendicularity / numerator-bound analogs are **not formalised** —
  that is the entire content of the `conjectureB` `sorry`.

Proving them (the degree-weighted `‖h'‖²` identity, `∑ h' = 0`, and `t_ab ≤ min−1`
numerator bound, then assembling Courant–Fischer) is a substantial theorem — the irregular
twin of the ~150-line `lambda2_triangle_graph_le` — **not** a wiring step, and well beyond a
safe 20-attempt edit. Forcing it would either add new sorrys (forbidden) or risk the build.

### TASK 4 — verified count
`check_file` on the edited file: **3** `sorry` warnings — `854`, `1038`, `~1137`. Unchanged.
Build green (`=== check_file OK ===`).

### TASK 5 — the dependency chain (what already holds)
```
conjectureB                       (SORRY 3: irregular lift reduction — open)
   ⟶ conjectureB_lift             (sorry-free wiring, 1114)
        ⟶ triEnergy_le_RHS_exists (sorry-free wiring, no own token, 1085)
             ⟶ aggregate_triangle_poincare   (SORRY 1, 854)
             ⟶ typeA_slack_ge_required        (SORRY 2, 1038)
```
The chain `triEnergy_le_RHS_exists → aggregate + typeA` and
`conjectureB_lift → triEnergy_le_RHS_exists` are **already in place and sorry-token-free**.
The *only* missing link is `conjectureB → conjectureB_lift`, which is the unformalised
irregular reduction — the genuine third content gap, not a wiring artefact.

## What was changed
* `conjectureB` **docstring** enhanced to record the above precisely (regular case done;
  analytic core wired to the two content sorrys; remaining gap = irregular lift reduction).
  **No proof body modified; no sorry added/removed.** `aggregate_triangle_poincare` and
  `typeA_slack_ge_required` untouched. Build green.

## Honest bottom line
The requested 3→2 reduction presumes `conjectureB`'s `sorry` is a wiring artefact removable
by `exact conjectureB_lift …`. It is not — the types differ by the open irregular
Fiedler-lift reduction. `triEnergy_le_RHS_exists` was already wired. So the count remains
**3 = {aggregate (854), typeA (1038), conjectureB-irregular-reduction (~1137)}**, now with
the third gap documented as genuine content rather than an opaque token.
