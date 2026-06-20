# TYPE A extremality — TASK 4A.5: search for the rigidity variable (honest negative)

**Goal:** find a structural variable `Φ` of the bulk `H` such that `excess := g − 1/3` (with `g =
gap/eff`) satisfies `g ≥ 1/3 + c·Φ` for some `c > 0` — which would *prove* `g ≥ 1/3`. **Result: no
strong predictor emerges, and the `g ≥ 1/3 + c·Φ` test is circular.** Code:
[`conjecture_B_typeA_rigidity_variable.py`](../conjecture_B_typeA_rigidity_variable.py) (42 TYPE A
samples; degree-2 twin ports `a,b~{0,1}`; `excess ∈ [0.175, 0.533]`, all `> 0`).

## Correlations of `excess = g − 1/3` with the 7 candidates

| candidate `Φ` (bulk `H`) | `corr(excess, Φ)` |
|---|---|
| 1. degree variance `Var(d_v)` | **−0.447** (best, weak) |
| 6. port degree deficit `(N−1)−d_port` | −0.195 |
| 2. conductance (Cheeger) | −0.184 |
| 3. spectral-gap ratio `(λ₃−λ₂)/λ₂` | +0.184 |
| 4. missing edges | −0.125 |
| 7. eff-resistance ratio `eff(H)/2` | −0.058 |
| 5. local irregularity (near ports) | −0.038 |

> **No strong predictor.** The best is degree variance at `r = −0.447` — *weak*, and with the **wrong
> sign** for a lower-bound mechanism: more degree variance correlates with *smaller* excess (closer to
> `1/3`), so variance pushes `g` *toward* the floor, not away. All other candidates are `|r| < 0.2`.
> The excess is genuinely **multi-factor** (consistent with every prior TYPE A analysis: no finite
> invariant determines the prefactor).

## Why the `g ≥ 1/3 + c·Φ` test is circular (not a proof)

The script's "min(excess/Φ) > 0" came out positive for all candidates — but this is **vacuous**:
since `excess > 0` (the finite-`N` samples sit above the `1/3` limit) and every `Φ ≥ 0`, the ratio
`excess/Φ` is automatically positive. That establishes `excess ≥ c·Φ` with `c = min(excess/Φ) > 0`
**only because we already observed `excess > 0`** — it *assumes* `g ≥ 1/3` rather than proving it. A
genuine proof would need `Φ` to *lower-bound* excess via an *independent* structural argument
(`Φ ≤ excess` with `Φ` provably `≥ 0` from `H`'s structure, and `Φ > 0` whenever `H ≠ K_N`). No
candidate does this:

- For the **extremizer itself** (`K_N` twins) every `Φ → 0` (degree variance `0`, missing edges `0`,
  …) *and* `excess → 0`. So near the extremizer `Φ` and `excess` both vanish — a lower bound
  `excess ≥ c·Φ` is consistent but says nothing (both sides `→ 0`), and the *rate* is what matters,
  which the weak correlation (`−0.447`, wrong sign) does not pin down.
- Away from `K_N`, `excess` and the `Φ`'s are only weakly related, so no `Φ` tracks the floor.

## Honest conclusion

- **No rigidity variable found.** Among degree variance, conductance, spectral-gap ratio, missing
  edges, local irregularity, port-degree deficit, and eff-resistance ratio, **none predicts `excess`
  strongly** (best `|r| = 0.447`, wrong sign), and **none yields a non-circular lower bound**
  `g ≥ 1/3 + c·Φ`.
- The aggregate fact `g ≥ 1/3` (TASK 4A scan, 0 counterexamples) stands as an **empirical infimum with
  a known extremizer** (`K_N` twins `→ 1/3`), but it is **not reducible to a single structural
  variable**. The prefactor `g` depends on the full bulk spectrum (the standing TYPE A obstruction);
  this scan confirms it at the rigidity level too.
- **Do not claim** any `g ≥ 1/3 + c·Φ` lemma — the data does not support a structural lower bound; the
  positive "min ratio" is an artefact of `excess > 0` (which is the conclusion, not a hypothesis).

## Implication for the proof route

The rigidity step (TASK 4) cannot be reduced to a **scalar** bulk invariant. A proof of `g ≥ 1/3` for
general bulks must therefore be **spectral/variational** (using the whole resolvent), not a one-variable
inequality. Candidate directions that remain (not pursued here): (a) a variational argument that
completing the bulk lowers `g` (the *operator* monotonicity `(L_H − λ)^{-1}` under edge addition, used
*aggregately* not edge-by-edge); (b) directly bounding `gap·3 ≥ eff` via the Green's-function
representation of both. Both are full-spectrum, matching the obstruction's nature.

## Lean
No theorem (negative result). The standing target remains the aggregate `gap ≥ eff/3`
(`CONJECTURE_B_STATUS.md`), to be proven spectrally — not via a rigidity scalar.
