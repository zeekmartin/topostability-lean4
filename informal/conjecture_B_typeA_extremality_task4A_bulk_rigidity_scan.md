# TYPE A extremality — TASK 4A: bulk-rigidity scan (no over-claiming)

**Goal:** test the *weakest* bulk-rigidity statement needed — `gap/eff ≥ 1/3` for degree-2 ports on a
**general** (non-complete) dense bulk `H` — by searching for counterexamples below `1/3`. **Do NOT**
attempt edge-by-edge monotonicity. Code:
[`conjecture_B_typeA_extremality_task4A.py`](../conjecture_B_typeA_extremality_task4A.py).

## 1–2. Bulk families scanned + measurements

Degree-2 ports `a,b` (twins `a,b~{0,1}` unless noted), `v₀~{a,b}`; per graph: `λ₂(G), γ=λ₂(H), eff,
gap, gap/eff`, restricted to genuine TYPE A (`λ < γ`, `f_v₀² > 0.3`). Families:

- `K_N` minus `0–35%` random interior edges; quasi-complete regular `rr(N, N−5..0.7N)`; dense ER
  `gnp(N, 0.5–0.85)`; **adversarial** (port-neighbours `0,1` forced to low degree); **low-conductance**
  (two dense blobs, ports same-side / split); disjoint ports (`a~{0,1}, b~{2,3}`).

## 3. Counterexample search — none found

| statistic (67 finite-`N` samples, `N≤80`) | value |
|---|---|
| min `gap/eff` | **0.466** (`K₈₀` twins, → 1/3 as `N→∞`) |
| median | 0.657 |
| fraction `≥ 1/3` | **1.000** |
| counterexamples `< 1/3` | **0** |

The **lowest** values are the complete-bulk twin ports (`K_N`); every non-complete bulk gives a
*higher* `gap/eff`. Large-`N` limits (the real test, since finite-`N` sits above the limit):

| family (twins `a,b~{0,1}`) | N=100 | 200 | 400 | 700 | trend |
|---|---|---|---|---|---|
| **`K_N` (extremizer)** | 0.440 | 0.387 | 0.361 | — | **→ 1/3** |
| `K_N` − 30% interior | 0.630 | 0.583 | 0.558 | — | → ~0.55 (**> 1/3**) |
| 2-blob, ports same side | 6.33 | 7.12 | 7.53 | — | ≫ 1/3 |
| adversarial, port-nbrs deg ~4 | 0.554 | 0.480 | 0.442 | 0.427 | → ~0.40 (**> 1/3**) |
| adversarial, port-nbrs deg ~6 | 0.535 | 0.464 | 0.428 | 0.412 | → ~0.38 |
| adversarial, port-nbrs deg ~10 | 0.485 | 0.425 | 0.393 | 0.380 | → ~0.36 |

> **No counterexample below `1/3`** — across `K_N±edges`, regular, ER, adversarial low-local-density,
> 2-blobs, disjoint ports, and their `N→∞` limits. The **complete-bulk twin port** is the minimizer,
> attaining `1/3` in the limit; every other bulk gives `gap/eff > 1/3`.

**Structural pattern.** Two regimes among non-complete bulks:
- **Interior sparsification** (`K_N` minus edges away from the ports): *raises* `gap/eff` (0.56 vs
  1/3). A sparser interior is *less* favourable to the minimum — consistent with "complete bulk
  minimizes".
- **Local sparsification at the ports** (adversarial: `0,1` low degree): *lowers* `gap/eff` toward
  `1/3`, approaching it **from above** as the local degree grows (0.40 → 0.38 → 0.36 → 1/3). This is
  the same axis as the port degree (TASK 1): making the port-neighbourhood denser pushes toward the
  twin-port limit `1/3`, never below.

## 4. False vs true statements

**FALSE / unsupported (do not claim):**
- *Edge-by-edge monotonicity* `gap/eff(ρ_bulk)` — that *every* bulk edge addition lowers `gap/eff`
  monotonically. Not tested edge-by-edge here, and TASK 3 already showed single-edge effects can be
  non-monotone in detail (`a~b` can lower `g` for large `d`). **Not asserted.**
- Any closed-form `g(H)` for general `H` — the gap depends on the full bulk spectrum (established).

**TRUE / data-supported (aggregate rigidity):**
> **Conjecture (scan-supported, NOT proven):** for `v₀` on two degree-2 ports into any connected dense
> bulk `H` with `λ₂(G) < λ₂(H)`, `gap/eff ≥ 1/3`, with the complete-bulk twin port attaining `1/3` in
> the `N→∞` limit.

This is an **aggregate lower bound**, not a monotonicity. The scan (67 samples + large-`N` limits, 0
counterexamples, infimum exactly the proven extremizer value `1/3`) supports it but does not prove it.

## 5. The weakest rigidity lemma needed

For the TYPE A proof, the needed statement is **only the aggregate bound** `gap/eff ≥ 1/3`, equivalent
to **`gap ≥ eff/3`** (with `eff > 0` already proven). The path to it that the data suggests:

1. **Reduce to degree-2 ports** — the minimizer has `min(d_a,d_b)=2` (TASK 1, `g(d)` increasing in `d`).
2. **Reduce to twins + `a≁b`** — overlap lowers `g` to the twin value, `a≁b` is the minimizing edge
   choice at the extremizer (TASKS 2–3).
3. **Bulk rigidity (this scan):** among all dense bulks with degree-2 twin ports, the **complete bulk**
   gives the infimum `1/3`. Interior sparsification raises `g`; local port-density only approaches
   `1/3` from above.

Step 3 is the open analytic content. The scan shows it as an **aggregate infimum** (`= 1/3`, attained
by `K_N`), *not* requiring edge-by-edge monotonicity — the weaker, sufficient form.

## Conclusion (no theorem stronger than the data)

- **No counterexample to `gap/eff ≥ 1/3`** over a broad bulk scan (incl. adversarial + large-`N`
  limits). The complete-bulk twin-port extremizer (`→ 1/3`) is the scan minimizer.
- The supported statement is an **aggregate lower bound** `gap/eff ≥ 1/3` (`gap ≥ eff/3`), **not** a
  monotonicity; edge-by-edge bulk monotonicity is explicitly *not* claimed.
- This is the weakest rigidity form sufficient for TYPE A; proving it (step 3) remains the open
  analytic step, now framed as an infimum-over-bulks statement with a known extremizer.

## Lean
No theorem committed (scan only). The aggregate bound `gap ≥ eff/3` is the target once step 3 is
proven on paper; `eff > 0` is already available (Green's-function sum rule / Courant–Fischer).
