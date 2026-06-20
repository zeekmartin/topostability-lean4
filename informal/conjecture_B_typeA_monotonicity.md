# Conjecture B — TYPE A gap monotonicity under core edge edits

Hope: if `gap` decreases monotonically as core edges are added, the **complete core minimizes** `gap`
among cores on the same vertex set; since the complete core is proved positive (`gap = 10(n−3)/m > 0`),
all TYPE A would follow. We test it. Code:
[`conjecture_B_typeA_monotonicity.py`](../conjecture_B_typeA_monotonicity.py). **Verdict: monotonicity
FAILS — the complete core is not the minimizer.** (But `gap > 0` still holds everywhere.)

## Tests (TYPE A preserved: `λ₂(G) < λ₂(core)`, `f_v₀² > 0.3`)

| test | result |
|---|---|
| **1. add core non-edge:** `gap(H+e) ≤ gap(H)`? | `91/120` (24% **violations**, usually small) |
| **2. delete core edge:** `gap(H−e) ≥ gap(H)`? | `84/120` (30% **violations**) |
| **3. sparse → complete path:** monotone decreasing? | mostly (172/203, 352/420) but with 31–68 *increasing* steps; **min is NOT at complete** (nH=25: min `0.728 < 0.762 = complete`) |
| **4. is complete the global minimizer?** | nH=20: yes (0/32 below); **nH=30: NO** — a core with `gap = 0.629 < 0.641 = complete` |

So single-edge monotonicity fails (~25–30%), and the complete core is **not** the global gap-minimizer.

## Question 4 — characterizing the failure

The non-monotonicity is **localized to edges incident to the attachment vertices `a, b`**. From the
complete core `K_{n_H}` (attachments `a=0, b=1`):

| deletion | Δgap (nH=20) | Δgap (nH=30) | direction |
|---|---|---|---|
| `K − (a–b)` | **−0.015** | **−0.007** | gap **drops** |
| `K − (a–bulk)` | **−0.040** | **−0.029** | gap **drops** (most) |
| `K − (bulk–bulk)` | +0.011 | +0.005 | gap rises (monotone) |

> **Lowering an attachment degree `d_a` or `d_b` DECREASES the gap**; lowering a bulk degree increases
> it (the monotone direction). Greedy gap-minimizing deletion from the complete core removes
> attachment-incident edges and drives `gap`: `0.9375 → 0.849` (nH=20), `0.641 → 0.577` (nH=30), then
> bottoms out at an **interior** minimizer (a few attachment edges removed) and rises again.

**Reading.** The gap-minimizer is a **dense bulk with reduced-degree attachments** — i.e. moving
`a, b` toward low degree (toward a `v₀–a–…–bulk` path), interpolating TYPE A → TYPE B. The complete
core minimizes over the *bulk-bulk* edges (`gap` is monotone decreasing in those) but is *maximal* in
the attachment degrees, which is the **wrong** direction for the minimum.

## Answers

1. **Is gap minimized by the complete core?** **No.** Cores with reduced attachment degree have
   strictly smaller gap (verified down to `−2%` at nH=30, more under greedy deletion).
2. **Does adding a core edge decrease gap?** **Usually (76%) but not always** — bulk-bulk additions
   lower gap; attachment-incident additions often *raise* it.
3. **Does deleting a core edge increase gap?** **Usually (70%)** — but deleting an **attachment-
   incident** edge *decreases* gap (the systematic violation).
4. **Failures:** edges incident to `a, b`. Monotonicity holds along the bulk-bulk axis but **fails
   along the attachment-degree axis**.

## Conclusion

- **Monotonicity fails**, so **TYPE A does NOT reduce to the complete-core proof** — the complete core
  is not extremal; the true gap-minimizer has a dense bulk and *low* attachment degrees (an interior,
  closed-form-free structure interpolating toward TYPE B).
- **`gap > 0` nonetheless holds everywhere** (minima `0.577, 0.728, 0.849, …`, all positive); the
  conjecture is true, but the witness/extremizer is not the complete graph.
- Partial monotonicity *does* hold: `gap` is monotone decreasing in **bulk-bulk** edges (complete bulk
  minimizes for fixed attachments). The obstruction is entirely the **attachment degrees `d_a, d_b`**,
  exactly the variables the resolvent/junction analysis identified as carrying `C_attach`.

This rules out the "complete-core extremality" route. A proof must handle the attachment-degree axis
directly (the `v₀–a–b` junction), which is where every TYPE A obstruction has concentrated.

## Lean
No new lemma (numerical monotonicity study). Standing positive content unchanged: TYPE B closed
(`typeB_triEnergy_bound`, sorry-free), complete-core `gap = 10(n−3)/m`.
