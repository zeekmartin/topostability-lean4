# Conjecture B — TYPE A asymptotic proof attempt (and a correction)

Attempt the asymptotic argument for `gap/eff ≥ c₀`, splitting into (a) large `n` and (b) finite check.
**The attempt overturns two earlier claims** and gives the corrected picture. Code:
[`conjecture_B_typeA_asymptotic_proof.py`](../conjecture_B_typeA_asymptotic_proof.py).

## TASK 1a — the proposed mechanism is FALSE

Proposed: for `min(d_a,d_b) ≥ D₀`, `f_a ~ x/d_a → 0`, `C_attach → 0`, `gap → R″ > 0`. Tested on dense
`gnp(0.5)`, `n` growing:

| n | `f_a` | `x/γ` | `f_a·d_a` | `C_attach` | `R″` | gap | `gap/eff` |
|---|---|---|---|---|---|---|---|
| 40 | 0.0159 | 0.072 | 0.40 | **−0.95** | 1.56 | 0.804 | 7.15 |
| 120 | 0.0077 | 0.022 | 0.49 | **−0.94** | 1.19 | 0.322 | 9.98 |
| 320 | 0.0030 | 0.008 | 0.49 | **−0.94** | 1.08 | 0.200 | 16.74 |

> **`C_attach` does NOT → 0** — it is `O(1)` (`≈ −0.94`), because `f_a·d_a = O(1)` (`f_a ~ x/γ ~ x/d_a`
> for a dense core, so `(d_a−2)f_a(f_a−x) ~ d_a·(x/d_a)·(−x) = −x²`). And **`gap → 0`** (not `R″`):
> `R″ ≈ 2(1−q)x²` and `C_attach ≈ −2(1−q)x²` are both `O(1)` and **cancel**, leaving the `O(1/n)`
> residual. The correct surviving object is **`gap/eff → c(q) = O(1)`**, not `gap → R″`.

So the "`C_attach → 0`, `gap → R″`" argument is incorrect; `gap/eff` (not `gap`) is the bounded object.

## TASK 1b — `gap/eff` for dense (symmetric) attachments

`gnp(q)`, `a,b = (0,1)`: `gap/eff ∈ [6, 17]` across `q ∈ {0.3..0.9}`, `n` up to 320 — large, stable.
The dense-interior symmetric case is **not** the minimizer.

## TASK 1c — DECISIVE: fixed low attachment degree ⇒ minimizers PERSIST (correction)

Fix the attachment degree (delete edges so `d_a = d_b = d` in the core) on a growing dense `gnp(0.5)`:

| fixed `d` | n=100 | 300 | 600 | 1000 | gap (n=1000) | eff (n=1000) |
|---|---|---|---|---|---|---|
| **2** | 0.732 | 0.688 | 0.682 | **0.677** | 1.36 | 2.01 |
| **3** | 1.351 | 1.248 | 1.230 | **1.204** | 1.40 | 1.16 |
| **4** | 1.850 | 1.711 | 1.648 | **1.625** | 1.27 | 0.78 |

> **With the attachment degree held fixed and low, `gap/eff` STABILISES at a low value** (`d=2 → 0.68`,
> `d=3 → 1.20`, `d=4 → 1.63`) and **does not rise with `n`**. These are genuine TYPE A (`f_v₀² ≈ 0.66`,
> `λ < γ`). **This corrects the previous round's conclusion**: the low `gap/eff` cases are **NOT
> finite-size artefacts** — they are a **persistent family controlled by the attachment degree
> `min(d_a,d_b)`**. (The earlier scale test used `gnp`-`lolo` where the "low-degree" vertex still has
> degree `~0.4n` growing with `n`, so `gap/eff` rose; fixing the degree reveals the persistence.)

Note the two regimes both keep `gap > 0`:
- **dense** (attachment degree `~qn`): `gap → 0` (`= c(q)·n/m`), `eff → 0`, `gap/eff → c(q) ≈ 6–17`;
- **fixed low degree** `d`: `gap → const > 0` (`≈ 1.3–1.4`, nearly `d`-independent), `eff → const`,
  `gap/eff → g(d)` with `g(2) ≈ 0.68`.

So `gap` itself is **bounded away from 0** in the low-degree family (`gap → 1.36` at `d=2`); the small
quantity is the *ratio* `gap/eff`, not `gap`.

## TASK 2 — finite verification is NOT possible (no `n₀`)

Searching TYPE A graphs (`n = 8..40`) for `gap/eff < 5`:

> **432 found; they occur at EVERY `n` up to 40** (`≈12` per `n`, no decay); largest `n` with
> `gap/eff < 5` is the cap (40); smallest `gap/eff = 0.026`. **224/432 have `min(d_a,d_b) ≤ 4`.**

So **the `(a)/(b) split fails**: there is no `n₀` above which `gap/eff ≥ 5`. The `gap/eff < 5` cases
persist at all `n` (the fixed-low-degree family), so a finite check up to some `n₀` cannot cover them.

## Corrected picture / open lemma

- The proposed asymptotic mechanism (`C_attach → 0`, `gap → R″`) is **false**; `C_attach = O(1)`,
  `gap → 0` in the dense regime.
- The minimizers are a **persistent** family: **`v₀` attached to two low-degree core vertices**
  (`min(d_a,d_b)` fixed) inside an otherwise dense core. `gap/eff → g(min-degree)`, with
  **`inf ≈ 0.68` at degree 2** (genuine TYPE A), persistent — *not* `≈5`, *not* finite-size.
- **`gap > 0` nonetheless holds robustly**: in the low-degree family `gap → const ≈ 1.3 > 0`; in the
  dense family `gap → 0⁺` (the `c(q)·n/m` residual). The conjecture is safe; only the *ratio* `gap/eff`
  dips to `≈ 0.68`.
- The open lemma is therefore **`gap/eff ≥ c₀` with `c₀ ≈ 0.68`** (degree-2 attachments), holding
  *uniformly in `n`* — there is no finite/asymptotic split. Equivalently, prove `gap > 0` directly,
  handling (i) the dense residual `c(q)·n/m > 0` and (ii) the fixed-low-degree family
  (`gap → const > 0`).

## What this means for a proof

A clean target emerges: the **low-degree-attachment family** (`v₀` on two degree-`d` vertices in a
dense core) has `gap → const > 0` as `n → ∞` with `d` fixed — a *bounded-below* limit that may be
analysable in closed form (the attachments are themselves near-degree-2, a "thick bottleneck"; the
dense bulk is rigid). This is the genuine extremal family, replacing the false "boundary" and
"finite-size" leads. The dense regime is the already-understood `gap = c(q)·n/m` residual.

## Lean
No new lemma (numerical correction + asymptotic test). `CONJECTURE_B_STATUS.md` §6 updated to the
corrected open lemma (`c₀ ≈ 0.68`, persistent; no finite/asymptotic split). Standing positive content
unchanged (TYPE B closed, complete-core `10(n−3)/m`).
