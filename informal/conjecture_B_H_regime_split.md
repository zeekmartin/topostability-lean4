# Conjecture B — two-regime proof via `H(f)=Σ f_v²/d_v`: 91% covered, hard core remains

Split `C+R″ ≥ 0` by `H(f)` (corr `−0.935` with the slack). Code:
[`conjecture_B_H_regime_split.py`](../conjecture_B_H_regime_split.py).

**Key reframing.** `R″ ≥ 0` always, so `C+R″ ≥ 0` is **automatic when `C ≥ 0`**; the only
hard case is `C < 0` (7323/9020 = 81%), where we need `R″ ≥ |C|`.

**Headline.** The H-split + a crude Cauchy–Schwarz bound covers **91%** of the corpus,
but does **not** close B. Two corrections to the proposed plan:
1. **Regime 2 premise is false:** high `H` does **not** make `C ≈ 0`. As `H` grows,
   `C < 0` becomes *more* prevalent (99% at `H∈[0.35,0.45]`) and `|C|/R″` *grows* — high
   `H` is the **hard** regime. The `−0.935` correlation is `R″` shrinking, not `C`
   vanishing.
2. **Regime 1 works:** the crude C-S bound `|C| ≤ Cb_cs ≤ R″` holds for small `H`
   (100% for `H ≤ 0.25`). The remaining 9% (high-`H`, `C<0`) is the irreducible hard core.

Positive deliverable: **Task 7's `C=0` lemma is verified exactly and is Lean-provable.**

---

## TASK 7 — `C = 0` when degrees are equal on support-incident edges (clean, Lean-ready)

> **Lemma.** If for every edge `ab` with `f_a ≠ 0` or `f_b ≠ 0` we have `d_a = d_b`, then
> `C = Σ_{ab∈E}(d_h−d_l) f_h (f_h−f_l) = 0`.

**Verified:** 13/9020 graphs satisfy the hypothesis; **all have `C = 0` exactly**
(`max |C| = 0`). **Proof** (Lean-ready): for each edge `ab`, either (i) it touches the
support (`f_a≠0` or `f_b≠0`) ⇒ `d_a=d_b` ⇒ `d_h−d_l = 0` ⇒ term `= 0`; or (ii) it does
not (`f_a=f_b=0`) ⇒ `f_h = 0` ⇒ term `= 0`. So every edge term vanishes. (`C` is not yet
a defined object in the Lean repo; formalizing needs `C` defined first.)

**But the regime-2 hope built on this fails:** support-degree-homogeneity is *rare* (13
graphs), so "`H` large ⇒ Fiedler on equal-degree vertices ⇒ `C=0`" does **not** hold.

---

## Sign of `C` and `|C|/R″` across `H` bins — regime 2 refuted

| `H` bin | #graphs | frac `C≥0` | frac `C<0` | median `\|C\|/R″` | max `\|C\|/R″` |
|---|---|---|---|---|---|
| `[0.00,0.20)` | 672 | **0.62** | 0.38 | 0.015 | 0.250 |
| `[0.20,0.25)` | 2778 | 0.33 | 0.67 | 0.027 | 0.245 |
| `[0.25,0.30)` | 2122 | 0.09 | 0.91 | 0.058 | 0.221 |
| `[0.30,0.35)` | 1284 | 0.08 | 0.92 | 0.064 | 0.328 |
| `[0.35,0.45)` | 1752 | 0.01 | **0.99** | 0.129 | 0.372 |
| `[0.45,0.51)` | 412 | 0.10 | 0.90 | 0.130 | 0.468 |

- `C ≥ 0` is common at **low** `H` (62%) and vanishes at high `H` (1–10%).
- `|C|/R″` **grows** with `H` (0.015 → 0.13). High `H` ⇒ small `R″` (tight slack) **and**
  `C < 0` ⇒ the hard regime. The proposed "high-`H` ⇒ `C≈0`" is exactly backwards.
- Throughout, `|C|/R″ ≤ 0.47` — B holds with ≥ 2× margin everywhere; the obstacle is
  *proof technique*, not closeness to violation.

---

## REGIME 1 — crude Cauchy–Schwarz bound (works for small `H`)

Split each term of `C = Σ (d_h−d_l)f_h(f_h−f_l)` as `[(d_h−d_l)(f_h−f_l)]·[f_h]` and
apply C-S over edges:

> `|C| ≤ Cb_cs := √(Σ_{ab}(d_h−d_l)²(f_h−f_l)²) · √(Σ_{ab} f_h²)`.

| | result |
|---|---|
| `\|C\| ≤ Cb_cs` (C-S, exact) | **9020/9020** |
| `Cb_cs ≤ R″` | **8139/9020 (90.2%)** |
| `Cb_cs ≤ R″` for `H < 0.25` | **100%** |
| `Cb_cs ≤ R″` for `H ∈ [0.35,0.45)` | 62.6% |
| `Cb_cs ≤ R″` for `H ∈ [0.45,0.51)` | 59.5% |

So for **`H ≤ 0.25`** the rigorous chain `|C| ≤ Cb_cs ≤ R″` proves `C+R″ ≥ 0`
(covers 3450 graphs, 38%, fully). The bound degrades as `H` grows (median `Cb_cs/R″`:
0.34 at low `H` → 0.95 at high `H`).

---

## COMBINED — 91% covered, 9% irreducible

A graph is **covered** if `Cb_cs ≤ R″` (Regime 1, crude C-S) **or** `C ≥ 0` (trivial,
since `R″≥0`):

> covered: **8209/9020 = 91.0%**.

**Uncovered: 811 graphs (9%)** — all have `C < 0` *and* `Cb_cs > R″`. Their `H ∈
[0.286, 0.491]` (median 0.44): the **high-`H` regime**. Worst `|C|/R″ = 0.264`
(`n=9, m=23, H=0.444`). The regime-2 escape fails here: `C ≥ 0` holds on only **4.8%** of
`H > 0.3` graphs (not ~100%), so no `H`-threshold makes regime 2 trivial.

| `H` threshold `c` | #graphs `H>c` | frac `C≥0` | max `\|C\|/R″` |
|---|---|---|---|
| 0.30 | 3448 | 0.048 | 0.468 |
| 0.35 | 2164 | 0.027 | 0.468 |
| 0.40 | 1893 | 0.029 | 0.468 |

No `c` makes the upper regime provable by either route.

---

## Synthesis

- **No single threshold `c` closes B.** Low `H` (`≤0.25`): crude C-S proves it (100%).
  Plus `C≥0` cases (trivial). Together 91%. The remaining **9% are high-`H`, `C<0`**
  graphs where crude C-S is too weak and `C≥0` fails — the same dense hard core as every
  prior round, now localized to `H ≳ 0.3`.
- **The proposed regime 2 is refuted:** high `H` correlates with *more* negative `C` and
  *smaller* `R″`, not `C≈0`. `H` is a great *predictor* (corr `−0.935`) but the high-`H`
  end is the difficulty, not an easy regime.
- **Banked:** Task 7's `C=0` lemma (degrees equal on support-incident edges) is exact
  and Lean-provable; and the Regime-1 crude C-S bound `|C| ≤ Cb_cs ≤ R″` is a rigorous
  proof of `C+R″ ≥ 0` on the low-`H` (distributed-Fiedler) regime.

### Caveats
`λ₂`, `f` numerical; over the 9020 distinct corpus graphs (`n≤9`). `|C| ≤ Cb_cs` and
`H·fᵀDf ≥ 1` are exact; `Cb_cs ≤ R″` thresholds and the 91% coverage are empirical.
The hard 9% confirms B is not closed by an `H`-regime split + crude bounds.
