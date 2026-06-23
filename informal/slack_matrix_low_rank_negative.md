# Conjecture B — the low-rank negative of `S`: Schur/port/avoidance routes FAIL

Exploit `S = ½(LD+DL) − L_t` (`u_kᵀS u_k = λ_k u_kᵀD u_k − u_kᵀL_t u_k`) via its low-rank negative.
**Result: the negative part is genuinely low-rank (≤ 2 eigenvalues), but it is NOT cleanly structured —
it is NOT port-localized (it lives in the *core* for deg2+dense: `S_HH` core block is indefinite, Schur-
on-ports fails 15/27), and the Fiedler does NOT avoid it (lollipop: Fiedler overlap 0.90 with the negative
direction). The negative direction aligns with the CONSTANT vector (deg2+dense/gnp, overlap 0.93–0.97) or
with the Fiedler mode (lollipop) — no consistent structure. The aggregate holds by positive-part
domination (magnitude), not by orthogonality. The proposed Schur/port/avoidance reduction does not
yield a proof.** Code: [`slack_matrix_low_rank_negative.py`](../slack_matrix_low_rank_negative.py).

## TASK 1 — negative rank and (in)consistent localization

`#neg(S) ≤ 2` (low-rank, confirmed). But the negative direction `w` is not consistently port-localized:

| graph | `#neg S` | min `S` | `w` port support | max-overlap mode `k` (λ_k/λ₂) |
|---|---|---|---|---|
| deg2+dense(80,.2) | 1 | −4.85 | 0.06 | **k=0 (constant)**, overlap 0.96 |
| deg2+dense(80,.9) | 1 | −15.1 | 0.16 | k=0 (constant), 0.90 |
| twin-port `K₅₀` d3 | 1 | — | **0.66** | k=0 / k=3 |
| lollipop(15,12) | 2 | — | 0.42 | **k=1 (Fiedler!)**, 0.90 |

> The negative direction `w` aligns with the **constant vector** (deg2+dense/gnp: overlap 0.93–0.97 with
> `u_0`) — irrelevant for the aggregate (`λ_0 = 0`). For **lollipop** it aligns with the **Fiedler**
> (overlap 0.90). So `w` is *not* a clean port mode; its identity varies by family.

## TASK 2 — decomposition (trivial identity)

`S = S_+ − Σ_j α_j w_j w_jᵀ` (`S_+ ⪰ 0`, `α_j = −sev_j`), and
`u_kᵀS_+ u_k ≥ Σ_j α_j⟨u_k,w_j⟩² ⟺ u_kᵀS u_k ≥ 0` — holds 29/29, but this is the identity itself, not a
bound (it just restates the per-mode aggregate).

## TASK 3 — bounding `⟨u_k, w_j⟩²` FAILS

The hope: `Lu_k = λ_k u_k` forces small overlap with the port-local `w`. **FALSE.** The Fiedler overlap
`|⟨f,w⟩|²` reaches **0.90** (lollipop) — the Fiedler *aligns* with the negative direction. Yet
`fᵀS f ≥ 0` (aggregate holds). So there is **no useful upper bound** on the overlap; the per-mode holds
because `S_+` is large *even where `f` aligns with `w`* (positive-part domination), not because `f`
avoids `w`.

## TASK 4 — Schur on ports FAILS (negative is in the core)

Partition `P` = ports, `H` = core; `S = [[S_PP, S_PH],[S_HP, S_HH]]`:

| | result |
|---|---|
| `S_HH` (core block) PSD | **15/27** |
| deg2+dense (1 port) `S_HH` min eig | **−2 to −12.6** (core indefinite!) |

> **`S_HH` is NOT PSD for deg2+dense** — the negative lives in the *dense core*, not the port. So the
> Schur complement on ports cannot isolate it (`S_HH⁻¹` doesn't exist / Schur invalid). Only for
> star/lollipop (many ports) is `S_HH` PSD and the Schur complement matches `#neg(S)`. The
> Schur-complement-on-ports reduction **fails on the main hard family (deg2+dense)**.

The diag-dominance `d_v² ≥ s_v` fails at *many* core vertices (not just ports), and the rank-≤2 negative
is a *global* combination, not a port-block — so no block partition isolates it.

## TASK 5 — no clean conditional lemma

The intended `slack_matrix_port_schur` (`S_HH PSD` ∧ Schur obstruction port-controlled `→ uᵀS u ≥ 0`) has
a **false premise** (`S_HH` not PSD for deg2+dense), and the obstruction is not port-controlled
(Fiedler overlap up to 0.90). So no such conditional lemma applies to the hard cases.

## Conclusion

- **Negative is low-rank (≤ 2)** — confirmed — but **NOT port-localized** (core for deg2+dense; `S_HH`
  indefinite, Schur-on-ports fails 15/27), and the negative direction aligns with the **constant**
  (deg2+dense) or the **Fiedler** (lollipop).
- **The Fiedler does NOT avoid the negative** (overlap up to 0.90) — the aggregate holds by *positive-part
  domination*, not orthogonality. No useful overlap bound (TASK 3 fails).
- **No Schur/port/avoidance reduction** — the rank-≤2 negative is a global object; the proposed
  conditional lemma has a false premise on the hard family.
- The aggregate remains the irreducible `S ⪰ 0 on eigenspaces` with a low-rank but *unstructured* (global,
  magnitude-dominated) negative — no operator shortcut.

## Lean
No code change: the Schur/port/avoidance conditional lemma does not apply (`S_HH` not PSD on deg2+dense,
Fiedler overlap up to 0.90). `aggregate_triangle_poincare` stays the direct sorry; the λ-free `S`
(`triangle_poincare_eigenbasis_diagonal.md`) remains the cleanest reformulation, but its rank-≤2 negative
resists localization. 3 sorrys unchanged.
