# Conjecture B — an EXACT identity for `B2′` via the Fiedler equation

Attack the leaf `B2′ ≤ 2λ·degQuad` through the combinatorial meaning of the `−1`. **Result: an exact
identity (verified to `2·10⁻¹³`):**

> **`B2′_unord = λ(d_eff − 1) − ½(A + I)`**, where `A = Σ_e(d_a−d_b)(f_a²−f_b²)` (signed assortativity)
> and `I = Σ_e|d_a−d_b|·g_e² ≥ 0` (imbalance energy).

**Hence the Lean leaf `B2′_ord ≤ 2λ·degQuad ⟺ A + I ≥ −2λ` (43/43). The `−1` supplies exactly the `2λ`
margin. Mechanism: `A` (large negative) and `I` (large positive) nearly CANCEL; `A + I` is a small
residual in `[−2λ, 0]`. The cancellation is essential — `A` alone `≥ −2λ` fails 11/43.** Code:
[`conjecture_B_minus_one_identity.py`](../conjecture_B_minus_one_identity.py).

## TASK 3/5 — the exact identities (all verified `< 10⁻¹²`)

Via the Fiedler equation `Σ_{u∼v} f_u = (d_v − λ)f_v`:

| identity | meaning | max err |
|---|---|---|
| `D_v = (2λ − d_v)f_v² + P_v` | local Dirichlet (`P_v = Σ_{u∼v}f_u²`) | `1·10⁻¹³` |
| `W = Σ_v d_v D_v` | `W = Σ_e(d_a+d_b)g²` | `9·10⁻¹³` |
| **`W = 2λ·d_eff − A`** | `A = Σ_e(d_a−d_b)(f_a²−f_b²)` | `5·10⁻¹³` |
| `Σ_e min·g² = ½(W − I)` | `min = ½((d_a+d_b) − |d_a−d_b|)` | `2·10⁻¹³` |
| **★ `B2′_unord = λ(d_eff−1) − ½(A + I)`** | the leaf's exact form | `2·10⁻¹³` |

Derivation: `Σ_e min·g² = ½(W − I)` (since `min = ½(sum − |diff|)`); `W = 2λd_eff − A` (the `D_v`
identity summed against `d_v`, where `Σ_v(s_v − d_v²)f_v² = −A`, `s_v = Σ_{u∼v}d_u`); and
`B2′_unord = Σ_e min·g² − λ` (the `−1` is `−Σ_e g² = −λ`). Combining:
`B2′_unord = ½(2λd_eff − A − I) − λ = λ(d_eff − 1) − ½(A + I)`.

## TASK 1/4 — the reduced inequality `A + I ≥ −2λ`

`B2′_unord ≤ λ·d_eff ⟺ λ(d_eff−1) − ½(A+I) ≤ λd_eff ⟺ **A + I ≥ −2λ**`. Equivalently
`E_μ[min] = d_eff − (A+I)/(2λ)`:

| inequality | `⟺` | holds |
|---|---|---|
| `A + I ≥ −2λ` | `E_μ[min] ≤ d_eff + 1` (= **Lean leaf**) | **43/43** |
| `A + I ≥ −λ` | `E_μ[min] ≤ d_eff + ½` (the prompt's candidate) | **40/43** ✗ |
| `A + I ≥ 0` | `E_μ[min] ≤ d_eff` | 23/43 |

> **The prompt's `E_μ[min] ≤ d_eff + ½` is FALSE (40/43, 3 violations).** The sharp constant is exactly
> `−2λ` (i.e. `E_μ[min] ≤ d_eff + 1`); the `−1` in `B2′` is precisely what buys the `2λ` margin, no more.

## TASK 2/4 — the `A ↔ I` cancellation (why `min` is irreducible)

`A` and `I` are individually **large and opposite**, nearly cancelling:

| graph | class | `A` | `I` | `A + I` | `−2λ` |
|---|---|---|---|---|---|
| gnp(60,.7) | RANDOM | **−328.5** | **+322.1** | −6.4 | −56.5 |
| deg2+dense(80,.7) | TYPE A | **−107.6** | **+106.6** | −1.0 | −4.0 |
| deg2+dense(80,.3) | TYPE A | −44.3 | +41.6 | −2.7 | −3.9 |

> **`A ≈ −I`** (disassortative `A` ≈ minus the imbalance `I`); `A + I` is a tiny residual. `A` alone is
> hugely negative (`min A/λ = −68.7`), so **`A ≥ −2λ` fails 11/43** — the cancellation with `I` is
> essential.

This is exactly *why* every degree relaxation died: `min(d_a,d_b) = ½((d_a+d_b) − |d_a−d_b|)` encodes
the cancellation — the `(d_a+d_b)` part is `W` (carrying `−A`) and the `|d_a−d_b|` part is `I`. The `F`
route kept the orientation-degree (`≈ W`, i.e. only `−A`) and dropped `I`; the `W`-route kept `W`
(`−A`) and dropped `I`. Both discard the cancelling `I` and explode. **`min` is the unique combination
that pairs `A` with its canceller `I`.**

## TASK 2 — closed form of `A + I` per edge

With `h, ℓ` the higher/lower-degree endpoints of `e`:
`A + I = 2·Σ_e (d_h − d_ℓ)·f_h·(f_h − f_ℓ)` (verified). The target `A + I ≥ −2λ` is the *global* sum
inequality `Σ_e (f_h − f_ℓ)·[(d_h − d_ℓ)f_h + (f_h − f_ℓ)] ≥ 0` — not sign-definite per edge, so it
needs the Fiedler structure (consistent with the scale-free product form failing for arbitrary `f`).

## Regular anchor

For regular graphs `A = I = 0`, so `B2′_unord = λ(d_eff − 1) = λ(d − 1)` exactly, and
`A + I = 0 ≥ −2λ` with slack `2λ`. This recovers `B2prime_le_two_lam_degQuad_regular` from the identity
(the irregular part is purely the defect `−½(A + I)`).

## TASK 6 — Lean target without `F`/`W`

> **Reduce `B2prime_le_two_lam_degQuad` to `A + I ≥ −2λ`** via the exact identity
> `B2′_unord = λ(d_eff−1) − ½(A+I)`. The identity is algebra + the Fiedler equation (`D_v` identity,
> `W = 2λd_eff − A`) — all formalisable. The remaining open inequality is `A + I ≥ −2λ`, with `I ≥ 0`
> manifest and `A` the (already-studied) signed assortativity term; the regular case `A = I = 0` is
> immediate.

## Conclusion

- **EXACT:** `B2′_unord = λ(d_eff − 1) − ½(A + I)`, `A = Σ_e(d_a−d_b)(f_a²−f_b²)`,
  `I = Σ_e|d_a−d_b|g² ≥ 0` (verified `2·10⁻¹³`).
- **Leaf `⟺ A + I ≥ −2λ`** (43/43); the prompt's `E_μ[min] ≤ d_eff+½` (`A+I ≥ −λ`) is FALSE (40/43).
- **Mechanism:** `A ≈ −I` (large, opposite); `A + I` is a small residual. The cancellation is why every
  degree relaxation (`F`, `W`, constant-`α`) died — `min` uniquely pairs `A` with its canceller `I`.
- **Lean route:** formalise the identity, reduce the leaf to `A + I ≥ −2λ` (regular `A=I=0` immediate).

## Lean
No code change yet. The identity `B2′_unord = λ(d_eff−1) − ½(A+I)` and the reduction to `A + I ≥ −2λ`
give a cleaner Lean target than the raw `min`-sum; the regular anchor (`A=I=0`) is already proved
(`B2prime_le_two_lam_degQuad_regular`). Next Lean step: formalise the identity (Fiedler-equation
algebra) so the leaf becomes the single inequality `A + I ≥ −2λ`.
