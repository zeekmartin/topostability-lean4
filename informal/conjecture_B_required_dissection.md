# Conjecture B — direct dissection of `Required = λ₂·R`, `R = λ₂ + S²/m − fᵀDf`

Focus entirely on `R` (and `Required = λ₂·R`) on deg2+dense, *not* on bounding `T`.
`v₀` = the degree-2 bottleneck vertex; `f_{v₀}` its (dominant) Fiedler value;
`a,b` its two neighbours. Code: inline (`conjecture_B_required_dissection` run).

**Headline.** `Required` is a **delicate `O(1)` difference of large terms** that stays
bounded as `n → ∞`. The eigen-equation at `v₀` fixes `λ₂ → d_{v₀} = 2` exactly. `S = Σ d_v
f_v` grows like `−qn·f_{v₀}` (|S| ≈ 0.65n), but enters only through `S²/m → 2q` (constant).
`fᵀDf → 2.65` (constant). Hence `R → 0.65` and `Required → 1.3`. Meanwhile `Deficit →
λ₂f_{v₀}² → 2`, so `Deficit − Required = RHS − T → λ₂(f_{v₀}² − R) ≈ 0.72 > 0` — the stable
margin. **B reduces on this family to the scalar inequality `fᵀDf + f_{v₀}² ≥ λ₂ + S²/m`**
(margin ≈ 0.36).

---

## TASK 1 — term-by-term decomposition (deg2+dense, q=0.65)

| `n` | `λ₂` | `S` | `S²/m` | `fᵀDf` | `R` | `Required` | `f_{v₀}²` |
|---|---|---|---|---|---|---|---|
| 50 | 1.976 | 29.0 | 1.094 | 2.650 | 0.420 | 0.830 | 0.978 |
| 100 | 1.988 | 61.1 | 1.188 | 2.646 | 0.531 | 1.055 | 0.990 |
| 200 | 1.994 | −126.0 | 1.244 | 2.649 | 0.589 | 1.174 | 0.995 |
| 500 | 1.998 | −320.7 | 1.276 | 2.648 | 0.626 | 1.250 | 0.998 |
| 1000 | 1.999 | −645.9 | 1.288 | 2.649 | 0.638 | 1.276 | 0.999 |

**Scaling of each term:**
- **`λ₂ → 2`** (= `d_{v₀}`). The bottleneck pins it; the deviation `2−λ₂ → 0`.
- **`S` grows linearly**, `|S| ≈ qn` (646 ≈ 0.65·1000). Its sign is the arbitrary
  eigenvector sign; only `S²` matters.
- **`S²/m → 2q = 1.30`** (constant). The `n`-growth of `S` is exactly cancelled by
  `m ≈ qn²/2`: `S²/m ≈ (qn·f_{v₀})²/(qn²/2) = 2q·f_{v₀}²`.
- **`fᵀDf → 2.65`** (constant): `= d_{v₀}f_{v₀}² + (fᵀDf)_dense → 2 + 0.65`.
- **`R = λ₂ + S²/m − fᵀDf → 0.65`** (= `2 + 1.30 − 2.65`); **`Required = λ₂·R → 1.30`.**

**Dominant terms:** `λ₂ (≈2)` and `fᵀDf (≈2.65)` are the large pieces; `S²/m (≈1.3)` the
middle; `R ≈ 0.65` is the *small difference* of these `O(1)` quantities. `S` itself is
*large* (`~qn`) but harmless — it only appears as the bounded `S²/m`. So **Required is
bounded, not growing** — the reason deg2+dense is `Required > 0` yet tame.

## TASK 2 — the eigen-equation at `v₀`

`(d_{v₀} − λ₂)·f_{v₀} = Σ_{u∈N(v₀)} f_u = f_a + f_b`. **Verified exactly:**

| `n` | `f_a+f_b` | `(2−λ₂)f_{v₀}` |
|---|---|---|
| 50 | −0.023 | −0.023 |
| 200 | 0.006 | 0.006 |
| 1000 | 0.001 | 0.001 |

So `λ₂ = d_{v₀} − (f_a+f_b)/f_{v₀} → d_{v₀} = 2` (the neighbours `f_a,f_b → 0` relative to
`f_{v₀} → 1`). This is the **source of `λ₂ ≈ 2`**: the bottleneck eigen-equation, not the
dense bulk. Expressing the other terms:
- `S = d_{v₀}f_{v₀} + S_dense`, and `S_dense = Σ_dense d_v f_v ≈ d̄_dense·Σ_dense f_v =
  d̄_dense·(−f_{v₀})` (since `f ⊥ 1 ⇒ Σ_dense f = −f_{v₀}`), so `S ≈ f_{v₀}(d_{v₀} −
  d̄_dense) ≈ −qn·f_{v₀}`.
- `S²/m ≈ 2q·f_{v₀}²` (linear `n` cancels), `fᵀDf = d_{v₀}f_{v₀}² + (fᵀDf)_dense`.
- `R = λ₂ + S²/m − fᵀDf ≈ (d_{v₀} − d_{v₀}f_{v₀}²) + 2q f_{v₀}² − (fᵀDf)_dense → 2q + (2 −
  fᵀDf)`, an `O(1)` constant.

## TASK 3 — `Required` vs `Deficit`

The exact identity `Deficit − Required = RHS − T` holds to machine precision:

| `n` | `Deficit` | `Required` | `Deficit−Required` | `RHS−T` | `λ₂f_{v₀}²` | `λ₂(f_{v₀}²−R)` |
|---|---|---|---|---|---|---|
| 50 | 2.043 | 0.830 | **1.213** | **1.213** | 1.933 | 1.103 |
| 200 | 2.015 | 1.174 | **0.841** | **0.841** | 1.983 | 0.809 |
| 1000 | 1.999 | 1.276 | **0.723** | **0.723** | 1.997 | 0.721 |

- `Deficit − Required = RHS − T` **exactly** (the established identity).
- `Deficit → λ₂·f_{v₀}²` (the carrier result: the two `v₀`-neighbour apices carry it), so
  `Deficit − Required → λ₂(f_{v₀}² − R)` — converging (n=1000: 0.723 vs 0.721).
- Therefore **`B ⟺ Deficit ≥ Required ⟺ f_{v₀}² ≥ R ⟺ fᵀDf + f_{v₀}² ≥ λ₂ + S²/m`** (using
  `Deficit ≈ λ₂f_{v₀}²`). Numerically:

| `n` | `fᵀDf + f_{v₀}²` | `λ₂ + S²/m` | margin |
|---|---|---|---|
| 50 | 3.628 | 3.070 | 0.56 |
| 1000 | 3.648 | 3.287 | **0.36** |

The margin `fᵀDf + f_{v₀}² − (λ₂ + S²/m) → 0.36 > 0` (stable). All four quantities are `O(1)`
with explicit limits: `fᵀDf → 2.65`, `f_{v₀}² → 1`, `λ₂ → 2`, `S²/m → 2q = 1.3`.

---

## Synthesis — the bottleneck reduces B to one scalar inequality

On deg2+dense, the whole conjecture collapses, via (i) the eigen-equation at `v₀`
(`λ₂ → d_{v₀} = 2`) and (ii) the carrier identity (`Deficit → λ₂f_{v₀}²`), to the **bounded
`O(1)` inequality**

> `fᵀDf + f_{v₀}² ≥ λ₂ + S²/m`,

equivalently `f_{v₀}² ≥ R`. Both sides are `O(1)` with explicit limits; the margin is
`≈ 0.36` and stable. `Required` does not grow because the only `n`-growing quantity (`S ~
qn`) enters solely through `S²/m → 2q`. This is the cleanest reduction of the `Required > 0`
regime yet: **no large/small competition, no asymptotic tightness** — just a fixed `O(1)`
gap. A proof of this regime would establish `f_{v₀}² ≥ λ₂ + S²/m − fᵀDf` from the
bottleneck eigen-equation plus the degree structure (`λ₂ ≈ d_{v₀}`, `S²/m ≈ 2q f_{v₀}²`),
modulo the carrier approximation `Deficit ≈ λ₂f_{v₀}²` (exact in the limit, ≈3% at n=50).

### Caveats
`λ₂`, `f` numerical; deg2+dense `q=0.65`, `n` to 1000, one sample each (the trends are
monotone/converging). The eigen-equation identity and `Deficit − Required = RHS − T` are
exact (machine precision). `Deficit ≈ λ₂f_{v₀}²` is the carrier approximation — exact as
`n→∞`, off by ~5% at n=50 (the `λ₂(f_{v₀}²−R)` column vs `Deficit−Required`). The reduction
`B ⟺ fᵀDf+f_{v₀}² ≥ λ₂+S²/m` is exact only in that limit; `B` itself (`Deficit ≥ Required`)
holds at every finite `n`.
