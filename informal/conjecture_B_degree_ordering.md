# Conjecture B — is the lock controlled by degree ordering, not Fiedler values?

Tests the hypothesis that the lock `W = Σ_v(d_v−δ)D_v⁺` (unit Fiedler `f`,
`D_v⁺ = Σ_{b∼v, d_b>d_v}(f_v−f_b)²`) is governed by the **degree sequence**, by
comparing it to the purely combinatorial
`H_v = (d_v−δ)·|N_v⁺|`, `N_v⁺ = {b∼v : d_b>d_v}`. Code:
[`conjecture_B_degree_ordering.py`](../conjecture_B_degree_ordering.py).
Data: 52 tight + 1051 broad + 630 dense, all `T(G)`-connected.

**Verdict (nuanced).** Degree ordering controls the **structure** of `W` (where it
concentrates: `corr(W_v,H_v)=0.95` on tight graphs) but **not its magnitude**: the
purely combinatorial reduction (item 5) **fails** — replacing the Fiedler gradient
by its trivial cap `λ₂` overshoots `R''` by ~60×. The Fiedler geometry enters
irreducibly through one scalar per graph, the **average uphill gradient**
`ρ = W/ΣH ≈ 0.014·λ₂`. The **Chebyshev sum inequality** is the right rigorous
encoding of the anticorrelation and nearly closes the gap (~83%), but is defeated
by imperfect monotonicity (~5%).

---

## Rigorous combinatorial facts established

- **`ΣH := Σ_v H_v = Σ_{ab∈E}(min(d_a,d_b)−δ)`** (verified, err 0) — purely
  combinatorial (degree sequence only); the same min-degree weights as `W`, with
  the Fiedler gradient stripped out.
- **`ΣH ≤ ½Σ_v d_v² − mδ`** (verified) — by `min ≤ average` + handshaking
  (`Σ_{ab}(d_a+d_b)=Σ_v d_v²`); expressible via degree variance
  `Σd_v² = n(σ²_d + d̄²)`.
- **`W ≤ λ₂·ΣH`** (rigorous) — every edge gradient `(f_a−f_b)² ≤ Σ_e(f_a−f_b)² =
  λ₂`, so `W = Σ w_e g_e ≤ λ₂ Σ w_e`. (Holds 52/52, 1039/1051, 628/630; the few
  misses are near-zero-λ₂ numerics.)

---

## 1. Correlation `corr(W_v, H_v)` — structure is combinatorial

| set | pooled `r` | per-graph mean `r` |
|---|---|---|
| **tight (52)** | 0.835 | **0.948** |
| broad | 0.589 | 0.718 |
| dense | 0.577 | 0.691 |

On the tightest graphs the combinatorial `H_v` predicts the lock contribution `W_v`
almost perfectly (`r=0.95`); generally `r≈0.7`. So **which vertices carry `W` is a
degree-ordering fact** — strongly so near tightness. (This is consistent with the
v4/three-projects finding that on tight graphs the hubs carry zero uphill energy.)

## 2–3. But the magnitude `ρ = W/ΣH` is ≪ λ₂

`W_v/H_v` is the average uphill gradient² at `v`; `ρ = W/ΣH` is the global
`(d−δ)`-weighted average uphill gradient. Both are **far below** `λ₂`:

| set | max `(W_v/H_v)/λ₂` | max `ρ/λ₂` | median `ρ/λ₂` |
|---|---|---|---|
| tight | 0.056 | 0.056 | **0.017** |
| broad | 0.168 | 0.259 | 0.014 |
| dense | 0.161 | 0.114 | 0.014 |

So `ρ ≈ 0.014·λ₂` typically — the trivial bound `W ≤ λ₂·ΣH` is loose by **~60×**.
The smallness of `ρ` *is* the anticorrelation (large-weight edges carry tiny
gradients), and it is exactly what a combinatorial count cannot see.

## 4. The combinatorial sum is too big

| set | median `ΣH` | median `fᵀDf` | median `ΣH/fᵀDf` |
|---|---|---|---|
| tight | 10.0 | 6.07 | **1.76** |
| broad | 30.0 | 5.43 | 5.55 |
| dense | 35.0 | 5.53 | 6.21 |

`ΣH` exceeds `fᵀDf` by 1.8–6×, and `R''/λ₂ = fᵀDf−λ₂+1−S²/m < fᵀDf`.

## 5. The proposed combinatorial reduction — **fails**

| set | `W ≤ λ₂·ΣH` | `λ₂·ΣH ≤ R''` | lock `W ≤ R''` |
|---|---|---|---|
| tight | 52/52 | **21/52** | 52/52 |
| broad | 1039/1051 | **71/1051** | 1050/1051 |
| dense | 628/630 | **24/630** | 630/630 |

The chain `W ≤ λ₂·ΣH ≤ R''` collapses: `λ₂·ΣH ≤ R''` (equivalently
`ΣH ≤ R''/λ₂`) holds on only **5–40%** of graphs. **Conjecture B does NOT reduce
to a purely combinatorial inequality** via the trivial gradient bound — the ~60×
factor `ρ/λ₂` is essential, and it depends on the Fiedler geometry.

## 6. Chebyshev sum inequality — the right tool, ~83% but not universal

The anticorrelation (weight `w_e=min(d_a,d_b)−δ` vs gradient `g_e`, `corr≈−0.7`)
is exactly the hypothesis of **Chebyshev's sum inequality**: if `w` and `g` are
oppositely ordered, `Σ w_e g_e ≤ (1/m_up)(Σw_e)(Σg_e) = ΣH·(Σ_{uphill}g)/m_up =:
CB`. With `Σ_{uphill}g ≤ λ₂`:

| set | `W ≤ CB` | `CB ≤ R''` | `W ≤ CB'=ΣH·λ₂/m_up` | `CB' ≤ R''` |
|---|---|---|---|---|
| tight | 52/52 | 41/52 (79%) | 52/52 | 41/52 |
| broad | 993/1051 (94%) | 870/1051 (83%) | 1022/1051 | 844/1051 |
| dense | 602/630 (96%) | 524/630 (83%) | 620/630 | 507/630 |

Chebyshev tightens the bound by the factor `(Σ_{uphill}g)/(λ₂·m_up) ≈ 1/m_up`,
lifting `CB ≤ R''` to **~83%** (vs 5–40% for the trivial bound). **But it is not a
proof:** `W ≤ CB` itself fails on ~5% (the weight/gradient ordering is
`corr≈−0.7`, not perfectly monotone — Chebyshev's hypothesis is violated), and
`CB ≤ R''` fails on ~17% (residual constant). Both gaps are small but real.

---

## Synthesis

- **Structure is combinatorial, magnitude is spectral.** Degree ordering predicts
  *where* `W` lives (`corr(W_v,H_v)=0.95` tight), but the *size* of `W` is carried
  by the average uphill gradient `ρ = W/ΣH ≈ 0.014·λ₂`, which no degree count
  captures. The hypothesis "Fiedler geometry is secondary" is **true for the
  support, false for the magnitude.**
- **Cleanest reframing.** `B ⟺ ρ ≤ R''/ΣH`, i.e. the `(d−δ)`-weighted average
  uphill Fiedler gradient is at most `R''/ΣH`, where `ΣH = Σ_{ab}(min(d_a,d_b)−δ)`
  is purely combinatorial (and `≤ ½Σd² − mδ`). The whole difficulty is the single
  scalar `ρ`.
- **The rigorous tool is Chebyshev's sum inequality**, not a degree count: it
  encodes the anticorrelation and gets ~83% of the way. A proof needs (a) a
  **monotone-rearrangement** fix for the ~5% where `w,g` are not oppositely sorted
  (e.g. sorting uphill edges by weight and bounding the gradient tail), and (b) a
  tighter handle on `Σ_{uphill}g ≤ λ₂` (most uphill gradient mass is small) to
  close the residual ~17%.

### Caveats
- `λ₂` numerical; ties in degree handled by excluding strict-uphill count. The
  `W ≤ λ₂·ΣH` / `W ≤ CB` misses on broad/dense are dominated by near-zero-λ₂
  numerical cases. `T(G)`-connected graphs only, `n ≤ 14`.
