# Conjecture B — candidate lemmas for uniform smallness of ρ: a decisive negative + one live lead

Goal: find a provable bound on `ρ = W/ΣH` (the `(min−δ)`-weighted average uphill
Fiedler gradient) closing the lock `W ≤ R'' = λ₂(fᵀDf−λ₂+1−S²/m)`. Code:
[`conjecture_B_rho_lemmas.py`](../conjecture_B_rho_lemmas.py). Hard set: 1957
irregular `T(G)`-connected graphs (tight + Chebyshev outliers + dense + dense
Watts–Strogatz), `n ≤ 29`.

**Decisive result.** A *uniform* bound `ρ ≤ c·λ₂` — the strategy suggested by
"`ρ ≤ 0.104λ₂` across the corpus" — **cannot close Conjecture B.** The gating test
shows the required bound is graph-dependent and can be ~60× smaller than the
uniform ceiling. Of the five directions, four are dead for closing the lock; only
the **normalized Laplacian (D4)** yields the correct `fᵀDf`-scaled form, with one
explicit open sub-inequality.

---

## Gating test — uniform `ρ ≤ c·λ₂` is insufficient

`ρ ≤ c·λ₂` closes the lock iff `c·λ₂·ΣH ≤ R''` for all graphs, i.e. iff
`max_G ρ/λ₂ ≤ min_G R''/(λ₂·ΣH)` (separation). Measured over 1957 graphs:

| quantity | value |
|---|---|
| `max_G ρ/λ₂` (uniform ceiling) | **0.1044** |
| `min_G R''/(λ₂·ΣH)` (tightest required) | **0.0018** |

**Not separated** (`0.1044 ≫ 0.0018`). On the binding graph (a large dense
Watts–Strogatz, big `ΣH`, modest `fᵀDf`) the lock demands `ρ ≤ 0.0018·λ₂`, while a
uniform `c = 0.05` would assert `ρ ≤ 0.05λ₂` and **overshoot the requirement 28×**.
So although `ρ ≤ 0.104λ₂` is empirically *true* (and the lock holds 1956/1957),
the uniform bound is **useless for the proof**: the admissible bound on `ρ` scales
as `R''/ΣH ≈ (fᵀDf−λ₂+1−S²/m)/ΣH`, which depends on the **degree-weighted Fiedler
norm `fᵀDf` and the combinatorial mass `ΣH`** — not on `λ₂` alone.

> **Takeaway.** Abandon "uniform `ρ` smallness." Any closing bound must carry the
> `fᵀDf/ΣH` scaling. This is why pure-`λ₂` lemmas (D1, D5 below) fail and the
> `fᵀDf`-aware D4 is the only candidate with the right shape.

---

## The five directions — concrete lemma, test, verdict

### D1. Weighted Poincaré: `W ≤ λ₂·(fᵀDf − δ)`
- **max `W/(λ₂(fᵀDf−δ)) = 2.47`**, holds on only **40%**. ❌ **False.** Counterexamples
  are dense irregular graphs where `W` exceeds `λ₂(fᵀDf−δ)` by up to 2.5×.
- *Could imply C4″?* No — fails outright, and is a pure-`λ₂` form (wrong scaling).

### D2. Fiedler smoothness on degree-level sets
- The uphill gradient energy carried by the **upper-half degree levels is only 31%**
  of the total (lower-degree levels carry 69%) — a clean quantitative confirmation
  of *flat-at-hubs*. But this is a *structural* fact, not an inequality bounding `W`
  by `R''`; no clean per-level bound emerged.
- *Could imply C4″?* Not on its own — supplies intuition, not a closing bound.

### D3. Rearrangement without monotonicity (gradient-mass decay)
- Gradient mass `G_w` (gradient on weight-`w` edges) is monotone-decreasing in `w`
  on only **66%** of graphs; the top weight-class carries on average 18% of `W`
  (but up to **100%** on some graphs). So the decay is statistical, not structural —
  exactly why Chebyshev/rearrangement cannot be made rigorous (no monotone order).
- *Could imply C4″?* No — the absence of guaranteed monotone decay is the same
  obstruction that defeats Chebyshev (cf. `conjecture_B_chebyshev_outliers.md`).

### D4. Normalized Laplacian — **the live lead**
With `μ₂` = second eigenvalue of `L_norm = I − D^{-1/2}AD^{-1/2}`:
- **`μ₂·fᵀDf ≤ R''` holds on 100%** of the hard set — the correct `fᵀDf`-scaled
  lower proxy for `R''`, and the *only* clean inequality here that respects the
  scaling the gating test demands.
- But **`W ≤ μ₂·fᵀDf` fails on 15%** (max ratio `W/(μ₂·fᵀDf) = 3.23`). So `W` and
  `μ₂·fᵀDf` both lie below `R''`, but neither dominates the other.
- `ρ ≤ μ₂·d̄` (avg degree): max ratio `0.084` — `ρ` is also small relative to the
  *normalized* gap, but again not a closing chain.
- *Could imply C4″?* **Potentially** — this is the one direction with the right
  form. It reduces B to the single open inequality **`W ≤ μ₂·fᵀDf`** (or a
  variant), which is *correct on 85%* and exceeds by at most 3.2× on the rest.
  The remaining work is to close that ~3× gap on the 15% (likely the same
  high-`ΣH` Watts–Strogatz regime that binds the gating test).

### D5. Conductance / sweep on uphill edges: `g_e·min(d_a,d_b) ≤ c·λ₂`
- The per-edge inverse-degree bound holds with **`c = 1.29`** (every edge:
  `(f_a−f_b)²·min(d_a,d_b) ≤ 1.29 λ₂`). But propagating it, `W ≤ c·λ₂·m_up`, gives
  `c·λ₂·m_up ≤ R''` on **0%** — the edge count `m_up` is far too large.
- *Could imply C4″?* No — a per-edge bound loses the collective anticorrelation
  (consistent with the earlier finding that the sum structure is essential).

---

## Synthesis and redirection

1. **The uniform-`ρ` program is closed (negative).** The gating test refutes any
   `ρ ≤ c·λ₂`: the lock's required margin `R''/(λ₂ΣH)` ranges down to `0.0018`,
   while `ρ/λ₂` reaches `0.104`. Uniform smallness is true but cannot prove B.
2. **The scaling must be `fᵀDf/ΣH`, not `λ₂`.** This kills D1 and D5 (pure-`λ₂`)
   and explains why D4 (the only `fᵀDf`-aware candidate) is the survivor.
3. **One open inequality remains as the lead:** the normalized-Laplacian bound
   **`W ≤ μ₂·fᵀDf`** (`μ₂ = λ₂(L_norm)`). It is true on 85% and, crucially,
   `μ₂·fᵀDf ≤ R''` is true on **100%** — so proving `W ≤ μ₂·fᵀDf` would prove
   Conjecture B. The gap (≤3.2×, on ~15% high-`ΣH` graphs) is the precise next
   target; D2's flat-at-hubs (gradient concentrated on low-degree levels) is the
   structural fact a proof of it would exploit.

### Caveats
- `λ₂`, `μ₂`, `f` numerical; hard set is irregular `T(G)`-connected, `n ≤ 29`,
  deliberately including the dense-Watts–Strogatz regime that stresses `ΣH`.
- The lock `W ≤ R''` holds 1956/1957 (one near-zero-`λ₂` numerical miss).
- `μ₂·fᵀDf ≤ R''` at 100% and `W ≤ μ₂·fᵀDf` at 85% are empirical (this corpus),
  not proven; they are stated as candidate lemmas, with the 15% gap a counterexample
  set to the strong form `W ≤ μ₂·fᵀDf`.
