# A Lean-formalizable bound on `D_core` that closes `hcond` without matrix inverses

**Goal.** Replace the block-resolvent bound `D_core ≤ ρ·sourceNormSq` (the one remaining
semantic gap in `typeA_slack_ge_required`, needing matrix-inverse / Cauchy-interlacing
infrastructure absent from Mathlib) by a simpler upper bound that

* (a) is a valid upper bound on `D_core` (verified on all 17 Case 2A graphs),
* (b) still closes `hcond`,
* (c) uses only `Finset.sum`, degree, and basic arithmetic — no matrix inverse, no
  spectral decomposition of submatrices.

**Headline result.** The bound is the **exact total-Dirichlet partition identity**

> **`D_core = λ₂ − D_port`**  (equivalently `D_core = λ₂ − D_cross − D_pp`),

where `D_port` is the Dirichlet energy on all port-touching edges. It is an *equality*,
hence the tightest possible valid upper bound, it closes `hcond` (worst ratio **0.935**,
identical to the verified resolvent), and it is provable in **current Mathlib** from
`quadratic_form_eq_edge_sum` (already used in `conjectureB`). It removes the matrix-inverse
dependency entirely.

Scripts: `dcore_simple_bound.py`, `dcore_simple_bound2.py`, `dcore_simple_bound3.py`
(the last is definitive). 17/17 graphs, identical construction to `verify_block_resolvent.py`.

---

## 0. Conventions (a correction worth stating)

`dirichletOn G P f = Σ_{i,j} [G.Adj i j ∧ P i j] (f_i − f_j)²` is an **ordered** double sum,
so it equals **2×** the undirected edge sum. Working undirected (upper-triangle), the verified
`hcond` (matching `verify_block_resolvent.py` `check (d)`, max ratio 0.952) is

```
hcond:   2·[ (δ−1)·D_cross + maxt_core·D_core ]  ≤  RHS         (worst actual ratio 0.9349)
RHS  =   2λ₂·(2·fᵀDf − λ₂ − S²/mE)  =  2λ₂·degQuad − required
```

Each undirected edge falls into exactly one of three classes under the degree-gap port split
`P` (= low-degree vertices):

| class       | both endpoints | energy   | triangle count `t_e`        | coefficient |
|-------------|----------------|----------|-----------------------------|-------------|
| **cross**   | one in `P`     | `D_cross`| ≤ `δ−1` (= `Cp`)            | `Cp = δ−1`  |
| **core**    | none in `P`    | `D_core` | ≤ `maxt_core` (= `Cc`)     | `Cc = maxt` |
| **port-port** | both in `P`  | `D_pp`   | **= 0** (verified, see below)| `0`         |

**Verified structural fact:** in all 17 graphs the port-port edges have `t_e = 0`
(`max port-port triangle count = 0`). Hence they contribute **0** to `triEnergy` and legitimately
carry coefficient `0` — this is exactly why the verified `hcond` uses `D_cross` (cross-only) and
not the full port-touching energy. (Using the full `D_port = D_cross + D_pp` with coefficient
`δ−1` over-charges the high-energy zero-triangle apex edges and the two-class bound fails on the
twin family, ratio → 1.34.)

Total Dirichlet identity (unit Fiedler `f`, `‖f‖=1`, `L f = λ₂ f`):

```
D_cross + D_core + D_pp  =  Σ_E (f_a − f_b)²  =  fᵀ L f  =  λ₂·‖f‖²  =  λ₂.
```

---

## 1. TASK 1 — simple bounds (validity & closure)

Tested as upper bounds on `D_core`, substituted into the verified `hcond`
`2[(δ−1)D_cross + maxt·B] ≤ RHS`:

| bound `B ≥ D_core?`              | valid? | closes? | worst LHS/RHS | min margin `B−D_core` |
|----------------------------------|:------:|:-------:|:-------------:|:---------------------:|
| (a) `λ₂` (total Dirichlet)       | YES    | **no**  | 32.2          | +0.9998               |
| (b) `λ₂ − D_port = λ₂−D_cross−D_pp` (IDENTITY) | YES | **YES** | **0.9349** | −0.0000 (equality) |
| (b′) `λ₂ − D_cross` (drop `D_pp`)| YES    | **no**  | 14.8          | −0.0000               |
| (c) `(|E_core|/|E|)·λ₂` (proportional) | YES | **no** | 16.1          | +0.986                |
| (d) `λ₂·(1 − δ/Δ)` (degree ratio)| YES    | **no**  | 15.7          | +0.933                |
| `D_cross/maxt`                   | **no** | —       | 0.93          | −0.022                |
| `required/(2λ₂·maxt)`            | **no** | —       | 0.64          | −0.082                |
| `D_cross²/λ₂`                    | YES    | **no**  | 31.3          | +0.151                |

**Why everything except the identity fails.** `maxt_core ∈ [20, 80]` but the actual
`D_core ∈ [0.013, 0.090]` and its closure budget `(RHS/2 − Cp·D_cross)/maxt ∈ [0.03, 0.14]`.
Any bound of order `λ₂ ≈ 2` (or `required/2λ₂ ≈ 0.16–0.96`) is multiplied by `maxt` and
overshoots `RHS` by 15–32×. The bound must itself be `≲ 0.1`, i.e. it must capture the genuine
*smallness* of `D_core`. The only elementary quantity that small **and** `≥ D_core` is the
identity value `λ₂ − D_port` (which *equals* `D_core`).

`D_core/budget` worst case = **0.305** (twin) … **0.878** (deg2d): the identity has margin to spare.

---

## 2. TASK 2 — Fiedler flatness on the core

Core-edge flatness `max_{core edge} g_e² / mean_{core edge} g_e²` ranges **4.2 – 24.7**
(mean 13.7): the core Fiedler is **not** pointwise flat. Nonetheless `D_core` is tiny because
the *mean* core-edge energy is minute (`D_core/|E_core| ≈ 2·10⁻⁴`). The proposed flatness
bound `D_core ≲ |E_core|·(λ₂/|E|)` is exactly candidate (c): **valid but does not close**
(ratio 16). Flatness is real in aggregate but the naive `|E_core|·mean` packaging is far too
loose against `maxt`.

---

## 3. TASK 3 — direct substitution `D_core = λ₂ − D_port`

Substituting the identity (the clean three-class version) into `hcond`:

```
2[(δ−1)·D_cross + maxt·(λ₂ − D_cross − D_pp)]
   = 2[ maxt·λ₂ + (δ−1 − maxt)·D_cross − maxt·D_pp ]  ≤  RHS.
```

Since `δ−1 < maxt` (always: `δ−1 ∈ {1,2,3,4}`, `maxt ∈ [20,80]`), the `D_cross` coefficient is
**negative** and the `D_pp` coefficient is negative — **both port masses help**, exactly as the
task anticipated. The substitution reproduces the literal `hcond` (because the identity is exact),
so it closes with the same worst ratio **0.9349**.

The task's hypothesis "edges partition cleanly (`D_cross ≥ 0`)" is confirmed: the three classes
partition all edges and `D_cross + D_core + D_pp = λ₂` exactly. The subtlety the task flagged
(`D_cross` separate from `D_pp`) is real and essential — `D_pp` must be subtracted too
(candidate (b′), which drops `D_pp`, fails on twins).

---

## 4. TASK 4 — best bound

**Best (and essentially only) closing bound: the total-Dirichlet partition identity.**

> Exact statement (Lean normalization, `dirichletOn` = ordered sum):
> ```
> dirichletOn G (¬P) f  =  2·λ₂·‖f‖²  −  dirichletOn G P f
> ```
> i.e. `D_core = (total ordered Dirichlet) − D_port`, with
> `total ordered Dirichlet = Σ_{i,j}[Adj] (f_i−f_j)² = 2·fᵀLf = 2λ₂` for a unit `λ₂`-eigenvector.

* **Valid?** Yes — it is an *equality*, the tightest possible upper bound.
* **Closes `hcond`?** Yes — worst ratio 0.935 (= the verified resolvent's actual value).
* **Lean-formalizable with current Mathlib?** **Yes, with no new infrastructure.** Both ingredients
  already exist in this repo:
  1. the edge-partition split `dirichletOn(P) + dirichletOn(¬P) = Σ_{i,j}[Adj](f_i−f_j)²`
     — pure `Finset` bookkeeping (cf. `triEnergy_split`, which does the identical split for
     `triEnergyOn`);
  2. `Σ_{edge}(f_i−f_j)² = fᵀLf = λ₂·‖f‖²` — exactly `quadratic_form_eq_edge_sum` plus the
     eigenvector step already proved inline in `conjectureB` (`hf_edge_energy`).
* **Estimated Lean difficulty: MODERATE.** The identity itself is trivial/moderate (one
  `Finset.sum` split + reuse of `hf_edge_energy`). See the residual caveat below.

**Bonus self-contained bound.** `D_core ≤ required/(2λ₂)` holds on all 17 (`D_core` uses
1.6 %–57 % of `required/2λ₂`) and needs **no** `D_port` and **no** matrix inverse — only
`required` (the regime-ii quantity, already in scope) and `λ₂`. It does **not** close on its own
(too loose against `maxt`), but it is a clean elementary fact worth recording (it says the core
energy is controlled by the spectral defect `required`).

### Honest caveat — what the identity does and does not remove

The identity *eliminates the matrix-inverse gap*: the unprovable hypothesis
`D_core ≤ ρ·sourceNormSq` of `typeA_slack_ge_required_of_resolvent` is replaced by a **provable
equality**. What remains after substitution is the residual **scalar flatness inequality**

```
2[ (δ−1)·D_cross + maxt·(λ₂ − D_cross − D_pp) ]  ≤  RHS            (validated 17/17, ≤ 0.935)
```

purely in elementary quantities `λ₂, D_cross, D_pp, RHS` — **no matrix inverse, no submatrix
spectrum, no `sourceNormSq`, no `ρ`.** This residual still *encodes* the flatness
(`D_core` small ⇔ `D_port ≈ λ₂`), so to reach a fully `sorry`-free proof it must either be taken
as a hypothesis (exactly as the resolvent bridge takes `hflat`) or be discharged by an
independent lower bound on `D_port`. The net gain is concrete: **one fewer unprovable hypothesis,
and the remaining one is elementary arithmetic on Dirichlet energies rather than resolvent
spectral data.**

---

## 5. TASK 5 — Lean proof sketch

A drop-in replacement bridge (parallel to `typeA_slack_ge_required_of_resolvent`,
`Helpers/BlockResolventBridge.lean`) that needs **no** resolvent hypothesis:

```text
theorem typeA_slack_ge_required_of_dirichlet
    (f : V → ℝ) (lam mE : ℝ) (P : V → V → Prop) (Cp Cc : ℝ)
    (hf_eig  : (G.lapMatrix ℝ).mulVec f = lam • f)         -- f is a λ₂-eigenvector
    (hf_unit : ∑ v, (f v)^2 = 1)                            -- ‖f‖ = 1
    (hport : ∀ i j, G.Adj i j →   P i j → t(i,j) ≤ Cp)      -- mechanical (Cp = δ−1)
    (hcore : ∀ i j, G.Adj i j → ¬ P i j → t(i,j) ≤ Cc)      -- mechanical (Cc = maxt)
    (hCc   : 0 ≤ Cc)
    (hflat : Cp · dirichletOn G P f
             + Cc · (2*lam - dirichletOn G P f)             -- D_core REWRITTEN by the identity
             ≤ 2*lam*(2*degQuad G f - lam - (degLin G f)^2/mE)) :
    required G f lam mE ≤ aggregateSlack G f lam := by
  -- STEP 1 (the new ingredient): the total-Dirichlet partition identity.
  --   dirichletOn(P) + dirichletOn(¬P) = Σ_{i,j}[Adj](f_i−f_j)²            -- Finset split
  --                                     = 2 · (fᵀ L f)                      -- ordered = 2×edge
  --                                     = 2 · lam · ‖f‖² = 2·lam.           -- hf_eig, hf_unit
  -- Hence  dirichletOn(¬P) = 2*lam − dirichletOn(P).      (D_core = 2λ − D_port)
  have hId : dirichletOn G (fun i j => ¬ P i j) f = 2*lam - dirichletOn G P f := by
    -- (i) edge-partition split, mirroring `triEnergy_split`:
    --     Σ_{i,j}[Adj](f_i−f_j)² = dirichletOn P + dirichletOn ¬P
    -- (ii) Σ_{i,j}[Adj](f_i−f_j)² = 2 · ∑_{e∈edgeSet} (f_a−f_b)²   (ordered = 2×)
    -- (iii) ∑_{e} (f_a−f_b)² = lam     (quadratic_form_eq_edge_sum + hf_eig + hf_unit,
    --        i.e. exactly the `hf_edge_energy` computation reused from `conjectureB`)
    sorry  -- moderate: pure Finset + reuse of existing energy lemma
  -- STEP 2: rewrite hcond's D_core via the identity, then apply the existing partition bound.
  have hcond : Cp * dirichletOn G P f
             + Cc * dirichletOn G (fun i j => ¬ P i j) f
             ≤ 2*lam*(2*degQuad G f - lam - (degLin G f)^2/mE) := by
    rw [hId]; exact hflat
  -- STEP 3: the existing sorry-free chain — identical to the resolvent bridge from here.
  exact slack_ge_required_of_triEnergy_le_RHS G f lam mE
    (triEnergy_le_of_partition G P f Cp Cc _ hport hcore hcond)
```

Only **STEP 1** (`hId`) is new, and it is elementary:

* the `Finset` partition split is a copy of `triEnergy_split`'s proof with the triangle weight
  `|N(i)∩N(j)|` deleted (so it is strictly easier);
* the "`= λ₂`" step is the exact `hf_edge_energy` block already written and verified inside
  `conjectureB` (`quadratic_form_eq_edge_sum` → eigenvector → unit norm); it can be factored out
  as a small lemma `edge_dirichlet_eq_lam` and shared.

Everything downstream (`triEnergy_le_of_partition`, `slack_ge_required_of_triEnergy_le_RHS`) is
already `sorry`-free. Net effect: the matrix-inverse hypothesis `hDcore` of the resolvent bridge
is **deleted**, replaced by the provable `hId`; the surviving `hflat` is the same kind of
validated scalar inequality the resolvent bridge already required, now stated in elementary
Dirichlet/eigenvalue terms.

---

## Appendix — per-graph data (verified convention)

```
graph         D_core   budget   Dc/bud   D_cross  D_pp     λ₂      maxt  δ−1  hcond
deg2d40_0.6   0.0879   0.1200   0.733    1.8792   0.0000   1.9671  22    1    0.8438
deg2d40_0.85  0.0596   0.0752   0.793    1.9337   0.0000   1.9934  33    1    0.8838
deg2d60_0.4   0.0898   0.1307   0.688    1.8579   0.0000   1.9477  20    1    0.8174
deg2d60_0.6   0.0536   0.0801   0.668    1.9281   0.0000   1.9817  30    1    0.8160
deg2d60_0.85  0.0397   0.0465   0.852    1.9554   0.0000   1.9950  50    1    0.9196
deg2d80_0.4   0.0576   0.1003   0.574    1.9117   0.0000   1.9693  24    1    0.7627
deg2d80_0.6   0.0384   0.0560   0.686    1.9492   0.0000   1.9876  41    1    0.8301
deg2d80_0.85  0.0294   0.0335   0.878    1.9669   0.0000   1.9963  67    1    0.9349
twin30_2      0.0439   0.0987   0.444    0.6567   0.3432   1.0437  30    2    0.6152
twin30_3      0.0408   0.1124   0.363    0.6207   0.6639   1.3254  30    3    0.5894
twin30_4      0.0338   0.1138   0.297    0.5276   0.9417   1.5031  30    4    0.5655
twin50_2      0.0264   0.0544   0.486    0.6607   0.3392   1.0264  50    2    0.6543
twin50_3      0.0248   0.0619   0.401    0.6260   0.6517   1.3025  50    3    0.6273
twin50_4      0.0209   0.0629   0.332    0.5344   0.9219   1.4772  50    4    0.6024
twin80_2      0.0166   0.0322   0.515    0.6629   0.3370   1.0166  80    2    0.6794
twin80_3      0.0156   0.0366   0.427    0.6290   0.6449   1.2895  80    3    0.6518
twin80_4      0.0133   0.0372   0.356    0.5383   0.9111   1.4627  80    4    0.6264

worst literal hcond ratio = 0.9349     max port-port triangle count = 0
```
