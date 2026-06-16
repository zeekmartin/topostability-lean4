# Conjecture B — proof v2: triangle-free reduction + the near-optimality theorem

**Conjecture B.** For `G` with `T(G)` connected, `λ₂(T(G)) ≤ λ₂(G)`. Proved for
regular `G`; open for irregular `G`.

This builds on [`conjecture_B_proof_attempt.md`](conjecture_B_proof_attempt.md)
(the lift reduction `B ⟸ μ(G) ≤ λ₂(G)`). v2 contributes:

1. Two **machine-exact operator identities** that recast `μ(G)` as a
   Rayleigh–Ritz value — giving a clean **structural reason** the Fiedler-lift is
   near-optimal (`μ ≈ λ₂(T)`).
2. A **triangle-free reduction**: using a Lean-verified edgewise bound, `B`
   reduces to a **degree-only** spectral inequality on the Fiedler vector — the
   triangle counts `t_{ab}` are eliminated entirely.
3. An **exact closed form** for that inequality via a derived degree-sum
   identity, isolating the one remaining analytic obstruction.

Code: [`conjecture_B_proof_v2_explore.py`](../conjecture_B_proof_v2_explore.py).
Status: still **not a closed proof**, but the remaining gap is now a clean,
triangle-free, degree-only inequality verified on 4000+ graphs.

---

## 1. Operator identities (rigorous, machine-exact)

With `B` the **unsigned** incidence matrix (`|V|×|E|`), `L_{T(G)}` the triangle-
graph Laplacian, `L_t` the triangle-weighted Laplacian (edge weight
`t_{ab}=|N(a)∩N(b)|`), `Q=D+A` the signless Laplacian:

> **`L_t = B · L_{T(G)} · Bᵀ`**  and  **`Q = B · Bᵀ`.**

Both verified to `0.00e+00` on every test graph. The first is Lemma 1 of v1
(the lift's `T(G)`-energy is the triangle-weighted energy) written as a matrix
identity; the second is the standard `BBᵀ = D+A`.

**Consequence.** The reduction's quantity
`μ(G) = min_{φ⟂d} (φᵀL_tφ)/(φᵀQφ)` becomes
`min_{φ⟂d} (φᵀ B L_{T(G)} Bᵀ φ)/(φᵀ BBᵀ φ)` — a **Rayleigh–Ritz quotient** of
`L_{T(G)}` restricted to the additive subspace `U = range(Bᵀ) ⊆ ℝ^E`
(the edge-vectors of the form `h_e = φ_u+φ_v`).

---

## 2. Why the Fiedler-lift is near-optimal (Rayleigh–Ritz theorem)

**Theorem.** For connected non-bipartite `G`, `μ(G)` is the second-smallest
**Ritz value** of `L_{T(G)}` on the `n`-dimensional additive subspace
`U = range(Bᵀ)`. By Cauchy interlacing `λ₂(T(G)) ≤ μ(G)`, with **equality iff the
`T(G)`-Fiedler vector lies in `U`** (i.e. is *additive*, `ψ_e = φ_u+φ_v`).

*Proof.* `U` contains `1_E` (`= Bᵀ(½·1)`, since for non-bipartite `G` the only
solution of `φ_u+φ_v=1` on all edges is `φ≡½`). The orthogonal projector onto `U`
is `P_U = Bᵀ(BBᵀ)^{-1}B`. The generalized eigenvalues of `(BL_{T(G)}Bᵀ, BBᵀ)`
are the eigenvalues of the compression `P_U L_{T(G)} P_U |_U`; `φ⟂d ⟺ Bᵀφ⟂1_E`
(v1 Lemma 3) removes the `1_E` (zero) mode, leaving `μ(G)` as the second Ritz
value. Ritz values interlace the true spectrum (Cauchy), and the lowest nonzero
Ritz value equals `λ₂(T(G))` exactly when the corresponding eigenvector is in the
trial space `U`. ∎

**This answers the empirical "`μ ≈ λ₂(T)`":** the `T(G)`-Fiedler vector is *almost
additive*. Measured directly, the additive overlap `‖P_U ψ_T‖` (with `ψ_T` the
unit `T(G)`-Fiedler) is **≥ 0.9856 on every one of the 52 tightest irregular
graphs**, and the Ritz gap `μ − λ₂(T) ≤ 0.206`. The lift route therefore loses
almost nothing — `T(G)`'s slowest mode is, to >98%, a vertex-additive function.

| graph | overlap `‖P_U ψ_T‖` | `μ − λ₂(T)` |
|---|---|---|
| `K10−e`, `K9−e`, `K8−e` | 1.0000 | 0.000 (lift exact) |
| rand-tight Q1.190 | 0.9983 | 0.025 |
| rand-tight Q1.232 | 0.9977 | 0.031 |
| min over all 52 | **0.9856** | ≤ 0.206 |

---

## 3. Triangle-free reduction (the main v2 result)

**Edgewise bound (Lean-verified).** For every edge `{u,v}`,
`t_{uv} = |N(u)∩N(v)| ≤ min(deg u, deg v) − 1`
(the common neighbours lie in `N(u)\{v}` and `N(v)\{u}`). Verified in Lean
against the repo's `triCount`:

```lean
theorem triCount_le_min_degree_sub_one (u v : V) (h : G.Adj u v) :
    triCount G u v ≤ min (G.degree u) (G.degree v) - 1
```
(`check_file OK` on Modal; also the one-sided `triCount_le_degree_sub_one`).

**Reduction.** Let `f` be the unit Fiedler vector (`L_G f = λ₂ f`, `f⟂1`),
`d` the degree vector, `S = fᵀd = Σ_v deg(v)f_v`, `m=|E|`. Define the
**min-degree-weighted Laplacian** `L_md` (edge weight `min(d_a,d_b)−1`). Then:

> **Conjecture B holds whenever**
> **`(DEG):  fᵀ L_md f  ≤  λ₂ · (fᵀ Q f − S²/m)`.**

*Proof.* The S2 test vector `h' = Bᵀf − (S/m)1_E ⟂ 1_E` has, by the v1 identities,
`R_{T(G)}(h') = fᵀL_t f / (fᵀQf − S²/m)`. The edgewise bound gives
`fᵀL_t f = Σ_{ab} t_{ab}(f_a−f_b)² ≤ Σ_{ab}(min(d_a,d_b)−1)(f_a−f_b)² = fᵀL_md f`.
So `(DEG) ⟹ R_{T(G)}(h') ≤ λ₂ ⟹ λ₂(T(G)) ≤ λ₂(G)`. ∎

**The triangle counts are gone.** `(DEG)` involves only degrees and the Fiedler
vector. It is verified on **every one of 4000+ graphs** across three independent
sweeps (52 tightest irregular; 2107 structured+random `n=6..11`, all densities;
1845 more) — **0 failures**.

**`min` is essential — looser degree bounds fail:**

| upper bound on `t_{ab}` | closes `(DEG)`? |
|---|---|
| `Δ − 1` (crude, constant) | 16/52 ❌ |
| `(d_a+d_b)/2 − 1` (degree average) | 1810/2107 ❌ |
| `√((d_a−1)(d_b−1))` (geometric mean) | 1740/1845 ❌ |
| **`min(d_a,d_b) − 1`** | **4000+/4000+ ✅** |

So a proof must use the **minimum** degree per edge; average/geometric-mean
relaxations overshoot on irregular graphs.

---

## 4. Exact closed form of `(DEG)`

Two exact identities (both verified to `<1e-13`) reduce `(DEG)` to a transparent
form. Using `L_G f = λ₂ f`:

**Degree-sum identity.**
`Σ_{ab∈E}(d_a+d_b)(f_a−f_b)² = 2λ₂·(fᵀDf) + Σ_v f_v²·disc(v)`,
where `disc(v) = Σ_{b∼v}(d_b − d_v)` is the **degree discrepancy** at `v`
and `fᵀDf = Σ_v deg(v) f_v²`.

**Min/average decomposition.**
`min(d_a,d_b) − 1 = (d_a+d_b)/2 − 1 − |d_a−d_b|/2`, hence
`fᵀL_md f = λ₂·(fᵀDf) + ½Σ_v f_v²·disc(v) − λ₂ − ½Σ_{ab}|d_a−d_b|(f_a−f_b)²`.

Since `fᵀQf = 2fᵀDf − λ₂`, the inequality `(DEG)` is **equivalent** to:

> **`(DEG′):  ½ Σ_v f_v²·disc(v) − ½ Σ_{ab}|d_a−d_b|(f_a−f_b)²`**
> **`≤  λ₂·( fᵀDf − λ₂ + 1 − S²/m )`.**

**What this isolates.**
- For **regular** `G`: `disc ≡ 0`, all `|d_a−d_b| = 0`, `S=0`, `fᵀDf=δ`; `(DEG′)`
  reads `0 ≤ λ₂(δ−λ₂+1)`, true since `λ₂ ≤ δ`. (Recovers the known regular case.)
- The whole open content is the **irregular** part: the signed degree-discrepancy
  `Σ_v f_v² disc(v)` must be dominated by `λ₂(fᵀDf − λ₂ + 1 − S²/m)` *plus* the
  degree-gap-weighted Fiedler energy `½Σ|d_a−d_b|(f_a−f_b)²`. Both correction
  terms are degree-irregularity measures that vanish together; the remaining task
  is a quantitative comparison of `disc(v)` (weighted by `f_v²`) against the
  Fiedler spectral data. This is the natural next target — now a statement about
  degrees and one eigenvector, with no triangle combinatorics.

---

## 5. Lean verification (Modal)

Verified with `lake env lean` against `Topostability.Defs`
(`modal run modal_lean.py::check_file`, `check_file OK`):

- `triCount_le_degree_sub_one`  : `triCount u v ≤ deg(u) − 1` for `u ~ v`.
- `triCount_le_min_degree_sub_one` : `triCount u v ≤ min(deg u, deg v) − 1`.

These are the rigorous foundation of §3's triangle-elimination step. (v1 also
verified `edgeLift_eval` and `edgeLift_diff_triangle`, the numerator identity.)
The operator identities (§1) and degree-sum identity (§4) are finite linear
algebra, verified numerically to machine precision; the reduction (§3) and
Ritz theorem (§2) are min–max arguments over `ℝ^E`/`ℝ^V`.

---

## 6. Status and caveats

- **Rigorous:** operator identities, the Ritz/near-optimality theorem, the
  triangle-free reduction `(DEG) ⟹ B`, the Lean edgewise bound, and the exact
  equivalence `(DEG) ⟺ (DEG′)`.
- **Open (conjectural, strong evidence):** the degree-only inequality `(DEG)`
  itself — verified on 4000+ graphs (`n≤11`), 0 failures, but unproven in general.
  Proving `(DEG′)` would complete Conjecture B for all graphs.
- Tests: structured families (`K_n−ke`, complete multipartite, split/threshold) +
  broad random sweeps, all densities with `T(G)` connected; `λ₂` numerical
  (`eigvalsh`, tol 1e-9). Non-bipartite assumed (bipartite `G` has no triangles).
- The lift route is sufficient but not proven necessary; `μ ≈ λ₂(T)` (§2) shows
  it is nearly tight in practice.
