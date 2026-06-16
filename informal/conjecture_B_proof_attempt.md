# Conjecture B — proof attempt via the Fiedler-lift route

**Conjecture B (Paper 14).** For a graph `G` with `T(G)` connected,
`λ₂(T(G)) ≤ λ₂(G)` (the triangle graph's algebraic connectivity never exceeds
`G`'s). Proved for **regular** `G`; **open** for irregular `G`.

## 0. Status (honest summary)

This is **not** a complete proof. What it is:

1. A **rigorous reduction** of Conjecture B to a single clean spectral
   inequality `μ(G) ≤ λ₂(G)` (Theorem 2), via the unsigned Fiedler lift.
2. Two **Lean-verified** algebraic anchors of the reduction's numerator
   identity (`edgeLift_eval`, `edgeLift_diff_triangle`, checked on Modal against
   the repo's actual `triangleGraph`/`edgeLift`).
3. Numerical confirmation that the reduction's hypothesis `μ(G) ≤ λ₂(G)` holds
   on **52/52** of the tightest irregular graphs (the regime where the
   regular-case proof breaks), with the lift **near-optimal** (`μ ≈ λ₂(T)`).
4. A precise localisation of the **remaining gap**, and elimination of three
   tempting shortcuts (degree-reparametrisation, crude `t ≤ Δ−1` bound, and the
   unconstrained operator inequality) that provably **cannot** close it.

The crux `μ(G) ≤ λ₂(G)` remains conjectural — but it is now a much cleaner,
constraint-localised statement than the original.

Exploration code: [`conjecture_B_proof_explore.py`](../conjecture_B_proof_explore.py).

---

## 1. The lift identity (rigorous; Lean-verified core)

Let `B` be the **unsigned** vertex–edge incidence matrix (`|V|×|E|`,
`B[v,e]=1` iff `v∈e`). For `φ : V → ℝ` define the edge vector
`h = Bᵀφ`, i.e. `h_e = φ_u + φ_v` for `e={u,v}` — the repo's `edgeLift`.

**Lemma 1 (numerator).**
`hᵀ L_{T(G)} h = Σ_{(a,b)∈E} t_{ab} (φ_a − φ_b)²  =  φᵀ L_t φ`,
where `t_{ab} = |N(a)∩N(b)|` is the number of triangles through edge `ab`, and
`L_t` is the **triangle-weighted Laplacian** (edge weight `t_{ab}`).

*Proof.* `T(G)`'s edges are the triangle-adjacencies: `e₁=s(u,v)`, `e₂=s(u,w)`
adjacent iff `G.Adj v w`. Across such an edge the lift changes by
`(φ_u+φ_v) − (φ_u+φ_w) = φ_v − φ_w` — the difference of the two **opposite**
vertices, which are `G`-adjacent (they close the triangle `u,v,w`). Each
triangle `{a,b,c}` contributes its three sides as three `T(G)`-edges, summing
`(φ_a−φ_b)² + (φ_b−φ_c)² + (φ_a−φ_c)²`. Summing over all triangles, the
coefficient of `(φ_a−φ_b)²` is the number of triangles containing edge `ab`,
namely `t_{ab}`. ∎

The atomic step (lift difference across a `T(G)`-edge `= φ_v − φ_w`) is
**Lean-verified**:

```lean
theorem edgeLift_diff_triangle {R} [AddCommGroup R] (f : V → R)
    (u v w : V) (h1 : s(u, v) ∈ G.edgeSet) (h2 : s(u, w) ∈ G.edgeSet) :
    edgeLift G f ⟨s(u, v), h1⟩ - edgeLift G f ⟨s(u, w), h2⟩ = f v - f w := by
  rw [edgeLift_eval, edgeLift_eval]; abel
```
(checked with `lake env lean` on Modal — `check_file OK`).

**Lemma 2 (denominator).** `hᵀh = φᵀ(D+A)φ = φᵀ Q φ`, where `Q = D+A = BBᵀ` is the
**signless Laplacian**.
*Proof.* `BBᵀ[u,v]` = number of edges containing both `u,v` = `deg(u)` if `u=v`,
else `A[u,v]`; so `BBᵀ = D+A`, and `hᵀh = φᵀBBᵀφ`. ∎

**Lemma 3 (orthogonality).** `h ⟂ 1_E  ⟺  φ ⟂ d`, where `d=(deg v)_v`.
*Proof.* `1_Eᵀh = φᵀ(B 1_E) = φᵀ d`. ∎

All three are confirmed numerically to machine precision on every test graph.

---

## 2. The reduction theorem (rigorous)

**Theorem.** Let `G` be connected and **non-bipartite** with `T(G)` connected.
Define
```
  μ(G) = min { φᵀ L_t φ / φᵀ Q φ : φ ⟂ d, φ ≠ 0 }.
```
Then `λ₂(T(G)) ≤ μ(G)`. Consequently **Conjecture B holds whenever
`μ(G) ≤ λ₂(G)`**.

*Proof.* `λ₂(T(G)) = min { ψᵀL_{T(G)}ψ / ψᵀψ : ψ ⟂ 1_E }`. The lifts
`{ Bᵀφ : φ ⟂ d }` form a subspace of the test space `1_E^⟂` (Lemma 3), and
`Bᵀ` is injective (a connected non-bipartite graph has full incidence rank `n`),
so each nonzero `φ⟂d` gives a nonzero test vector. By Lemmas 1–2 its Rayleigh
quotient is exactly `φᵀL_tφ / φᵀQφ`. Minimising over this subspace can only
exceed the global minimum, so `λ₂(T(G)) ≤ μ(G)`. ∎

**The regular case falls out.** If `G` is `δ`-regular then `d = δ·1`, so
`φ ⟂ 1 ⟺ φ ⟂ d`; taking `φ` = Fiedler of `G` gives
`φᵀL_tφ ≤ (Δ−1)φᵀL_Gφ = (δ−1)δ‖φ‖²` and `φᵀQφ = (2δ−λ₂)‖φ‖²`, recovering the
known `λ₂(T)≤λ₂(G)`. Irregularity breaks `φ⟂1 ⟹ φ⟂d`, which is precisely the
open difficulty.

**Numerics.** Over 52 tightest **irregular** graphs (`n≤10`, including
`K_n − e`, complete multipartite, threshold/split, and the 30 tightest random
graphs found): `μ(G) ≤ λ₂(G)` on **52/52**, and `μ(G) ≥ λ₂(T)` on **52/52**
(the lift is a valid bound). Strikingly `μ ≈ λ₂(T)` to 2–3 digits — the lift is
**near-optimal**, so the route loses almost nothing:

| graph | n | m | Q=λ₂(G)/λ₂(T) | λ₂(T) | μ(G) | λ₂(G) |
|---|---|---|---|---|---|---|
| `K10−e` | 10 | 44 | 1.143 | 7.000 | 7.000 | 8.000 |
| `K9−e` | 9 | 35 | 1.167 | 6.000 | 6.000 | 7.000 |
| rand-tight Q1.190 | 10 | 43 | 1.190 | 6.725 | 6.750 | 8.000 |
| `K8−e` | 8 | 27 | 1.200 | 5.000 | 5.000 | 6.000 |
| `K10−2e` | 10 | 43 | 1.214 | 5.767 | 5.791 | 7.000 |
| rand-tight Q1.232 | 9 | 34 | 1.232 | 5.683 | 5.714 | 7.000 |

So Conjecture B reduces, on all evidence, to the operator inequality
**`L_t ⪯ λ₂(G)·Q` restricted to `d^⟂`**.

---

## 3. The user's stated "core" is the wrong direction (rigorous)

The brief proposed proving `(Bh)ᵀ L_G (Bh) ≥ λ₂(T)·|Bh|²` for `h ⟂ 1_E`
(unsigned `B`). This is **vacuous**: for `h ⟂ 1_E`,
`1_Vᵀ(Bh) = Σ_v Σ_{e∋v} h_e = 2·1_Eᵀh = 0`, so `Bh ⟂ 1_V` and therefore
`(Bh)ᵀL_G(Bh) ≥ λ₂(G)|Bh|² ≥ λ₂(T)|Bh|²` **automatically** (using B itself).
Proving it yields nothing toward B. The correct sufficient condition is the
*lift bound* of §2, not this inequality. (Verified: the implication
`h⟂1_E ⟹ Bh⟂1_V` holds to machine precision.)

---

## 4. Strategy results

### Strategy 1 — degree-weighted test vector `ψ = φ/√deg`

Writing `φ = D^{1/2}ψ` is a **congruence** `(L_t, Q) ↦ (D^{1/2}L_t D^{1/2},
D^{1/2}Q D^{1/2})`. Generalised eigenvalues are congruence-invariant
(`det(M−λS)` scales by `det(D^{1/2})²`), so **`μ(G)` is unchanged**. S1 is a
change of coordinates, not a reduction: it cannot by itself make
`μ ≤ λ₂(G)` easier. It *is* the natural coordinate for a normalised-Laplacian
attack (it sends `Q` to `I + D^{-1/2}AD^{-1/2}`), but the gap survives it.
**Verdict: reframes, does not close.**

### Strategy 2 — Cauchy–Schwarz on the degree imbalance (the concrete witness)

Take the **true** Fiedler vector `φ*` (`φ*⟂1`, `L_Gφ*=λ₂φ*`, `‖φ*‖=1`) and its
lift `h=Bᵀφ*`; it is *not* `⟂1_E` because `S := 1_Eᵀh = dᵀφ* ≠ 0` for irregular
`G`. Project in **edge space**: `h' = h − (S/m)·1_E ⟂ 1_E`. Since `L_{T(G)}1_E=0`,
the numerator is **unchanged**, and `‖h'‖² = ‖h‖² − S²/m`:
```
  R_{T(G)}(h') = (φ*ᵀ L_t φ*) / (φ*ᵀ Q φ* − S²/m).
```
- **Holds: `R_{T(G)}(h') ≤ λ₂(G)` on 52/52** (worst margin `+0.74`), and
  `R_{T(G)}(h') ≈ λ₂(T)`. The vertex-space projection
  `φ̃ = φ* − (S/‖d‖²)d ⟂ d` likewise gives `≤ λ₂(G)` on 52/52. So the projected
  Fiedler lift is an **explicit witness** realising the reduction.
- **The imbalance is controlled:** `|S| = |dᵀφ*| = |(d−d̄1)ᵀφ*| ≤ √(n·σ²_d)`
  by Cauchy–Schwarz (`σ²_d` = degree variance). Valid on **52/52**.
- **But the crude closed form fails (16/52).** Replacing the numerator by its
  worst case `φ*ᵀL_tφ* ≤ (Δ−1)φ*ᵀL_Gφ* = (Δ−1)λ₂` and lower-bounding the
  denominator by `2δ − λ₂ − S²/m` gives `(Δ−1) ≤ 2δ − λ₂ − S²/m`, which holds
  only **16/52**. **Discarding the triangle-weighted structure is fatal** — the
  proof must keep `φ*ᵀL_tφ*` (it is much smaller than `(Δ−1)λ₂` because the
  Fiedler variation concentrates on *low-triangle* edges).

  **Exact remaining inequality (S2 form):**
  `φ*ᵀ L_t φ* ≤ λ₂·(2·φ*ᵀ D φ* − λ₂ − S²/m)`.

### Strategy 3 — edge-space operator comparison

- **`L_t ⪯ (Δ−1)·L_G` globally** (rigorous: `t_{ab} ≤ Δ−1` edge-wise, both are
  `Σ` of `weight·(φ_a−φ_b)²`). Confirmed: `max gen-eig(L_t, L_G) = 7.8 ≤ Δ−1=8`.
- **The unconstrained operator inequality `L_t ⪯ λ₂(G)·Q` is FALSE — 0/52.**
  The `d^⟂` (equivalently `1_E^⟂`) restriction in Theorem 2 is **essential**:
  `λ₂(T)` lives on `1_E^⟂`, and without that constraint the bound fails on every
  graph. A naive operator-norm / interlacing argument therefore **cannot** prove
  B; the constraint does real work.

---

## 5. The precise open problem

> **Conjecture B′ (reduced).** For connected non-bipartite `G`,
> `φᵀ L_t φ ≤ λ₂(G)·φᵀ(D+A)φ` for all `φ ⟂ d`,
> i.e. `L_t ⪯ λ₂(G)·(D+A)` on `d^⟂`, where `L_t` is the triangle-weighted
> Laplacian and `D+A` the signless Laplacian.

By Theorem 2, **B′ ⟹ B**, and B′ holds on every graph tested (52/52 tight
irregular here; 0 violations across the 45 196-graph census in
[`conjecture_B_exploration.md`](conjecture_B_exploration.md)). The hard core,
now isolated, is to bound the **triangle-weighted** Dirichlet energy by `λ₂`
times the **signless-Laplacian** norm on `d^⟂` — a bound that genuinely couples
the triangle counts `t_{ab}` to the Fiedler geometry and is *not* reducible to
degree-only quantities (Strategy 2's crude form fails, Strategy 3's global form
fails). This is the natural next target.

---

## 6. Lean verification

Verified on Modal (`modal run modal_lean.py::check_file`, `lake env lean`,
against `Topostability.Defs`):

- `edgeLift_eval`  : `edgeLift f {u,v} = f u + f v`.
- `edgeLift_diff_triangle` : across a `T(G)`-edge the lift changes by `f v − f w`
  — the atomic identity underlying Lemma 1's numerator.

Both compile cleanly (only an expected unused-section-variable linter warning).
The full reduction (Theorem 2) is a Rayleigh/min–max argument over `ℝ^E`, not a
finite algebraic statement, so it is outside a single-file `lean_check`; it is
stated here as standard linear algebra. The numerator identity — the one step
that is specific to the triangle-graph combinatorics — is the part worth
machine-checking, and it is verified.

---

## Caveats

- The **reduction (Theorem 2) is rigorous**; the crux **B′ (`μ ≤ λ₂(G)`) is a
  conjecture** with strong evidence, not a theorem.
- Tests: 52 tightest irregular graphs, `n ≤ 10` (`K_n−ke`, complete multipartite,
  split/threshold, 30 tightest random); `λ₂` numerical (`eigvalsh`, tol 1e-9).
- Non-bipartite assumed: bipartite `G` has no triangles, so `T(G)` is edgeless /
  disconnected and the statement is vacuous.
- The lift route is **sufficient but a priori not necessary**; that `μ ≈ λ₂(T)`
  empirically (lift near-optimal) is encouraging but unproven in general.
