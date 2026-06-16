# Conjecture B — closed form for the additive lift quotient R_T(h)

For `h_{uv} = φ_u + φ_v` (the unsigned lift of `φ`), derive and verify a closed form
for `R_T(h) = hᵀL_T h / hᵀh` (`L_T` = triangle-graph Laplacian), compare to `λ₂(G)`,
and isolate the term that drops `K_n−e` below equality. Code:
[`conjecture_B_additive_quotient.py`](../conjecture_B_additive_quotient.py).
All identities verified to `≤2e-13` on 191 random graphs and the four families.

---

## 1. Numerator `hᵀL_T h` — three equivalent closed forms

For a `T(G)`-edge `(e,e')` sharing vertex `u` with opposite vertices `v,w`
(triangle `u,v,w`), `h_e − h_{e'} = (φ_u+φ_v) − (φ_u+φ_w) = φ_v − φ_w`
(Lean-verified, `edgeLift_diff_triangle`). Each triangle `{a,b,c}` contributes its
three squared side-differences, so the coefficient of `(φ_a−φ_b)²` is the number of
triangles on edge `ab`, i.e. `t_{ab} = |N(a)∩N(b)| = (A²)_{ab}`. Hence:

> **`hᵀL_T h = Σ_{(a,b)∈E} t_{ab}(φ_a−φ_b)²`**  (triangle-weighted Dirichlet form)
> **` = Σ_{c∈V} 𝓔_{G[N(c)]}(φ)`**  (apex form: total Dirichlet energy of `φ` over
> the neighbourhood-induced subgraphs)
> **` = φᵀ L_t φ`**  (`L_t = D_t − A∘A²`, the triangle-weighted Laplacian).

The apex form sums, over each vertex `c`, the Dirichlet energy
`𝓔_{G[N(c)]}(φ) = Σ_{(a,b)∈E,\, a,b∈N(c)}(φ_a−φ_b)²` of `φ` on the subgraph induced
by `c`'s neighbours (each triangle counted once, at its apex). All three forms
verified equal to `≤2e-13`.

## 2. Denominator `hᵀh` — signless Laplacian

`hᵀh = Σ_{(u,v)∈E}(φ_u+φ_v)² = φᵀ B Bᵀ φ = φᵀ(D+A)φ`, since `BBᵀ = D+A` (signless
Laplacian `Q`). Equivalently, using `D+A = 2D − L_G`:

> **`hᵀh = φᵀ(D+A)φ = 2 Σ_v deg(v)φ_v² − φᵀ L_G φ`.**

Verified to `≤5e-15`.

## 3. The quotient and the comparison to `λ₂(G)`

> **`R_T(h) = [Σ_{(a,b)∈E} t_{ab}(φ_a−φ_b)²] / [2 Σ_v deg(v)φ_v² − φᵀ L_G φ]`.**

Specialize `φ = f` (unit Fiedler, `L_G f = λ₂ f`, `f⊥1`): `φᵀL_Gφ = λ₂`, and using
`Af = Df − λ₂ f` the denominator is `2fᵀDf − λ₂ = fᵀ(D+A)f`. So

> **`R_T(f) = (Σ t_{ab}(f_a−f_b)²) / (2fᵀDf − λ₂)`,  and B (lift form) is
> `R_T(f) ≤ λ₂(G)`, i.e.**
> **`Σ_{(a,b)∈E} t_{ab}(f_a−f_b)² ≤ λ₂(G)·fᵀ(D+A)f`.**

Define the **missing term**
`Δ := λ₂·fᵀ(D+A)f − Σ t_{ab}(f_a−f_b)² = fᵀ(D+A)f·(λ₂(G) − R_T(f)) ≥ 0`.
So `Δ ≥ 0 ⟺ R_T(f) ≤ λ₂ ⟺ B`, and `Δ = 0 ⟺ equality`.

---

## 4. Verification + closed forms (K_n, K_n−e, K_n−△)

| family | n | λ₂(G) | R_T(f) | λ₂(T) | `N=Σt(Δφ)²` | Den | **Δ (missing)** |
|---|---|---|---|---|---|---|---|
| `K_n` | 8 | 8 | **8 = λ₂** | 8 | 48 = (n−2)n | 6 | **0** |
| `K_n − e` | 8 | 6 | **5 = λ₂−1** | 5 | 30 = (n−2)(n−3) | 6 | **6 = n−2** |
| `K_n − △` | 8 | 5 | **4 = λ₂−1** | 4 | 20 = (n−3)(n−4) | 5 | **5 = n−3** |

Closed forms (verified `n=6,8,10,12`):

- **`K_n`:** `t_{ab} = n−2` for every edge; `N = (n−2)·n`, `Den = n−2`,
  `R_T = n = λ₂(G)` — **equality, `Δ=0`.**
- **`K_n − e`:** `λ₂(G)=n−2`, `R_T = n−3 = λ₂(T) = λ₂(G) − 1`; `N=(n−2)(n−3)`,
  `Den=n−2`, **`Δ = n−2`.**
- **`K_n − △`:** `λ₂(G)=n−3`, `R_T = n−4 = λ₂(T) = λ₂(G) − 1`; **`Δ = n−3`.**

For both single-edge and single-triangle deletions, the lift quotient sits
**exactly 1 below `λ₂(G)`**, with `Δ = Den = ` (the signless-Laplacian norm).

---

## 5. The missing term: a triangle-count deficit on the Fiedler-active edges

Why does `K_n − e` drop from `n−2` to `n−3`? Use the same Fiedler
`f = (e₀ − e₁)/√2` (concentrated on the removed edge's endpoints) for both `K_n`
and `K_n − e`. The denominator is unchanged (`Den = n−2`); the numerator drops by
`3(n−2)`, in two pieces:

| piece | value (general) | n=8 | mechanism |
|---|---|---|---|
| **removed edge `{0,1}`** | `(n−2)·(f₀−f₁)² = 2(n−2)` | 12 | the edge `{0,1}` itself (with `t=n−2` in `K_n`) is gone |
| **triangle deficit** | `2(n−2)·½·1 = (n−2)` | 6 | each of the `2(n−2)` edges `{0,v},{1,v}` loses **exactly one** triangle — `{0,1,v}` — because edge `{0,1}` is gone, so `t` drops `n−2 → n−3` |
| **total drop in N** | `3(n−2)` | 18 | `N: (n−2)n → (n−2)(n−3)` |

Since `f` is supported precisely on these edges, `R_T` drops by `3(n−2)/Den = 3`
(from `n` to `n−3`), while `λ₂(G)` drops only by `2` (from `n` to `n−2`). **Net:
`R_T = λ₂(G) − 1`.**

**So the "missing term" is the triangle-count deficit:** removing edge `{0,1}` kills
the triangle `{0,1,v}` on every edge `{0,v}` and `{1,v}`, lowering their
common-neighbour count `t` from `n−2` to `n−3`. The Fiedler vector lives exactly on
those edges, so the triangle-weighted numerator falls below the equality value
`λ₂·Den` by `Δ = n−2`. In the apex form: each neighbourhood `N(0)`, `N(1)` lost a
vertex (they no longer contain each other), shrinking the local Dirichlet energy.

---

## Synthesis

- **Exact closed form (verified):**
  `R_T(h) = Σ t_{ab}(φ_a−φ_b)² / (2Σdeg·φ² − φᵀL_Gφ)`, three equivalent numerator
  forms (triangle-weighted / apex-neighbourhood / `L_t`), denominator = signless
  Laplacian `φᵀ(D+A)φ`.
- **B (lift form) ⟺ `Δ = λ₂·fᵀ(D+A)f − Σ t_{ab}(f_a−f_b)² ≥ 0`,** with `Δ = 0 ⟺
  K_n` (every edge has the maximal `t=n−2` and the structure is homogeneous).
- **The discriminator is the triangle count `t_{ab}` on Fiedler-active edges**, not
  additivity (cf. `conjecture_B_additivity_proof.md`): equality needs every active
  edge to carry the *full* `t=n−2`; any missing edge creates a unit triangle deficit
  on its incident edges, and the Fiedler concentrating there forces `R_T < λ₂`. For
  `K_n−e`/`K_n−△` the deficit is exactly enough to put `R_T = λ₂(G) − 1`.
- **The open core, restated cleanly:** prove `Σ_{(a,b)∈E} t_{ab}(f_a−f_b)² ≤
  λ₂(G)·fᵀ(D+A)f` for the Fiedler `f` of every connected `G` — equivalently `Δ ≥ 0`.
  This is the genuine remaining inequality (no proxy/relaxation); the apex form
  `Σ_c 𝓔_{G[N(c)]}(f)` is a promising handle (energy summed over neighbourhoods).

### Caveats
- Numerator per-edge identity Lean-verified (`edgeLift_diff_triangle`); the global
  forms and `BBᵀ=D+A` are elementary, verified numerically to `≤2e-13`. Closed forms
  for `K_n`, `K_n−e`, `K_n−△` derived and confirmed `n=6..12` (and `n=8,12,20` for the
  decomposition). For degenerate `λ₂(T)` (e.g. `K_n`) any eigenvector in the space
  gives the same `R_T`.
