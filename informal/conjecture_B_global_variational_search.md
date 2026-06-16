# Conjecture B — global/variational search from the exact inequality

Target (no relaxations): for `f` the unit Fiedler vector of `G`,
`Σ_{ab∈E} t_{ab}(f_a−f_b)² ≤ λ₂(G)·fᵀ(D+A)f`, i.e. `Δ := fᵀ(λ₂Q − L_t)f ≥ 0`
(`L_t` triangle-weighted Laplacian, weight `t_{ab}=(A²)_{ab}`; `Q=D+A`). Code:
[`conjecture_B_global_variational.py`](../conjecture_B_global_variational.py).

**Headline.** **TASK 0 is decisive and negative:** the operator inequality
`λ₂Q − L_t ⪰ 0` on `1⊥` holds on only **6 / 9020** graphs (min eigenvalue **−37**).
So **B is genuinely an eigenvector statement** — the operator `λ₂Q − L_t` is
*indefinite*, and B holds only because the Fiedler `f` lands in its positive part.
**Any proof must use `L_G f = λ₂ f`.** The two structural routes the brief proposed
(edge-monotonicity induction, neighborhood Poincaré) both **fail**, as do the Schur-
product and complement-additivity ideas. No off-the-shelf literature/Mathlib result
applies.

---

## TASK 0 — operator domination: FAILS (B needs the eigenvector)

Smallest eigenvalue of `(λ₂Q − L_t)|_{1⊥}` over the 9020 distinct corpus graphs:

| | value |
|---|---|
| graphs with `λ₂Q − L_t ⪰ 0` on `1⊥` | **6 / 9020 (0.1%)** |
| min smallest-eigenvalue across corpus | **−37.0** (at n=9, m=30) |

So `xᵀL_t x ≤ λ₂ xᵀQx` is **false for most `x⊥1`** — the operator is strongly
indefinite. **B is not an operator-domination fact**; it holds because the *specific*
Fiedler vector sits in the (rare) positive cone of `λ₂Q − L_t`. **Conclusion: a proof
must invoke `L_G f = λ₂ f`** — no eigenvector-free argument can work.

## TASK 3 — spectra of `(λ₂Q − L_t)|_{1⊥}` for named graphs

| graph | λ₂ | Δ (Fiedler) | spec min | spec max | #neg / dim |
|---|---|---|---|---|---|
| `K₈` | 8 | 0 | 0 | 0 | **0 / 7** (operator ≡ 0 on 1⊥) |
| `K₈ − e` | 6 | +6 | −13 | +6 | **6 / 7** (indefinite) |
| `K₈ − △` | 5 | +5 | −14.5 | +5 | **5 / 7** (indefinite) |
| Petersen | 2 | +8 | +2 | +8 | **0 / 9** (PSD) |

- **`K_n`:** `λ₂Q − L_t ≡ 0` on `1⊥` *identically* (on `1⊥`, `L_t=(n−2)·nI`,
  `Q=(n−2)I`, so `λ₂Q−L_t = n(n−2)I−(n−2)nI = 0`). Equality is structural.
- **`K_n − e`, `K_n − △`:** the operator is **indefinite** (5–6 negative
  eigenvalues out of 7) — yet `Δ > 0` because the Fiedler lands in the positive
  eigenspace. Vivid proof that B is an eigenvector phenomenon.
- **Petersen** (vertex-transitive, `λ₂=2` small): one of the 6 graphs where the
  operator *is* PSD on `1⊥`. The PSD cases are rare and highly symmetric.

## TASK 2 — lemma candidates (all fail to give a proof)

- **LEMMA 1 (Schur/Hadamard):** `L_t` comes from the Hadamard product `A∘A²`. The
  Schur product theorem needs *both* factors PSD; `A` (adjacency) is **not** PSD, so
  it does not apply, and TASK 0 shows no PSD comparison `L_t ⪯ λ₂Q` holds. **Dead.**
- **LEMMA 2 (neighborhood Poincaré):** `𝓔_{G[N(c)]}(f) ≤ λ₂·Σ_{N(c)}f²` was already
  refuted (`conjecture_B_local_decomposition.md`: 6% of vertices, worst ratio 3.26).
  **Dead.**
- **LEMMA 3 (eigenvector expansion):** `fᵀL_t f = 2Σ_v τ(v)f_v² − fᵀ(A∘A²)f`, and
  `fᵀ(A∘A²)f = Σ_c fᵀA[N(c)]f` (adjacency form of `f` on each neighbourhood). Using
  `Af=(D−λ₂)f` does **not** collapse the local `A[N(c)]` terms into a manifestly
  positive expression — no reducing identity emerges. (Numerically `fᵀ(A∘A²)f` is
  unrelated to `fᵀA³f`, `fᵀAf`.) **No simplification.**
- **LEMMA 4 (edge-monotonicity):** `w_{uv} = Δ(G) − Δ(G+uv)`. Over 6231 edge
  additions, **`w_{uv} < 0` on 68.3%** (min `−6.23`). So `Δ` **is not monotone**
  under edge addition — adding an edge usually *increases* `Δ`. **Induction from
  `K_n` via single-edge steps is impossible.** Dead.
- **LEMMA 5 (complement-additive):** `Δ` does **not** decompose additively over
  missing edges: `Δ(K_n−e)=n−2` but `Δ(K_n−△)=n−3` (3 missing edges, not `3×`); the
  missing edges interact through `λ₂` and `f`. No nonnegative per-missing-edge
  decomposition. **Dead.**

## TASK 1 — literature & Mathlib

**Literature** (no applicable result):
- **Schur product theorem** ([Schur product theorem](https://en.wikipedia.org/wiki/Schur_product_theorem)):
  Hadamard of PSD is PSD — inapplicable (`A` not PSD).
- **Haemers interlacing / quotient matrices / equitable partitions**
  ([Haemers, *Interlacing eigenvalues and graphs*](https://research.tilburguniversity.edu/files/996579/interlac.pdf);
  [arXiv:1307.4670](https://arxiv.org/pdf/1307.4670)): give exact eigenvalues for
  *symmetric* graphs (explains `K_n`, Petersen) but **no** up-vs-down or
  triangle-weighted-vs-signless comparison.
- **Triangular graph `J(n,2)`** ([Johnson J(n,2) spectrum, arXiv:2312.03114](https://arxiv.org/pdf/2312.03114)):
  `= L(K_n)`, strongly regular, adjacency eigenvalues `2(n−2), n−4, −2`; Laplacian
  `λ₂ = n = λ₂(K_n)` — confirms the `K_n` equality, nothing more.
- **Weighted/signed Laplacian Loewner conditions, effective resistance / Schur
  complement** ([arXiv:1803.05640](https://arxiv.org/pdf/1803.05640),
  [arXiv:2010.04521](https://arxiv.org/pdf/2010.04521)): no triangle-weighted vs
  signless comparison. **No neighborhood-Dirichlet local-to-global inequality found.**

**Mathlib4** (confirmed compiling on Modal):
- present: `Matrix.PosSemidef`, `Matrix.PosSemidef.add`,
  `Matrix.posSemidef_conjTranspose_mul_self` (`AᴴA ⪰ 0`); plus the graph-Laplacian
  API (`lapMatrix`, `posSemidef_lapMatrix`, `lapMatrix_toLinearMap₂'`,
  `card_connectedComponent_eq_finrank_ker`) and global Rayleigh sup/inf eigenvalue
  results.
- **absent:** Loewner-order eigenvalue monotonicity (`A⪯B ⇒ λᵢ(A)≤λᵢ(B)`), Cauchy
  interlacing / Courant–Fischer min–max for the `k`-th eigenvalue, a Hadamard-PSD
  (`Schur`) lemma, `λ₂`/algebraic connectivity as a constrained min, and any
  triangle-graph / Hodge spectral API. (Even `Matrix.PosSemidef.eigenvalues_nonneg`
  is not present under that name.)

So neither the literature nor Mathlib supplies the cross-comparison; both confirm
only the symmetric `K_n`/`J(n,2)` facts.

---

## Synthesis — the proof must couple the eigenvector to an indefinite operator

The exact, fully-reduced situation:

> **B ⟺ `fᵀ(λ₂(G)·Q − L_t)f ≥ 0`** where `f` is the `λ₂`-eigenvector of `L_G`, and
> the operator `M := λ₂(G)·Q − L_t` is **indefinite** (typically many negative
> eigenvalues; min over corpus `−37`). B holds because `f` lies in `M`'s positive
> cone — and `M` itself depends on `λ₂(G)`.

Every *structure-free* route is now closed (this round adds operator-domination,
edge-monotonicity, Schur-product, and complement-additivity to the earlier list:
min-degree relaxation, local certificates, signed Hodge, fixed test vector,
spectral radius, additivity residual). What remains is intrinsically variational:
the Fiedler vector — the *minimizer* of the `L_G` Rayleigh quotient on `1⊥` — must
also satisfy `fᵀMf ≥ 0` for the indefinite, `λ₂`-dependent `M = λ₂Q − L_t`. A proof
seems to require simultaneously using (i) `L_G f = λ₂ f` (the eigen-equation), and
(ii) the *minimality* of `λ₂` (that no `1⊥` direction beats it), to control the sign
of `f` against `M`'s negative eigenspaces. This is the genuine remaining problem; no
operator/inductive/local shortcut survives.

### Caveats
- `λ₂`, `f` numerical; TASK 0 over 9020 distinct corpus graphs (`n≤9`); LEMMA 4 over
  441 graphs / 6231 edge additions incl. deg2+dense and Petersen. Named-graph
  spectra exact-by-formula and verified. Mathlib declarations confirmed by `#check`
  on Modal; the 6 operator-PSD graphs include `K_n` (`M≡0` on 1⊥) and Petersen.
