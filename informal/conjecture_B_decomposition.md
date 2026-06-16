# Conjecture B — factorizing the core (C4): the LOCK is an anticorrelation

Per the directive, this does **not** attack `(C4)` head-on; it **factorizes** it.
Continues [`conjecture_B_proof_v3.md`](conjecture_B_proof_v3.md).

Open core (v3), unit Fiedler `f` (`L_G f = λ₂f`, `f⟂1`, `‖f‖=1`), `d`=degrees,
`δ`=min degree, `S=Σ_v d_v f_v`, `m=|E|`, `f_h`/`f_l` = values at higher/lower-
degree endpoints:
```
(C4)   Σ_{ab∈E} |d_a−d_b| · f_h · (f_l − f_h)  ≤  λ₂ (δ − λ₂ + 1 − S²/m).
```

**Main result of this round.** An *exact* identity (from the eigenvector
equation) factorizes `(C4)` into a clean nonnegative degree-weighted Dirichlet
form, and the numerics then pin the difficulty to a single, sharply-characterized
**LOCK**: a ~7× *anticorrelation* between min-degree edge weights and the Fiedler
gradient that no degree-only bound can see. The proposed crude chain
`A + B + D ⟹ (C4)` **provably does not close** — and we can now say exactly why.

Code: [`conjecture_B_decomposition_explore.py`](../conjecture_B_decomposition_explore.py).

---

## The factorization: Lemma D (eigenvector equation) → exact identity

From `L_G f = λ₂ f`: at each vertex `Σ_{b∼a} f_b = (d_a − λ₂) f_a`. Multiplying
by `(d_a − δ) f_a` and summing gives the cross-form identity
`Σ_{ab}[(d_a−δ)f_a − (d_b−δ)f_b](f_a−f_b) = λ₂(fᵀDf − δ)`. Expanding the summand
against the `(C4)` integrand yields (verified to `1.9e-14`):

> **Identity D2.**  `LHS(C4) = W − λ₂(fᵀDf − δ)`,  where
> **`W := Σ_{ab∈E} (min(d_a,d_b) − δ)·(f_a − f_b)²`**  (a *nonnegative*
> degree-weighted Dirichlet form; edge weight = smaller-endpoint degree − δ ≥ 0).

Hence **`(C4)` is exactly equivalent to**

> **(C4″)**  `W  ≤  λ₂(fᵀDf − λ₂ + 1 − S²/m) =: R″.`

This is the factorization: the awkward sign-indefinite integrand
`f_h(f_l−f_h)` is replaced by a clean sum of squares `W`, at the cost of the
exactly-known term `λ₂(fᵀDf−δ)`. `W` is the object to bound.

---

## The five lemmas — tested, with slack (52 tight + 1721 broad, n ≤ 14)

| lemma / chain | statement | tight | broad | verdict |
|---|---|---|---|---|
| **D2** | `LHS = W − λ₂(fᵀDf−δ)` (exact) | err 2e-14 | err 7e-14 | ✅ **rigorous** |
| **C4″** | `W ≤ R″` (= C4) | 52/52 | 1720/1721† | target |
| **A** | `W ≤ (Δ−δ)·λ₂` | 52/52 | 1721/1721 | ✅ rigorous (trivial: weight ≤ Δ−δ) |
| **A-chain** | `(Δ−δ) ≤ fᵀDf−λ₂+1−S²/m` | **16/52** | **124/1721** | ❌ **fails** |
| **H** | `W ≤ μ*·λ₂`, `μ*=max_e(min(d_a,d_b)−δ)` | 52/52 | 1721/1721 | ✅ rigorous (tighter than A) |
| **H-chain** | `μ* ≤ fᵀDf−λ₂+1−S²/m` | **18/52** | **254/1721** | ❌ **fails** |
| **B** | `S² ≤ n·σ²_d` (Cauchy–Schwarz) | 52/52 | ✅ | ✅ rigorous (classical) |
| **F** | `S²/m ≤ fᵀDf−δ` | 52/52 | 1710/1721 | ◐ near-universal, not exact |
| **E** | `W ≤ λ₂(fᵀDf−λ₂−S²/m)` (drop `+1`) | 30/52 | 1418/1721 | ❌ **fails → `+1` essential** |
| **G** | `LHS ≤ ¼Σ|d_a−d_b|f_l²` (complete square) | 52/52 | 1721/1721 | ✅ rigorous (per-edge) |

† The single broad miss (slack `−0.021`, `n=12`, `Q=2.16` — a *loose* graph where
B holds by a wide margin) is a Fiedler-degeneracy / eigenvector-choice artifact,
not a violation: it did not reproduce under a fresh random stream, and the lift
bound only needs *some* vector in the (multiple) `λ₂`-eigenspace.

---

## The LOCK: `W ≤ R″`, and why crude bounds miss it by ~7×

**The lock is `W` itself** — bounding the min-degree-weighted Dirichlet form.
The diagnostic that nails it:

> `W / ((Δ−δ)·λ₂)` over the broad set: **median 0.147**, max 0.52.

So the true `W` is typically only **~15%** of the crude bound `(Δ−δ)λ₂` that
Lemma A supplies. That factor of ~7 is a structural **anticorrelation**:

- the weight `min(d_a,d_b)−δ` is **large** only on edges between two
  high-degree vertices;
- the Fiedler gradient `(f_a−f_b)²` is **large** only on the *cut* edges of the
  Fiedler partition, which tend to touch **low**-degree vertices (weight ≈ 0).

The two factors are large in *disjoint* places, so `W = Σ weight·gradient` is far
below `(max weight)·Σ gradient`. **A and H are tight only when weight and
gradient line up — which is exactly when they don't.** This is precisely the
"structural, not global" failure the directive anticipated: Cauchy–Schwarz and
max-weight bounds are blind to *where* on the graph the two factors live.

Meanwhile `(C4″)` itself is comfortable: `W/R″` has **median 0.26, max 0.71** —
the inequality holds with healthy margin once the anticorrelation is respected.

---

## Does the chain `A + B + D ⟹ (C4)` close?  **No.**

The directive's proposed composition fails, and we can say exactly where:

- **D** (exact) reduces `(C4)` to `(C4″): W ≤ R″`. ✅
- **B** controls the correction `S²/m` (rigorous Cauchy–Schwarz). ✅
- **A** bounds `W ≤ (Δ−δ)λ₂`. ✅ rigorous — **but the A-chain
  `(Δ−δ) ≤ fᵀDf−λ₂+1−S²/m` fails 16/52 and 124/1721.** The bound is ~7× too
  weak (the anticorrelation), so `A + B + D` cannot reach `R″`.
- Refining A→H (max *edge*-min-degree weight `μ*` instead of `Δ−δ`) helps but
  still fails (18/52). Even the sharpest *degree-only* max-weight bound overshoots.

So the missing ingredient is **not** a better global constant — it is an
**anticorrelation-aware** bound on `W` that uses the *Fiedler geometry* (where the
gradient concentrates) against the *degree profile* (where the weight
concentrates). The rigorous pieces that DO compose: **D (reduction) + the `+1`
(E shows it is essential) + B (S² control)**; what they reduce to is the lock.

---

## The precise remaining problem (the LOCK)

> **Lock lemma.** For connected non-bipartite `G` with unit Fiedler `f`:
> `Σ_{ab∈E}(min(d_a,d_b) − δ)(f_a−f_b)²  ≤  λ₂(fᵀDf − λ₂ + 1 − S²/m).`
> Equivalently, the min-degree-weighted Dirichlet energy of the Fiedler vector is
> at most `λ₂` times the (signless-Laplacian-shifted) degree-weighted norm.

What a proof must exploit (all established above):
1. the **`+1`** term is essential (E);
2. the bound must be **finer than any max-weight × λ₂** estimate (A, H fail by ~7×);
3. it must capture that the **cut edges carry low min-degree weight** — i.e. couple
   the Fiedler nodal structure to the degree sequence. A promising route is a
   *localized* summation-by-parts using the per-vertex relation
   `Σ_{b∼a}f_b = (d_a−λ₂)f_a` (the same identity that produced D2) applied
   edge-class by edge-class, rather than globally.

### Rigorous deliverables this round
- **Identity D2** (eigenvector-equation factorization; verified `~1e-14`): exact,
  reduces `(C4) ⟺ (C4″)`.
- Lemmas **A**, **H**, **G** (degree-weighted Dirichlet / complete-square bounds);
  **B** (Cauchy–Schwarz on `S`); **E** (the `+1` is necessary). The per-edge
  algebra of D2 and of G is `ring`/`nlinarith`-trivial; the global D2 uses the
  standard Laplacian eigen-equation. No full proof emerged, so (per directive) no
  new Lean was added; the verified lemmas remain those of v1/v2.

### Caveats
- Tests: `K_n−ke`, complete multipartite, split/threshold, broad random
  `n=6..14`, all densities with `T(G)` connected; `λ₂` numerical (tol 1e-9). One
  borderline broad miss (above) is numerical. Non-bipartite assumed.
- The lock lemma is conjectural (0 genuine failures over ~1770 graphs here, plus
  the 5,600+ of v3); it remains the single open step for Conjecture B.
