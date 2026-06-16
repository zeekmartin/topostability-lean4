# Conjecture B — direct test of the signed Hodge up-vs-down conjecture: REFUTED

Tests `λ_min⁺(L₁_up) ≤ λ_min⁺(L₁_down) = λ₂(G)` directly, where (consistent
orientation) `L₁_up = B₂B₂ᵀ`, `L₁_down = B₁ᵀB₁`, `λ_min⁺` = smallest eigenvalue
`> tol`. Ratio `r = λ_min⁺(L₁_up)/λ₂(G)`. Code:
[`conjecture_B_hodge_test.py`](../conjecture_B_hodge_test.py).

**Result: the signed Hodge up-vs-down conjecture is FALSE.** Over 74,770 objects
there are **15,796 violations (21%)**, `r` up to **21.2**. And — decisively — even
on the **45,196 `T(G)`-connected graphs where combinatorial Conjecture B holds with
0 violations**, the signed version **violates on 461 (1.0%)** (worst `r = 1.86`).

> **So Conjecture B is intrinsically about the UNSIGNED/combinatorial triangle
> graph `T(G)`; the signed Hodge analogue is false. The signs HURT.** This also
> **corrects** the small-sample claim in `conjecture_B_literature_deep.md` ("signed
> Hodge holds and is tighter") — that was based on ~8 graphs; on the full corpus it
> fails badly.

---

## 1. Violations

| domain | objects | signed-Hodge violations `r>1` | combinatorial B violations |
|---|---|---|---|
| **all families** | 74,770 | **15,796 (21.1%)** | 0 |
| **`T(G)`-connected (B applies)** | 45,196 | **461 (1.0%)** | **0** |

The signed version fails *even where B holds*. Max `r = 21.16` overall; `r = 1.857`
on the `T(G)`-connected B-domain (`n=9, m=16, λ₂(G)=0.713, λ_min⁺(up)=1.325`, while
`λ₂(T(G))=0.178 ≪ λ₂(G)` — combinatorial B fine, signed Hodge violated).

## 2. Distribution of `r = λ_min⁺(L₁_up)/λ₂(G)`

| min | median | max | 90% | 99% | 99.9% |
|---|---|---|---|---|---|
| 0.0032 | 0.667 | 21.16 | 2.05 | 6.80 | 13.85 |

Over **10% of all objects have `r > 2`** — the signed up-gap routinely exceeds the
graph gap by large factors.

Per family (`r` min / median / max ; violations):

| family | min | median | max | viol |
|---|---|---|---|---|
| hierarchy (clique complex) | 0.051 | 0.667 | **21.16** | 15,551 |
| deg2+dense | 0.129 | 0.941 | 3.35 | 84 |
| large WS | 0.003 | 0.102 | 1.15 | 2 |
| near-complete | 1.000 | 1.000 | **16.0** | 16 |
| random ER/BA | 0.021 | 0.333 | 8.03 | 94 |
| dim-3 / dim-4 complexes | 0.112 | 0.667 | 5.00 | 49 |

Even the genuine **simplicial complexes** (dim-3/dim-4, using their actual 2-faces)
violate (49) — so it is not an artifact of the clique-complex choice.

## 3. Is the signed version always tighter than unsigned `T(G)`? — No

Over the 45,196 `T(G)`-connected graphs:
- signed tighter (`r_signed ≥ r_unsigned`): **only 45.8%** — *not* always;
- median `r_signed = 0.564`, median `r_unsigned = 0.538` (comparable on average);
- crucially, **`r_signed` exceeds 1 (violation) while `r_unsigned` never does**.

So the signed gap is *not* a valid tightening of B: it is a different quantity that
is sometimes larger than `λ₂(G)`, hence does **not** bound it. The unsigned
combinatorial `λ₂(T(G))` is the one that stays `≤ λ₂(G)`.

## 4. The 10 objects with `r` closest to 1 (from below)

Many sit at **exactly `r = 1`** (`λ_min⁺(L₁_up) = λ₂(G)`):

| r | family | n | m | #tri | λ₂(G) | λ_min⁺(up) |
|---|---|---|---|---|---|---|
| 1.00000 | deg2+dense | 22 | 149 | 470 | 1.960 | 1.960 |
| 1.00000 | hier rand8 | 8 | 20 | 22 | 2.319 | 2.319 |
| 1.00000 | hier rand9 | 9 | 25 | 31 | 1.908 | 1.908 |
| 1.00000 | hier rand8 | 8 | 18 | 17 | 1.916 | 1.916 |
| 1.00000 | hier rand9 | 9 | 28 | 42 | 2.859 | 2.859 |
| … (several more at r=1.000) | | | | | | |

`r = 1` (equality of the up-gap and the graph gap) is a common boundary value;
beyond it, 21% of graphs cross into `r > 1` (violation).

---

## Why the signs matter

`L₁_up = B₂B₂ᵀ` has **signed** (oriented) triangle-edge incidences, so its
quadratic form involves *cancellation* between the three edges of each triangle.
The combinatorial `L_{T(G)}` (all `+1` adjacencies, no orientation) instead sums
unsigned squared differences, yielding a **smaller** smallest-nonzero eigenvalue
`λ₂(T(G))` that stays `≤ λ₂(G)`. The cancellation in the signed operator can
*raise* the smallest nonzero eigenvalue above `λ₂(G)`. So Conjecture B is a
statement about the **unsigned** combinatorial adjacency, and is *not* an instance
of a Hodge-Laplacian spectral inequality.

## Implication

**The Hodge-Laplacian route is a dead end for proving B.** The natural Hodge
analogue (signed 1-up gap ≤ 1-down gap) is false (21% overall, 1% even on the
B-domain). Combinatorial B is true precisely because the unsigned triangle graph
`T(G)` — not the signed `B₂B₂ᵀ` — is the right operator. Any proof must use the
unsigned combinatorial structure; Hodge theory provides language and the classical
`s(L₀)=s(L₁^down)` identity, but **no** valid spectral comparison for the unsigned
`T(G)` gap.

### Caveats
- `λ_min⁺` = smallest eigenvalue `> 1e-7`; orientations consistent (`∂[a,b,c] =
  [b,c]−[a,c]+[a,b]`); eigenvalues orientation-independent. Graphs use the clique
  complex (triangles = 3-cliques); the dim-3/dim-4 complexes use their actual
  2-faces. Numerical (`eigvalsh`). The hierarchy set reproduces the 45,196
  `T(G)`-connected graphs (B's census) exactly.
