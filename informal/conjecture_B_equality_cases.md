# Conjecture B — equality and near-equality cases λ₂(T(G)) ≈ λ₂(G)

Studies where the inequality `λ₂(T(G)) ≤ λ₂(G)` is tight. `ratio := λ₂(T(G))/λ₂(G)
∈ (0,1]`, equality ⇔ `ratio = 1`. Corpus: the 45,196 `T(G)`-connected graphs,
**deduplicated to 9,020 distinct graphs** (the corpus has heavy K₈/K₉ resampling).
Code: [`conjecture_B_equality_cases.py`](../conjecture_B_equality_cases.py).

**Answer.** Equality is achieved by **exactly the complete graphs `K_n`** — nothing
else — with the lift `exactly` additive there. It is **isolated** at each finite
`n` (the nearest competitor `K_n−e` has `ratio = (n−3)/(n−2)`), but that family
**approaches equality as `n → ∞`**. So `ratio = 1 ⟺ G = K_n`, and the "approach
from below" is via *almost-complete* graphs (one missing edge).

---

## 1–2. The equality graphs: exactly K₄…K₉

`|ratio − 1| < 0.001` ⇒ **6 distinct graphs**, all complete (the "1491 with dups"
were these K_n resampled):

| n | m | ratio | complete | regular | vertex-trans | τ(G) | T(G) ≅ J(n,2)? | \|Aut\| |
|---|---|---|---|---|---|---|---|---|
| 4 | 6 | 1.00000 | ✓ | ✓ | ✓ | 2 | ✓ | 24 (=4!) |
| 5 | 10 | 1.00000 | ✓ | ✓ | ✓ | 3 | ✓ | 120 |
| 6 | 15 | 1.00000 | ✓ | ✓ | ✓ | 4 | ✓ | 720 |
| 7 | 21 | 1.00000 | ✓ | ✓ | ✓ | 5 | ✓ | 5040 |
| 8 | 28 | 1.00000 | ✓ | ✓ | ✓ | 6 | ✓ | 40320 |
| 9 | 36 | 1.00000 | ✓ | ✓ | ✓ | 7 | ✓ | 362880 (=9!) |

Every equality graph is **complete, regular, vertex-transitive**, with `τ(G)=n−2`,
`|Aut| = n!`, and **`T(G)` isomorphic to the Johnson / triangular graph `J(n,2)`**
(= line graph of `K_n`).

**0 non-complete equality cases.** Equality is the complete-graph phenomenon.

---

## 3. Near-equality `ratio > 0.95`: only K_n (a finite-n gap)

In the corpus, **`ratio > 0.95` holds for the 6 K_n only** — there are **no
distinct graphs with `0.95 < ratio < 1`**. The maximum ratio among all 9,014
non-complete graphs is **0.85714** (`K₉−e`). Distribution over non-complete graphs:
`max 0.857, 99% 0.648, median 0.356`; only **1** has `ratio>0.85`, **5** have
`>0.80`, **14** have `>0.75`.

This apparent gap `(0.857, 1)` is a **finite-`n` artifact** (corpus is `n≤9`) — see
§6: the family `K_n−e` fills it as `n` grows.

---

## 4. Is equality ONLY K_n? — Yes (exactly)

`ratio = 1 ⟺ G = K_n` on the entire deduplicated corpus (n ≤ 9, exhaustive for
n ≤ 7). No regular non-complete graph (cocktail-party, complete multipartite,
circulant, etc.) reaches equality — e.g. the octahedron `K_{2,2,2}` has `ratio=0.5`.
The equality locus is precisely the complete graphs.

---

## 5. Why K_n? — `T(K_n)=J(n,2)` and the lift is exactly additive

- `T(K_n)` = the triangular graph `J(n,2)` (line graph of `K_n`): in `K_n` any two
  edges sharing a vertex automatically form a triangle, so triangle-adjacency =
  vertex-adjacency of edges. Johnson graphs satisfy `λ₂(J(n,k)) = n`, so
  `λ₂(T(K_n)) = n = λ₂(K_n)`. Equality.
- **Lift exactness:** measured `‖P_U ψ_T‖² = 1.000000` on all 6 equality graphs
  (`U = range(Bᵀ)`, `ψ_T` the `T(G)`-Fiedler). So **the `T(K_n)`-Fiedler vector lies
  *exactly* in the additive subspace** `range(Bᵀ) = {h_e = φ_u + φ_v}`. By the
  edge-transitive (Johnson-scheme) symmetry of `K_n`, the `λ₂`-eigenspace of
  `J(n,2)` is spanned by additive edge-vectors, so Cauchy interlacing is *exactly
  tight* (`μ(G) = λ₂(T) = λ₂(G)`). This is precisely the condition "T-Fiedler ∈
  range(Bᵀ)" identified earlier — it holds *with equality* only for `K_n`.

---

## 6. Approach from below: the family `K_n − e`

The extremal non-complete graphs are **`K_n` minus a few edges** (complement `H`
sparse). The tightest, by ratio:

| graph | n | m | ratio | Q=1/ratio | complement `H` |
|---|---|---|---|---|---|
| `K₉ − e` | 9 | 35 | 0.857 | 1.167 | single edge |
| `K₈ − e` | 8 | 27 | 0.833 | 1.200 | single edge |
| `K₉ − △` | 9 | 33 | 0.833 | 1.200 | triangle (3 edges) |
| `K₉ − 2e` | 9 | 34 | 0.812 | 1.232 | matching `2K₂` |
| `K₈ − △` | 8 | 25 | 0.800 | 1.250 | triangle |

The single missing edge (`K_n − e`) is the tightest. Its spectrum is exact:

> **`K_n − e`:  `λ₂(G) = n−2`,  `λ₂(T(G)) = n−3`,  `ratio = (n−3)/(n−2) → 1`.**

Verified: `0.833 (n=8), 0.857 (n=9), 0.900 (n=12), 0.929 (n=16), 0.944 (n=20),
0.979 (n=50)`. So **`K_n−e` approaches equality as `n → ∞`** — the `(0.857,1)` gap
seen at `n≤9` closes for large `n` (e.g. `K_{21}−e` already has `ratio>0.95`). The
corpus simply did not reach `n` large enough.

**So "near-equality from below" = almost-complete graphs:** `K_n` with `O(1)`
missing edges, tightest with a single missing edge, ratio `(n−3)/(n−2)`.

---

## Synthesis

- **Equality `λ₂(T)=λ₂(G)` ⟺ `G = K_n`** (exactly; 6/6 in the deduplicated corpus,
  exhaustive through `n=7`). All are complete/regular/vertex-transitive, `τ=n−2`,
  `T(G)=J(n,2)`, `|Aut|=n!`.
- The mechanism is **lift exactness**: only for `K_n` does the `T(G)`-Fiedler lie
  exactly in `range(Bᵀ)` (the additive subspace), making the interlacing bound
  `μ(G) ≤ λ₂(G)` an equality. For every other graph the `T(G)`-Fiedler has a
  non-additive component, forcing `λ₂(T) < λ₂(G)`.
- **No second equality family**, but the inequality is *not* uniformly bounded away
  from equality: `K_n − e` approaches it as `(n−3)/(n−2) → 1`. The margin shrinks
  like `1/(n−2)`. This is the same regime as the original "tightest irregular
  `Q=1.167`" (= `K₉−e`), now identified as an asymptotically-tight family.
- This is distinct from the `W ≤ R''` lock-breaking regime (degree-2 vertex + dense
  background, `Q≈2.2`, `ratio≈0.46`) — that regime is far from equality.

### Caveats
- Corpus `n ≤ 9` (exhaustive `n≤7`, sampled `n=8,9`); equality conclusion is exact
  there and the `K_n` / `K_n−e` structure is provable (`λ₂(J(n,2))=n`; `K_n−e`
  spectrum). Numerical `λ₂`; dedup by Weisfeiler–Lehman hash; `|Aut|` exact for
  complete graphs, else VF2 (capped 60000, no equality graph hit the cap).
