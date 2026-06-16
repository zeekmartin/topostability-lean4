# Conjecture B — proof v3: attacking the degree-discrepancy core (DEG′)

Continues [`conjecture_B_proof_v2.md`](conjecture_B_proof_v2.md). The reduction
chain `B ⟸ (S2) ⟸ (DEG) ⟺ (DEG′)` is established and rigorous; v3 attacks the
open core `(DEG′)`. Result: **no full proof yet**, but the core is simplified to a
single clean edge-sum, narrowed to an even cleaner *degree-extremal* inequality
`(C4)` that holds on **5,600+ graphs with zero failures**, and three natural
proof routes are *provably ruled out* — sharpening exactly what a proof must do.

Code: [`conjecture_B_proof_v3_explore.py`](../conjecture_B_proof_v3_explore.py).

Notation: `f` = unit Fiedler vector (`L_G f = λ₂ f`, `f⟂1`, `‖f‖=1`); `d` = degree
vector; `disc(v) = Σ_{b∼v}(d_b − d_v)`; `S = Σ_v d_v f_v = dᵀf`; `m = |E|`;
`δ`,`Δ` = min/max degree; `fᵀDf = Σ_v d_v f_v²`.

The open core (v2):
```
(DEG′)   ½ Σ_v f_v² disc(v) − ½ Σ_{ab∈E} |d_a−d_b|(f_a−f_b)²
         ≤  λ₂ ( fᵀDf − λ₂ + 1 − S²/m ).
```

---

## 1. Exact simplification of the LHS (rigorous)

**Identity 1.** `Σ_v f_v² disc(v) = Σ_{ab∈E}(d_b − d_a)(f_a² − f_b²)`.
*Proof.* Expand `disc(v)` over neighbours and regroup by edges. ∎ (max err 4e-14.)

**Identity 2 (LHS collapse).** Combining the two LHS terms edge-by-edge,
```
  ½(d_b−d_a)(f_a²−f_b²) − ½|d_a−d_b|(f_a−f_b)²  =  − |d_a−d_b| · f_h · (f_h − f_l),
```
where `h`, `l` are the higher- / lower-degree endpoints of the edge. Hence
```
  LHS(DEG′)  =  − Σ_{ab∈E} |d_a−d_b| · f_h · (f_h − f_l)
             =    Σ_{ab∈E} |d_a−d_b| · f_h · (f_l − f_h).
```
*Proof.* Per edge with `d_a ≥ d_b` (so `h=a`), `ring`:
`½(d_b−a)(f_a²−f_b²) − ½(d_a−d_b)(f_a−f_b)² = −(d_a−d_b)f_a(f_a−f_b)`. The
`d_a<d_b` case is symmetric. ∎ (max err 6e-15.)

So the entire open core is the single sum `Σ_{ab}|d_a−d_b| f_h(f_l−f_h)`: a
degree-gap-weighted coupling of the **higher-degree endpoint's value** `f_h` with
the **edge gradient** `f_l − f_h`. Only edges with unequal endpoint degrees
contribute; regular graphs give `LHS = 0` (recovering the proved case).

---

## 2. Literature search

Lower bounds on `λ₂` are the hard direction — the survey literature notes ~12
known *upper* bounds for `λ₂(G)` but only ~4 *lower* bounds, "typically far from
sharp" ([de Abreu, *Old and new results on algebraic connectivity*](https://www.math.ucdavis.edu/~saito/data/graphlap/deabreu-algconn.pdf);
[Laplacian eigenvalues survey, arXiv:1111.2897](https://arxiv.org/pdf/1111.2897)).
Findings relevant to `(DEG′)`:

1. **`λ₂ ≤ δ` (classical, Fiedler).** Algebraic connectivity never exceeds the
   minimum degree. This is exactly what makes the degree-extremal target `(C4)`
   below *imply* `(DEG′)` (it lets us replace `fᵀDf ≥ δ`). Confirmed standard.
2. **Signless Laplacian.** `Q = D+A` and `fᵀQf = 2fᵀDf − λ₂`; many Laplacian
   bound techniques transfer to `Q`, but no result was found bounding a
   degree-discrepancy form `Σ_v f_v² disc(v)` by `λ₂`.
3. **Degree-perturbed / weighted-Laplacian interlacing.** General interlacing
   exists, but nothing off-the-shelf compares `λ₂` of a degree-reweighted
   Laplacian (our `L_t`, `L_md`) to `λ₂(G)` in the needed direction.
4. **Line / triangle / Gallai graph spectra.** No published relation of the form
   `λ₂(T(G)) ≤ λ₂(G)` was located; the line-graph Laplacian spectrum is studied
   but not its algebraic connectivity versus `G`'s. (Lower bounds for `λ₂` via
   matching/edge-cover number exist — [arXiv:1401.2227](https://arxiv.org/pdf/1401.2227) —
   but do not apply here.)

**Conclusion of the search:** no off-the-shelf theorem closes `(DEG′)`. The only
directly usable classical input is `λ₂ ≤ δ`. So the proof must be largely
self-contained.

Sources: [Laplacian eigenvalues survey](https://arxiv.org/pdf/1111.2897),
[de Abreu survey](https://www.math.ucdavis.edu/~saito/data/graphlap/deabreu-algconn.pdf),
[lower bounds via matching number](https://arxiv.org/pdf/1401.2227),
[algebraic connectivity (Wikipedia)](https://en.wikipedia.org/wiki/Algebraic_connectivity).

---

## 3. Direct proof attempts (numerics: 52 tightest + 4000+ broad, n ≤ 14)

### 3a. The reduced degree-extremal target `(C4)` — universal

Following the suggested chain `fᵀDf = λ₂ + fᵀAf` and `fᵀDf ≥ δ` (since
`fᵀDf = Σ d_v f_v² ≥ δ‖f‖² = δ`), replace `fᵀDf` by `δ` in the RHS. Because
`δ ≤ fᵀDf`, the resulting inequality is **stronger** and implies `(DEG′)`:
```
(C4)   Σ_{ab∈E} |d_a−d_b| f_h(f_l−f_h)  ≤  λ₂ ( δ − λ₂ + 1 − S²/m ).
```
**`(C4)` holds on every graph tested: 4003/4003 (n ≤ 14) plus 1623/1623 earlier —
0 failures over ~5,600 graphs.** This is the cleanest sufficient condition found:
it eliminates the eigenvector-dependent `fᵀDf` in favour of the **degree extremes
`δ`**, leaving `λ₂`, `δ`, and the imbalance `S` as the only global quantities.
(The user's `fᵀAf ≤ λ_max(A)` gives the matching upper bound `fᵀDf ≤ λ₂+λ_max(A)`;
it is the *lower* bound `fᵀDf ≥ δ` that does the work here.)

### 3b. What a proof must use — three routes provably ruled out

| route | claim | verdict |
|---|---|---|
| **C1** | `LHS ≤ 0` (gradient penalty dominates the discrepancy) | ❌ fails ~70% (`LHS>0` on 1096/1571) |
| **C5** | drop the gradient penalty: `½Σf_v²disc(v) ≤ λ₂(fᵀDf−λ₂+1)` | ❌ fails (1395/1571) |
| **C7** | drop the `+1`: `LHS ≤ λ₂(δ−λ₂)` | ❌ fails (3822/4003) |
| **C2** | Cauchy–Schwarz `|LHS| ≤ √(Σ|d_a−d_b|f_h²)·√E_grad ≤ RHS` | ❌ 12 genuine failures (positive-LHS) |

Consequences — a correct proof of `(C4)`/`(DEG′)` **must**:
- **keep the gradient penalty** `½Σ|d_a−d_b|(f_a−f_b)²` (C5 shows the discrepancy
  alone overshoots), yet **cannot** rely on it dominating (C1);
- **use the `+1`** term (C7 shows `λ₂(δ−λ₂)` is too small);
- be **finer than Cauchy–Schwarz** — C-S is the optimal bound of the form
  `|Σ a_i b_i| ≤ √(Σa²)√(Σb²)` (equivalently optimal Young splitting), and it
  fails by a hair on 12 graphs. The proof must exploit the *correlation* between
  `f_h` (value at the high-degree endpoint) and the edge gradient `f_l−f_h`, not
  just their separate magnitudes.

The obstruction is structural: the `|d_a−d_b|` and the higher/lower-endpoint
asymmetry break linearity, so the eigenvector equation `L_G f = λ₂ f` cannot be
applied to the LHS directly (unlike the degree-sum identity, which is linear and
*was* solved exactly in v2).

---

## 4. Status and the precise remaining problem

> **Open target `(C4)`** (implies `(DEG′)`, hence Conjecture B):
> for connected non-bipartite `G` with unit Fiedler vector `f`,
> `Σ_{ab∈E} |d_a−d_b| · f_h · (f_l − f_h)  ≤  λ₂ ( δ − λ₂ + 1 − S²/m )`,
> where `h`/`l` are the higher/lower-degree endpoints and `S = Σ_v d_v f_v`.

- **Rigorous (this round):** Identities 1–2 (the LHS collapses to one edge-sum);
  the implication `(C4) ⟹ (DEG′)` via `λ₂ ≤ δ`; the elimination of routes
  C1/C5/C7/C2.
- **Empirical:** `(C4)` on ~5,600 graphs, 0 failures; `(DEG′)` likewise.
- **Open:** a proof of `(C4)`. It needs a finer-than-Cauchy–Schwarz argument that
  couples `f_h` with the gradient and uses the `+1` and the gradient penalty
  together — plausibly a graph-specific summation-by-parts or a dedicated
  degree-discrepancy lemma (none found in the literature).

No full proof emerged, so no new Lean formalization was added this round (the
per-edge Identity 2 is a one-line `ring` fact; the substantive verified lemmas
remain those of v1/v2: `edgeLift_eval`, `edgeLift_diff_triangle`,
`triCount_le_degree_sub_one`, `triCount_le_min_degree_sub_one`).

### Caveats
- Tests: `K_n−ke`, complete multipartite, split/threshold, broad random sweeps
  `n=6..14`, all densities with `T(G)` connected; `λ₂` numerical (`eigvalsh`,
  tol 1e-9). Non-bipartite assumed.
- `(C4)` is *stronger* than `(DEG′)`; should it fail at larger `n`, `(DEG′)` (with
  `fᵀDf` in place of `δ`) remains the fallback target — it has a strictly larger
  RHS and the same verified track record.
