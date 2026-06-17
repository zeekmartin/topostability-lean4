# Conjecture B — the final lemma: the Cheeger route is refuted; the gap is a degree-scale effect

**Target.** Establish `λ₂(G[B]) ≥ c·λ₂(G)` for `B = V \ C₈₀` (complement of the p=80% Fiedler
carriers), via the intuition "removing the bottleneck carriers restores conductance." Code:
[`conjecture_B_final_lemma.py`](../conjecture_B_final_lemma.py). Corpus: 1260 `Required > 0`
graphs.

**Headline (negative for the proposed route, clarifying for the real one).** The
Cheeger/cut/connectivity intuition behind TASKS 1–3 is **refuted on all three counts**:
1. **Conductance does not jump.** `h(G[B])/h(G)` has median **0.99** (≥2 for only 24%) and
   **zero correlation** with the λ₂-ratio (`−0.056`), while `λ₂(G[B])/λ₂(G) ≥ 2.43`. The
   spectral gap grows with the conductance essentially unchanged.
2. **The carriers are not on the nodal cut.** Only **1% (median 0%)** of nodal sign-change
   edges touch `C₈₀`. Carriers are the *largest-|f|* vertices — deep inside a nodal domain —
   while the cut is where `f ≈ 0`. They are geometric opposites, not coincident.
3. **`C₈₀` contains no vertex cut.** Removing it **never disconnects** G (0% of a 60-graph
   sample); `|C₈₀| ≤ κ(G)` always, but that is not the mechanism.

The gap `λ₂(G[B]) ≫ λ₂(G)` is therefore **not** a conductance effect. The surviving
explanation is **degree scale**: the combinatorial `λ₂` scales with vertex degree, `λ₂(G) ≤
δ(G)` is pinned by the low-degree bottleneck carriers, and `B` is the high-degree complement.
This is rigorous on the dense majority (via `2δ_B − |B| + 2`) but **not** universally — so the
final lemma is **not proved**; the proposed route is closed and the real obstruction is
relocated.

---

## TASK 1 — Cheeger: conductance does **not** jump

Sweep-conductance (normalized, in `[0,1]`) of `G` vs `G[B]`:

| family | `n` | `λ₂` | λ₂-ratio | `h(G)` | `h(B)` | `h(B)/h(G)` |
|---|---|---|---|---|---|---|
| deg2dense | 200 | 1.994 | 53.9 | 0.492 | 0.494 | **1.0** |
| lollipop (50,10) | 60 | 0.026 | 8.0 | 0.053 | 0.200 | 3.8 |
| lollipop (30,20) | 50 | 0.009 | 6.5 | 0.026 | 0.077 | 3.0 |

Aggregate (N=1260): `h(B)/h(G)` **min 0.81, median 0.99**, `≥ 2` for only **24%**;
`corr(h(B)/h(G), λ₂-ratio) = −0.056`.

**Why the intuition fails.** Combinatorial conductance `h = cut/vol ∈ [0,1]` measures
*normalized* connectivity; the dense deg2+dense block and the bottlenecked `G` have *the same*
normalized conductance (`≈ 0.49`). But the **combinatorial** `λ₂ ≈ h × (degree scale)`: the
block's degrees are `~ qn` while `G`'s effective degree near the bottleneck is `O(1)`. So
`λ₂(G[B])/λ₂(G) ≈ 54` with `h(B)/h(G) ≈ 1`. **The gap is degree scale, not conductance.** (For
the lollipop the conductance *does* rise modestly, 3–4×, because the path is a genuine
normalized bottleneck — but even there the bulk of the ratio is degree scale, `λ₂(clique)=m`.)

## TASK 2 — `C₈₀` contains no vertex cut

Sample of 60 small graphs: `|C₈₀| ≤ κ(G)` for **100%**, but **removing `C₈₀` disconnects `G`
for 0%**. So although the carrier set is small (`≤` vertex connectivity), it is **not** a
separator — the graph stays connected without it. The "big side of a vertex cut" argument does
not apply: there is no cut for `C₈₀` to be the small side of. `B` is well-connected for a
different reason (its internal degrees), not because it is a cut component.

## TASK 3 — the carriers are the opposite of the nodal cut

Fraction of nodal sign-change edges (`V⁺/V⁻` boundary of the Fiedler) incident to `C₈₀`:
**min 0, median 0, mean 0.01**; `≥ 90%` incident for only **1%** of graphs.

**The premise is geometrically backwards.** Carriers `C₈₀ = {largest f_v²}` sit at the
*extrema* of the Fiedler — the deep interior of a nodal domain. The nodal cut is where
`f ≈ 0`, i.e. the *smallest* `|f_v|` vertices — the complement of `C₈₀`. For deg2+dense the
nodal cut is **not** the two edges at `v₀`: the eigen-equation `(2−λ₂)f_{v₀} = f_a + f_b ≈ 0`
forces `v₀`'s neighbours `a,b` slightly *positive*, so they (high-degree dense vertices) carry
the sign boundary against the negative bulk — a large cut deep in the dense block, of which
`v₀`'s 2 edges are a vanishing fraction. Removing `C₈₀` does **not** remove the nodal cut.

## TASK 4 — energy decomposition (confirms flatness, not the gap)

`λ₂ = Σ_edges (f_a − f_b)²` split by carrier membership:

| component | fraction of `λ₂` (median) |
|---|---|
| cut `C–B` | **0.957** |
| internal-`B` | 0.042 (`< 0.1` for 75%, `< 0.5` for 90%) |
| internal-`C` + other | remainder |

So the Fiedler's variation lives almost entirely on the carrier-boundary edges, and **`f` is
flat on `B`** (internal-`B` energy vanishing). This is exactly the **Poincaré-on-block picture**
— `‖forcing‖²` (the cut term) dominates, `f|_B ≈ const` — and it confirms the *consequence* of
a large `λ₂(G[B])`. **But it does not prove the gap:** `f` being flat on `B` follows from
`λ₂(G[B])` being large (Poincaré, prior round); it cannot be used to establish it without
circularity. The 23% of graphs with internal-`B` `> 30%` are the path-bottleneck lollipops,
where the p=80% block retains a path stub carrying real ramp energy.

---

## Synthesis — the real mechanism, and what remains

**The proposed Cheeger route is refuted.** Conductance does not jump (TASK 1), the carriers are
not a cut (TASK 2) and not on the nodal boundary (TASK 3); the energy decomposition (TASK 4)
only re-expresses the already-known flatness of `f|_B`. The chain
`Cheeger(B) ≫ Cheeger(G) ⇒ λ₂(B) ≫ λ₂(G)` is **false** — both conductances are comparable.

**The surviving explanation is degree scale.** Combinatorial algebraic connectivity satisfies
`λ₂ ≤ δ` (min degree) and, for internally-dense `H`, `λ₂(H) ≥ 2δ_H − |H| + 2`. The earlier
necessary condition (`Required > 0 ⟺ fᵀAf < S²/m ⟺ fᵀDf` small `⟺` Fiedler mass on
**low-degree** vertices) means the carriers `C₈₀` are exactly the low-degree bottleneck, so
`λ₂(G) ≤ δ(G)` is small, while `B` is the **high-degree** complement with `λ₂(G[B])` on the
scale of its internal degrees. This gives the gap **without** conductance:

> `λ₂(G[B]) ≈ (normalized gap) × (degree scale of B) ≫ (normalized gap) × δ(G) ≥ λ₂(G).`

**What this does and does not settle.** The degree-scale bound `2δ_B − |B| + 2` proves
`λ₂(G[B]) ≥ c·λ₂(G)` on the **internally-dense** blocks (≈70% of degree-median blocks, and the
deg2+dense / clique cores), but **not universally** (the p=80% block is dense-by-half only
31–57% of the time, and lollipop path-stubs are sparse). So the universal `ratio ≥ 2.5`
(round `final_threshold`) is **still not derived from a single classical inequality**. The
honest status: the final lemma is **not proved**; the conductance route is closed, and the gap
is correctly attributed to degree scale, which is rigorous only on the dense majority.

**Revised remaining obstruction.** Prove the degree-scale statement in the form actually needed:

> `Required > 0 ⟹ λ₂(G[B]) ≥ c·λ₂(G)` where the right tool is **not** Cheeger but the
> interplay of `λ₂(G) ≤ δ(G)` (carriers = low-degree) with a lower bound on `λ₂(G[B])` from
> `B`'s internal degree sequence — uniformly, including the non-dense p=80% blocks.

This redirects the search away from isoperimetry toward degree/eigenvalue interlacing bounds
(Brouwer–Haemers `λ₂ ≥ δ − (n − 1 − δ)`-type, or Kirkland's bounds on algebraic connectivity by
degree sequence), which is where a universal proof of `ratio ≥ c` would now come from.

### Caveats
`λ₂`, `f` numerical; N = 1260 `Required > 0` graphs (deg2+dense, degk, lollipops, path-end,
two-cycles). `h` is the **sweep** (normalized) conductance — an upper bound on the true Cheeger
constant, computed via the Fiedler sweep; the qualitative conclusion (`h(B)/h(G) ≈ 1` while the
combinatorial λ₂-ratio is large) is robust to this. Vertex connectivity sampled on 60 graphs
with `n ≤ 45`. The degree-scale lower bound `2δ_B − |B| + 2` is classical and exact; its
insufficiency on non-dense blocks is the open point. No claim here is a completed proof of the
lemma — the round's result is the **refutation** of the conductance route and the relocation of
the obstruction to degree-sequence eigenvalue bounds.
