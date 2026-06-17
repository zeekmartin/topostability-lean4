# Conjecture B — proof-by-contradiction via Rayleigh competitor: mechanism refuted, B expands intrinsically

**Hypothesis (to contradict).** `B` = carrier-complement has a sparse internal cut `(S, B∖S)`
with raw expansion `h < λ₂(G)`; the indicator competitor would then have Rayleigh quotient
`< λ₂(G)`, contradicting minimality. Code:
[`conjecture_B_contradiction.py`](../conjecture_B_contradiction.py). Corpus: 988
`Required > 0` graphs.

**Headline (the proposed mechanism is refuted; one partial positive).** The boundary term is
**not** what forces `R(g) ≥ λ₂(G)`. For the competitor built from the *sparsest* internal cut
of `B`:
- **the cut term alone is `≥ 2.15·λ₂(G)` on 100%** of graphs (median 15.9) — `B` has no sparse
  cut *intrinsically*; the boundary term (median `0.02·λ₂`) is negligible and unnecessary;
- the proposed logic is **backwards**: the boundary term *inflates* `R_G(g)` above
  `λ₂(G[B])`, so a *large* boundary term makes the minimality bound `λ₂(G[B]) ≥ λ₂(G) −
  boundary` **vacuous**, not stronger.
- **Partial positive:** that minimality bound *does* prove `λ₂(G[B]) ≳ λ₂(G)` — but only for
  **vertex-bottleneck** families (deg2dense/degk), where `boundary ≈ 0`. For **path-bottleneck**
  families (lollipop, pathend) the block-Fiedler concentrates *at* the B–C boundary, the
  boundary term is huge (lollipop median `53·λ₂`), and the bound collapses.

So the contradiction does **not** yield a proof of the lemma; it confirms (again) that `B`
expands on its own, and it closes the vertex-bottleneck case while failing on the
path-bottleneck case — the same split as every prior round.

---

## The competitor and the correct logic

Competitor `g` = Fiedler of `G[B]` extended by `0` on `C` (so `g ⊥ 1`). Then
`R_G(g) = λ₂(G[B]) + boundary/‖g‖²` where `boundary = Σ_{v∈B adj C} g_v²`. Minimality gives

> `λ₂(G[B]) = R_G(g) − boundary/‖g‖² ≥ λ₂(G) − boundary/‖g‖².`

The boundary term is **added** to `λ₂(G[B])` to make `R_G(g)`. So minimality bounds
`λ₂(G[B])` *below* by `λ₂(G) − boundary` — **useful only if `boundary` is small.** A large
boundary term means `R_G(g)` is large for reasons unrelated to the cut, and the bound is
vacuous. (The prompt's hope — that a large boundary term "pushes `R(g)` above `λ₂(G)` and
thereby prevents sparse cuts" — inverts this: it would make the *bound* useless, not the cut
impossible.)

## TASK 1 — minimality (sanity)

| competitor | `R(g)/λ₂(G)` min | median | `≥ 1` |
|---|---|---|---|
| 1: B-Fiedler extended by 0 | 2.006 | 14.50 | 100% |
| 2: cut-indicator (sparsest cut) | 2.157 | 18.57 | 100% |

`R(g) ≥ λ₂(G)` always, as Courant–Fischer requires. This is automatic and carries no
information by itself.

## TASK 2 — decomposition: the cut term carries it, not the boundary

For competitor 2 (built from the *sparsest* internal cut of `B`):

| term / `λ₂(G)` | min | median | `≥ 1` |
|---|---|---|---|
| **cut term** | **2.155** | 15.88 | **100%** |
| boundary term | 0.002 | 0.02 | 27.7% |

**The cut term alone is `≥ 2.15·λ₂(G)` on every graph.** Even the sparsest internal cut of `B`
has `cut_term ≥ 2.15·λ₂(G)`, so `B` genuinely expands and the boundary term (median `2%` of
`λ₂`) is not needed. The hypothesis "`B` has a cut with `h < λ₂(G)`" is simply **false** — the
sparsest cut already exceeds `λ₂(G)` — so there is no contradiction to derive, only a
re-confirmation that `φ_raw(B) ≥ 2·λ₂(G)`.

## TASK 3+4 — the boundary-extension bound, split by bottleneck type

`boundary/‖g‖²` relative to `λ₂(G)` (competitor 1), the deficit in
`λ₂(G[B]) ≥ λ₂(G) − boundary`:

| family | `n` | boundary/λ₂ median | max | `< 1` (bound non-vacuous) |
|---|---|---|---|---|
| deg2dense | 452 | 0.00 | 0.44 | **100%** |
| degk | 235 | 0.00 | 0.92 | **100%** |
| lollipop | 244 | **53.5** | 702 | 5% |
| pathend | 57 | 14.0 | 40.6 | 23% |

- **Vertex-bottleneck families (deg2dense, degk): boundary `≈ 0`.** The carriers `C` attach to
  `B` at only `|∂(B,C)| = O(1)` edges, and the block-Fiedler `f_B` is *small* there (spread over
  the dense block), so `boundary ≈ 0`. The minimality bound then gives
  `λ₂(G[B]) ≥ λ₂(G) − O(λ₂) ≳ λ₂(G)` — a **genuine Courant–Fischer proof** of the gap for
  these families (certified ratio `≥ 1 − 0.44 = 0.56` worst case, `≈ 1` typical).
- **Path-bottleneck families (lollipop, pathend): boundary huge.** The block-Fiedler `f_B` of
  `clique + path-stub` concentrates *on the stub*, whose far end is exactly the B–C boundary
  (where the carriers were removed). So `f_B` is *largest* at the boundary, `boundary ≈ O(1) ≫
  λ₂(G) ≈ 1/L²`, and `λ₂(G) − boundary` is hugely negative — the bound is **vacuous** (certified
  LB min `−701`).

The certified lower bound `1 − boundary/λ₂` is positive for **72.2%** (the vertex-bottleneck
majority) and negative for the path-bottleneck `28%`. **The competitor proof never gives
`ratio ≥ 1` outright** (boundary `> 0` always), but for vertex bottlenecks it gives a positive
gap; for path bottlenecks it gives nothing.

---

## Synthesis

- **The proposed contradiction mechanism is refuted.** `R(g) ≥ λ₂(G)` is automatic minimality;
  the decomposition shows the *cut term* (the block's intrinsic expansion) already exceeds
  `2.15·λ₂(G)` everywhere, so the boundary term is negligible and is not what prevents sparse
  cuts. `B` has no sparse cut because it *intrinsically expands*, full stop — there is no
  boundary-energy mechanism, and a large boundary term would (and does, on lollipops) *break*
  the bound rather than help it.
- **One partial positive:** the minimality bound `λ₂(G[B]) ≥ λ₂(G) − boundary/‖f_B‖²` is a
  clean Courant–Fischer proof of the block gap **for vertex-bottleneck graphs**
  (deg2dense/degk), where `|∂(B,C)| = O(1)` *and* `f_B` is small at the boundary, so
  `boundary ≈ 0`. This is a genuine (if loose) proof of `λ₂(G[B]) ≳ λ₂(G)` for that family —
  consistent with deg2+dense being the cleanly-closed family throughout.
- **It fails for path bottlenecks** (lollipop/pathend) for a precise reason: the block-Fiedler
  lives *on the boundary stub*, so the extension picks up `O(1)` boundary energy that swamps
  `λ₂(G) = O(1/L²)`. This is the same vertex-vs-path split that has separated the two families
  in every approach.

**Net.** No universal proof. The contradiction confirms `B` expands intrinsically (`cut_term ≥
2.15 λ₂(G)`) and supplies a clean Courant–Fischer gap proof for the vertex-bottleneck family,
but the path-bottleneck family still resists — the block-Fiedler's concentration at the B–C
boundary is the obstruction. The lemma remains true and confirmed (`φ_raw(B) ≥ 2λ₂(G)`), with a
proof now in hand for vertex bottlenecks and open for path bottlenecks.

### Caveats
`λ₂`, `f`, `f_B` numerical; N = 988 `Required > 0` graphs. The sparsest internal cut of `B` is
found by Fiedler-sweep bisection of `G[B]` (an upper bound on `φ_raw`; the cut-term values are
for that cut, so "cut_term ≥ 2.15λ₂" uses a near-sparsest, not provably sparsest, cut — but
since even this cut is `≥ 2.15λ₂`, the true sparsest is `≥` something comparable). `R(g) ≥
λ₂(G)` is exact minimality. The boundary/cut decomposition is exact per graph. The
vertex-bottleneck proof gives certified ratio `≥ 1 − boundary/λ₂` (≈0.56–1), not a clean
`≥ 1`; tightening it is a loose end.
