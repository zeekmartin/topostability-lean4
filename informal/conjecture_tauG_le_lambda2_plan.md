# Plan — last `sorry`: `conjecture_tauG_le_algebraicConnectivity`

**Target.** `Topostability/Paper11.lean:19`
```
theorem conjecture_tauG_le_algebraicConnectivity
    (hconn : G.Connected) (hV : Fintype.card V ≥ 2) :
    (tauG G : ℝ) ≤ algebraicConnectivity G hV
```
where `tauG G = min over edges e of triCount` (= min common-neighbour count over
edges), and `algebraicConnectivity G hV = λ₂` (second-smallest Laplacian eigenvalue).

## ⚠️ Reality check first (do this before any Lean)

This is **Paper 11's "Conjecture 1"**. The name and framing suggest it may be an
**open conjecture** in the paper, not a proved theorem. Step 0 of tomorrow:
- Re-read Paper 11 (Zenodo) and check: is `tauG ≤ λ₂` *proved* there, or *stated as
  a conjecture* with only partial/heuristic evidence?
- If only conjectured → a full Lean proof is a research result; we should instead
  prove the **special cases the paper actually establishes** (likely d-regular)
  and keep the general statement as a documented `sorry` or restate it.
- Sanity values (from `Verify.lean`): `tauG K₃=1`, `tauG K₄=2`, `tauG P₃=0`,
  `tauG C₄=0`. λ₂: K_n = n, P₃ = 1, C₄ = 2. All satisfy `tauG ≤ λ₂`. Consistent,
  no obvious counterexample — but consistency ≠ proof.

## What infrastructure already exists (Paper11, all sorry-free)

- `spectral_identity`: `trace(L·A²) = Σᵢ dᵢ² − 6·totalTriangles G`.
- `lambda2_upper_bound_regular` (d-regular, `0<d<n`):
  `λ₂ ≤ (n·d² − 6T) / (d·(n−d))`.
- `directed_triangle_fiber_card` (counting helper).
- Mathlib spectral API: `isHermitian_lapMatrix`, `posSemidef_lapMatrix`,
  eigenvalues, `lapMatrix_toLinearMap₂'`; plus the whole Paper12 sweep machinery.

## Candidate routes (in increasing difficulty)

### Route A — d-regular case via the existing upper bound (most tractable)
The cleanest first milestone: prove `tauG ≤ λ₂` **for d-regular graphs** and a
clean triangle bound, reusing `lambda2_upper_bound_regular`.
- Hmm: `lambda2_upper_bound_regular` is an UPPER bound on λ₂, but we need a LOWER
  bound on λ₂ to conclude `tauG ≤ λ₂`. So this lemma alone is the **wrong
  direction** — it bounds λ₂ from above, not below. ⇒ Route A as stated does NOT
  close the conjecture; it would need a separate λ₂ lower bound.

### Route B — Rayleigh lower bound on λ₂ (the real engine)
`λ₂ = min_{x ⟂ 1, x≠0} (xᵀ L x)/(xᵀx)`. To prove `λ₂ ≥ tauG` we need: for the
minimizing/Fiedler `x`, `xᵀ L x ≥ tauG · xᵀx`, i.e. a Rayleigh lower bound driven
by the per-edge common-neighbour count. Sub-tasks:
1. A Mathlib bridge `λ₂ = ⨅ Rayleigh over ⟂1` (or `algebraicConnectivity_le_rayleigh`
   already used in Paper13 — check its exact form; it gives λ₂ ≤ Rayleigh, again
   the wrong direction for a lower bound on λ₂).
2. The hard combinatorial core: relate `xᵀ L x = Σ_e (x_u−x_v)²` to triangle/
   common-neighbour structure so that `tauG` appears as a lower factor. This is
   the genuinely novel mathematical content and is **not** obviously in the repo.

### Route C — special graphs only (safe partial win)
Prove the conjecture for concrete families to de-risk and document:
- Complete graphs `K_n`: `tauG = n−2`, `λ₂ = n` ⇒ `n−2 ≤ n` (easy once λ₂(K_n)=n
  is available — check Mathlib for `SimpleGraph.lapMatrix` eigenvalues of `⊤`).
- Edge-empty / triangle-free graphs: `tauG = 0 ≤ λ₂` (just `λ₂ ≥ 0`, which is
  `(posSemidef_lapMatrix).eigenvalues_nonneg`). **This is a 2-line lemma** and a
  good warm-up; it already covers all bridgeless-but-triangle-free cases.

## Recommended order for tomorrow
1. **Step 0**: confirm whether the paper proves it or conjectures it.
2. **Quick win**: prove the `tauG = 0` sub-case (`λ₂ ≥ 0`) as a standalone lemma —
   verifies the API path and covers triangle-free graphs.
3. If the paper has a real proof: transcribe its argument (likely Route B with a
   λ₂ lower bound the paper supplies). Identify the exact lower-bound lemma needed
   and prove it as sub-lemmas, Modal-verified one at a time (same workflow as the
   Cheeger proof).
4. If it's genuinely open: prove the special cases (Route C), restate the top-level
   theorem to the proved scope, and keep the general conjecture clearly marked.

## Workflow reminder
Same Modal loop as the Cheeger proof: develop each sub-lemma in a scratch with
`import Topostability.Paper11`, verify with `lean_check`, integrate, `build`,
commit. API gotchas recorded in memory (`dotProduct_*` root namespace,
`div_le_iff₀`, `Fin.mk_le_mk`, etc.).
