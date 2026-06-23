# Conjecture B — the 3×3 compression route FAILS (`μ_min ≥ −1` is 2×2-only)

Hypothesis: the missing factor-2 in the 2×2 route is carried by the degree–Fiedler direction `Df`, so a
3×3 compression onto `span{f, 1, Df}` would satisfy `μ_min(C) ≥ −1` *and* imply the target. **Result:
REFUTED. Adding any third direction (`Df`, `d`, `P_⊥Df`) DROPS `μ_min` well below `−1`** — the clean
fact `μ_min ≥ −1` is a 2×2-only coincidence (it holds on `span{f,1}` but not on any 3-dim extension).
The compression/interlacing approach is exhausted. Code:
[`conjecture_B_3x3_compression_irregular.py`](../conjecture_B_3x3_compression_irregular.py).

## TASK 1/2 — compressions and `μ_min ≥ −1`

| basis `U` | `C = A|_U` : `μ_min(C) ≥ −1` | `min μ_min` |
|---|---|---|
| **`span{f, 1}`** (2×2) | **46/46** | **−1.000** (tight `K_n`) |
| `span{f, 1, Df}` | **22/46** | **−3.50** |
| `span{f, 1, d}` | **12/46** | **−2.89** |

> **Adding `Df` or `d` breaks `μ_min ≥ −1`** (drops to `−3.5`). `A + I` is indefinite (bipartite-type
> directions have `μ(A) < −1`); the 2×2 `span{f,1}` avoided them (`f` low-frequency, `1` Perron-like),
> but any 3-dim extension re-admits a negative `A+I` direction. So `μ_min ≥ −1` does **not** scale to 3×3
> — it is a low-dimensional coincidence, not a usable certificate family.

## TASK 3 — the 3×3 compressions do NOT imply the target

Since `μ_min(C_{3×3}) < −1` on 24–34 of 46 graphs, `C + I ⪰ 0` *fails*, so no PSD/minor argument from
the 3×3 compression is even valid. On the tight cases:

| graph | target slack | `μ_min(U1)` | `μ_min(U2,Df)` | `μ_min(U3,d)` |
|---|---|---|---|---|
| `K₁₂` | 0.0 | **−1.0** | −1.0 | −1.0 |
| twin-port `K₈₀` d2 | 0.038 | +1.37 | **−0.34** | **−1.71** |
| deg2+dense(80,.9) | 0.238 | +0.055 | **−1.60** | **−1.19** |

> The 3×3 `μ_min` is *anti-aligned* with the target: where the target is tight-but-positive
> (deg2+dense, twin-port), the 3×3 `μ_min` is *negative* (`< −1`). So the third direction makes the
> certificate worse, not better — the factor-2 is **not** recovered by `Df`/`d`.

## TASK 4 — hard families confirm

Across deg2+dense, twin-port, lollipop, clique+star, near-complete, random dense: the 2×2 `μ_min(U1)` is
the *only* one universally `≥ −1`; both 3×3 extensions fail broadly. The target holds 46/46 throughout,
but no compression `μ_min ≥ −1` certifies it beyond `K_n`.

## TASK 6 — the witness direction is NOT a compression direction

`K_n` is the only graph where all compressions are tight (`μ_min = −1`, target `= 0`). For irregular
graphs the target has *positive* slack while the 3×3 `μ_min` is *negative* — so the structure achieving
the target inequality is **not** captured by adding any fixed direction (`Df`, `d`) to `span{f,1}`. The
factor-2 (from `2m = Σ d`) is carried by the **global degree–Fiedler coupling** `B₁₂ = S/√n` *together
with the full spectrum*, which no finite-rank compression isolates.

## Conclusion — the compression/interlacing route is exhausted

| route | status |
|---|---|
| regular edge-block `μ₂(A) ≥ −1` (2×2) | **PROVES** regular (`λ = d − μ₂ ≤ d+1`) |
| matrix-PSD `A + I − ddᵀ/m ⪰ 0` on `1⊥` | FAILS (13/46) |
| Cauchy–Schwarz | too weak / invalid |
| 2×2 `span{f,1}` `μ_min ≥ −1` | holds, **factor-2 short** |
| **3×3 `span{f,1,Df/d}` `μ_min ≥ −1`** | **FAILS (μ_min < −1)** |

> **No compression/interlacing certificate proves the irregular spectral inequality.** The clean
> `μ_min ≥ −1` is 2×2-only (factor-2 short); extending the compression destroys it. The regular case is
> the *maximal* reach of the interlacing approach (it uses `λ = d − μ₂`, which has no irregular
> analogue).

So the irregular case must be attacked **not** spectrally (compression) but via the **direct
deficit/complement inequality** `A − B ≥ λ(d_eff + 1 − λ)` (the combinatorial route that proved the
regular case as `gap = λ(n−λ) − C`, `C ≤ (n−1−d)λ`) — generalizing the *counting* bound, not the
spectral compression. The spectral reformulation `λ + S²/m ≤ d_eff + 1` is true but is a *consequence*,
not a provable *handle*, for irregular graphs.

## Lean
No new lemma. The compression route ends here: `μ_min ≥ −1` works only at 2×2 (proves regular via the
edge block; `triEnergy_le_RHS_regular`). The irregular target needs the combinatorial deficit bound,
not an interlacing certificate.
