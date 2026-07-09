# Does the Li-Ji technique transfer to Conjecture B?

**Verdict: NO.** The Li-Ji "expand `‖L z‖²`, no test vector" engine, lifted to
edge space via the incidence matrix, produces the operator `B L² Bᵀ`, and this
operator does **not** control the T(G) form `L_{T(G)}` — neither as matrices nor
on Fiedler lifts. The failure is structural and comes in two independent layers
(subspace mismatch and homogeneity mismatch), and it is not repairable by
`B Lᵏ Bᵀ` or `B(L²+αL)Bᵀ` variants. Details below.

Script: `liji_transfer_test.py` (18-graph corpus: K₆, K₁₀, gnp, deg2dense, twin,
lollipop, barbell, wheel, regular, Petersen, cube Q₃, icosahedral, octahedral).

Conventions: `B` is the oriented incidence matrix (m×n), `B_{e,v}=+1` if `v` is
the head of `e`, `−1` if the tail, so `L_G = Bᵀ B`. The lift of a vertex vector
`f` is the edge-difference `h = B f`, i.e. `h_e = f_a − f_b` for `e=(a,b)`.

---

## TASK 1 — The entries of `B L² Bᵀ`

Because each row of `B` is `u_e = δ_a − δ_b`, the whole operator is a
double-difference of the `L²` matrix:

> **`(B L² Bᵀ)_{e,e'} = (L²)_{ac} − (L²)_{ad} − (L²)_{bc} + (L²)_{bd}`**,  for `e=(a,b), e'=(c,d)`.

Verified to **machine zero** (`expand-err = 0.00e+00`) on all graphs. Feeding in
the Li-Ji entrywise identity `(L²)_{ij} = −a_{ij}(d_i+d_j) + c_{ij}` (`i≠j`),
`(L²)_{ii} = d_i(d_i+1)`, the diagonal collapses to a clean closed form
(also verified to machine zero):

> **`(B L² Bᵀ)_{e,e} = d_a² + d_b² + 3(d_a + d_b) − 2 t_e`**,  where `t_e = c_{ab}` = #triangles on `e`.

**Where does `t_e` appear?** *In the diagonal, cleanly, with coefficient `−2`*
(via `c_{ab}=t_e`). It does **not** appear cleanly in the off-diagonal: for two
edges sharing a triangle the off-diagonal entry is a signed sum of four
common-neighbour counts `c_{··}` **tangled with degree factors** `−a(d_i+d_j)`,
which does not reduce to the T(G) adjacency `−1`. So `B L² Bᵀ` is *not* a
rescaling of `L_{T(G)}`; the triangle content sits on the diagonal, not on the
edge-sharing off-diagonal where `L_{T(G)}` carries its structure. This is the
first sign the analogy is misaligned.

---

## TASK 2 — The `‖L Bᵀ h‖²` expansion

For any edge-vector `h`, `hᵀ(B L² Bᵀ)h = ‖L·(Bᵀh)‖² ≥ 0` — a genuine
nonnegative form, the direct analog of Li-Ji's `‖L z‖² = zᵀL²z ≥ 0`.

**Why it cannot isolate `L_{T(G)}`.** The zero-row-sum identity does apply, but
the resulting decomposition lives on the *wrong subspace*. `B L² Bᵀ = (BL)(BL)ᵀ`
is PSD with kernel `= ker(Bᵀ) = ` the **cycle space** of `G` (dimension
`m−n+1`). `L_{T(G)}` has kernel `= ` constants (dimension 1, when T(G) is
connected). These kernels are different, so no inequality `B L² Bᵀ ⪰ C·L_{T(G)}`
can hold as m×m matrices for any `C>0`: pick `h` in the cycle space, then
`hᵀ(BL²Bᵀ)h = 0` while `hᵀL_{T(G)}h > 0` generically. Li-Ji never hit this
because their comparison `(n−1)L_G ⪰ L_{A^[2]}` stays entirely in vertex space —
both sides share the kernel `span(1)`. Lifting to edge space breaks that.

The honest comparison is therefore restricted to the **cut space** (image of
`B`, i.e. the lifts `h = Bf`), which is where Conjecture B actually lives.

---

## TASK 3 — Numerical comparison on Fiedler lifts

`f` = unit Fiedler vector, `h = Bf`. Columns:
`(a)=hᵀ(BL²Bᵀ)h`, `(b)=hᵀL_{T(G)}h`, `(c)=λ·hᵀh` (Conjecture-B scale),
`C_cut = min_{f⊥1} (fᵀL⁴f)/(fᵀBᵀL_{T(G)}B f)` = the best constant with
`BL²Bᵀ ⪰ C·L_{T(G)}` on **all** lifts.

| graph | λ | (a) | (b) | (c) | a/b | b/c | **C_cut** |
|---|---|---|---|---|---|---|---|
| K6 | 6.00 | 1296 | 41.8 | 36.0 | 31.0 | 1.16 | 22.7 |
| K10 | 10.00 | 10000 | 122 | 100 | 82.0 | 1.22 | 56.5 |
| gnp_20_.3 | 1.82 | 11.0 | 2.28 | 3.32 | 4.83 | 0.69 | 3.38 |
| deg2dense_12 | 0.70 | 0.24 | 0.76 | 0.49 | 0.31 | 1.56 | 0.23 |
| twin_6 | 6.00 | 1296 | 30.0 | 36.0 | 43.2 | 0.83 | 38.3 |
| lollipop_6_4 | 0.18 | 0.001 | 0.037 | 0.031 | 0.027 | 1.18 | 0.027 |
| barbell_5_1 | 0.17 | 0.001 | 0.075 | 0.029 | 0.011 | 2.56 | 0.011 |
| **barbell_6_3** | 0.075 | 3e-5 | 0.018 | 0.006 | **0.002** | 3.29 | **0.002** |
| wheel_10 | 1.47 | 4.64 | 3.72 | 2.16 | 1.25 | 1.73 | 1.16 |
| wheel_16 | 1.17 | 1.89 | 2.67 | 1.38 | 0.71 | 1.94 | 0.69 |
| regular_3_12 | 0.63 | 0.16 | 0.041 | 0.40 | 3.78 | 0.10 | 1.91 |
| regular_4_14 | 1.43 | 4.16 | 0.56 | 2.04 | 7.38 | 0.28 | 5.65 |
| petersen | 2.00 | 16.0 | 0 | 4.0 | ∞ | 0 | ∞ |
| cube_Q3 | 2.00 | 16.0 | 0 | 4.0 | ∞ | 0 | ∞ |
| icosahedral | 2.76 | 58.4 | 9.05 | 7.64 | 6.45 | 1.19 | 5.21 |
| octahedral | 4.00 | 256 | 16.0 | 16.0 | 16.0 | 1.00 | 12.2 |

(Petersen and Q₃ are triangle-free ⇒ `L_{T(G)}=0`, so `b=0`, trivial ∞.)

Three exact facts fall out (all confirmed numerically):

1. **`(a) = λ⁴·‖f‖²` on the Fiedler lift** (`|a − λ⁴| ≤ 3e−11`). Reason: `Bᵀh =
   BᵀBf = Lf = λf`, so `‖L·Bᵀh‖² = ‖L(λf)‖² = λ⁴‖f‖²`. The operator delivers
   `λ⁴`, wildly overshooting the target scale `(c)=λ²` when `λ` is large and
   collapsing far below it when `λ` is small.

2. **The domination constant collapses.** `min a/b = 0.002` over
   triangle-containing graphs, and `C_cut` drops to **0.0017**. There is **no
   universal constant `C>0`** with `BL²Bᵀ ⪰ C·L_{T(G)}` even on lifts. It fails
   worst exactly on the low-λ bottlenecked graphs (barbell, lollipop) that
   Conjecture B is hardest for.

3. **The overshoot is `λ²`-graded — the exact obstruction.** Numerically
   `a/b = λ²·(c/b)` to 3 decimals on every graph (verified separately). Since
   `hᵀh = fᵀLf = λ`, this says `a/(hᵀh) = λ³` but `b/(hᵀh) = O(λ)`: the two
   forms differ by a factor of `λ²`. As `λ→0`, `a/b → 0`. **`L²` is not
   homogeneous with `L_{T(G)}`.** Li-Ji's `(n−1)` prefactor bridges a *degree-1
   vs degree-2 in `L`* gap in vertex space; here the gap is a `λ²` factor that a
   constant prefactor cannot absorb.

Side note (`b/c`): the *full* T(G) Dirichlet energy of the lift exceeds `λ·hᵀh`
on many graphs (`b/c` up to 3.29), because `h = Bf` is not orthogonal to `1_m`.
So even setting Li-Ji aside, the full-`L_{T(G)}`-on-`Bf` route overshoots the
naive RHS — a separate reason this particular lift is not the Conjecture-B
object. The actual remaining Lean `sorry` is the **diagonal** aggregate form
`Σ_e t_e h_e² ≤ 2λ Σ_v d_v f_v²`, which holds on all 18 graphs (min slack
0.7357) — the conjecture is fine; it is the *Li-Ji route to it* that fails.

---

## TASK 4 — The `|N_i ∪ N_j| ≤ n−1` analog

In Li-Ji the closure is `|N_i∪N_j| = d_i + d_j − c_{ij} ≤ n−1`: a **linear**
per-edge cap that turns the `L²` expansion into `(n−1)L_G`. The edge-space
analog is the diagonal excess of `B L² Bᵀ`, namely

> `d_a² + d_b² + 3(d_a + d_b) − 2 t_e`.

This is **quadratic** in the degrees (`d_a²+d_b²`), not linear, and — crucially
— it is a function of the *endpoint degrees of `e` alone*, carrying **no
reference to how many T(G)-neighbours `e` has**. The Li-Ji cap `n−1` works
because `|N_i∪N_j|` is exactly the count of `z_i−z_j` cross-terms it must
dominate; here the diagonal budget `d_a²+d_b²+…` is unrelated to the T(G)
degree `t_e` (which even enters with the *wrong sign*, `−2t_e`, *reducing* the
budget as an edge gains triangles). There is no bounded per-edge quantity that
plays the role of `n−1`, so the closure step has no analog. This is the
Task-1 misalignment (`t_e` on the diagonal, not the off-diagonal) resurfacing as
a broken closure.

---

## TASK 5 — Report

**(a) Does `B L² Bᵀ` dominate `L_{T(G)}` on Fiedler lifts?** No. `C_cut` reaches
`0.0017`; `a/b` reaches `0.002`. No positive constant survives the corpus.

**(b) Exact inequality / can it close Conjecture B?** The only exact relation is
`hᵀ(BL²Bᵀ)h = λ⁴‖f‖²` on the Fiedler lift, and `a/b = λ²·(c/b)`. Neither closes
Conjecture B: the first overshoots by `λ²` (useless when `λ` is large) and
undershoots by `λ²` (fatal when `λ` is small); the second just re-expresses the
target. Li-Ji's engine gives **no route** to Conjecture B.

**(c) Where does the analogy break?** Two independent failures:

- **Subspace mismatch (Task 2).** `BL²Bᵀ` is singular on the cycle space;
  `L_{T(G)}` is not. Li-Ji stays in vertex space where both operators share
  `ker = span(1)`. Lifting to edges destroys the shared kernel, so matrix
  domination is impossible before any numbers are computed.
- **Homogeneity mismatch (Task 3).** `L²` carries an extra factor of `L`
  relative to what `L_{T(G)}` needs: on the lift the two forms differ by `λ²`.
  Li-Ji's `(n−1)` prefactor cannot be mimicked because the gap here is not a
  scalar but a spectral factor that vanishes with the Fiedler value — precisely
  in the bottlenecked regime.

Concretely (which term fails to control which): the `d_a²+d_b²` **diagonal** of
`BL²Bᵀ` is what carries its mass, and it grows quadratically in degree while
being blind to `t_e`; meanwhile the triangle information `t_e` sits on the
diagonal with a *negative* sign, so it cannot supply the positive
`Σ_{e~e'} (h_e−h_e')²` off-diagonal energy that `L_{T(G)}` demands.

**(d) Do modified operators (`B Lᵏ Bᵀ`, `B(L²+αL)Bᵀ`) help?** No — and there is
a clean reason. For any power, `hᵀ(B Lᵏ Bᵀ)h = (Bᵀh)ᵀ Lᵏ (Bᵀh) = fᵀ L^{k+2} f =
λ^{k+2}‖f‖²` on the Fiedler lift. Matching the `λ²` homogeneity of `L_{T(G)}`
forces `k = 0`, i.e. the operator `B Bᵀ`. But:

- `B Lᵏ Bᵀ` for `k ≥ 1` scales as `λ^{k+2}` and collapses even faster than
  `BL²Bᵀ` for small `λ`. A mixture `B(L²+αL)Bᵀ` gives `λ⁴+αλ³ ~ αλ³`, still
  `→0` faster than `λ²`. Adding an `α` term cannot restore homogeneity.
- The *only* `B·poly(L)·Bᵀ` with the right `λ²` scaling is the constant-term
  operator `B Bᵀ` (line-graph / vertex-sharing operator). Empirically it
  *does* dominate `L_{T(G)}` on Fiedler lifts with a uniform constant:
  `fᵀL²f / hᵀL_{T(G)}h ≥ 0.30` across the corpus (min at barbell_6_3). **But
  `B Bᵀ` contains no triangle information** — its off-diagonal is vertex-sharing
  (`±1` when two edges meet), and `hᵀBBᵀh = fᵀL²f` is just the ordinary
  vertex-space form. So the scaling-matched operator has the wrong combinatorics,
  and the triangle-bearing operators have the wrong scaling. **No `B·poly(L)·Bᵀ`
  can be simultaneously `λ²`-homogeneous and triangle-carrying** — the triangle
  count `t_e` first appears only at `k=2` (`c_{ab}` in `L²`), which is exactly
  where the homogeneity is already wrong.

**Bottom line.** The Li-Ji matrix-inequality engine is a *vertex-space*
identity between two *degree-comparable* Laplacians sharing the kernel
`span(1)`. Conjecture B compares a vertex Laplacian with an *edge-space*
combinatorial Laplacian `L_{T(G)}` of a different kernel and different
homogeneity. Lifting Li-Ji through `B` produces `BL²Bᵀ`, which fails on both
counts — subspace and scaling — and no polynomial-in-`L` correction repairs
both at once. The remaining Conjecture-B `sorry` (the diagonal aggregate
Poincaré, which holds 18/18 numerically) needs a genuinely different mechanism;
the Li-Ji technique does not transfer.
