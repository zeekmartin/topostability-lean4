# Cheeger sweep pigeonhole — informal proof (Sub-goal C)

**Target.** Fill `sorry` at `Topostability/Paper12.lean:758`, inside
`sweep_pigeonhole`.

The remaining goal at that `sorry` is:

```
∃ k : Fin (Fintype.card V - 1),
    (Finset.univ.filter fun w => f w ≥ f (σ ⟨k.val + 1, _⟩))ᶜ.Nonempty ∧
    (Finset.univ.filter fun w => f w ≥ f (σ ⟨k.val + 1, _⟩)).card ≤
        Fintype.card V / 2 ∧
    ((edgeBoundary G (Finset.univ.filter fun w =>
            f w ≥ f (σ ⟨k.val + 1, _⟩))).card : ℝ) /
      ↑(Finset.univ.filter fun w =>
            f w ≥ f (σ ⟨k.val + 1, _⟩)).card ≤
      Real.sqrt (2 * algebraicConnectivity G hV * ↑G.maxDegree)
```

(`f` is a Fiedler vector: `f ≠ 0`, `∑ f = 0`, `L f = λ₂ f`.)

Hypotheses in context (see `Paper12.lean:712-744`):

- `σ : Fin n ≃ V` with `hσ : ∀ i j, i ≤ j → f (σ i) ≤ f (σ j)` (sorting bijection).
- `hcoarea` (from `discrete_coarea`):
  `∑ e ∈ edgeFinset, |f u − f v| = ∑ k, gap_k · |∂ S_k|`
  where `S_k := filter (fun w => f w ≥ f (σ (k+1)))`, `gap_k := f (σ (k+1)) − f (σ k)`.
- `hΔ` (from `edge_degree_bound`):
  `∑ e (f u − f v)² ≤ 2 · Δ · ∑_v f v²`.
- `heig_eq` (just above the `sorry`):
  `λ₂ · ∑_v f v² = ∑ e (f u − f v)²`.
- `hfsum : ∑_v f v = 0`; `hf : f ≠ 0`.
- `boundary_cauchy_schwarz` (Paper12.lean, already proved):
  `(∑_e ∈ ∂S, |f u − f v|)² ≤ |∂S| · ∑_e ∈ ∂S (f u − f v)²`.
- `hSne` ensures `S_k` is nonempty (it contains `σ(k+1)`).

---

## Why this is nontrivial

The statement demands **simultaneously** three things about the witness `k`:

1. `Sᶜ` nonempty (easy — `σ(k) ∈ Sᶜ` if the gap is strict, or the case of all
   ties reduces `f = const = 0` which contradicts `hfsum`, `hf`).
2. `|S_k| ≤ n/2` — this restricts `k` to the **upper half** of indices.
3. `|∂S_k| / |S_k| ≤ √(2 λ₂ Δ)`.

A naive pigeonhole `∃ k, |∂S_k|/|S_k| ≤ √(2λ₂Δ)` is already delicate; adding
the `|S_k| ≤ n/2` constraint requires the standard **positive-part / sign-flip**
trick of Alon–Milman.

---

## The Alon–Milman sign-flip (key step)

The cleanest proof uses a **replacement** of `f` by its one-sided positive
part so the sweep cuts are automatically small.

Let `n := Fintype.card V`. Let `m := n / 2` (Nat division). Consider the
median value `c := f (σ ⟨m, _⟩)`. Define

- `P := {v | f v > c}` — has size `n − m − 1` (assuming no ties at `c`) or
  more generally, `P ⊆ {σ(m+1), …, σ(n−1)}`, so `|P| ≤ n − m − 1 ≤ n/2 − 1`.
- `N := {v | f v < c}` — similarly `|N| ≤ m = n/2`.

Both `P` and `N` have size `≤ n/2`.

Define `g⁺ v := max (f v − c) 0` (positive part relative to the median),
`g⁻ v := max (c − f v) 0`. These are supported on `P` and `N` respectively.

**Key estimates.**

- `∑_v (g⁺ v)² + ∑_v (g⁻ v)² ≤ ∑_v (f v − c)² = ∑_v f v² − n · c² ≤ ∑_v f v²`
  (since `(f v − c)² = (g⁺ v)² + (g⁻ v)² − 2 · g⁺ v · g⁻ v` with
  `g⁺ v · g⁻ v = 0`; and `∑_v (f v − c)² = ∑ f v² − 2c·∑ f v + n·c²
  = ∑ f v² + n · c²` — correction: `= ∑ f v² − 2c · 0 + n · c² = ∑ f v² + n c²`).

  *Correct form*: since `∑ f = 0`, `∑ (f−c)² = ∑ f² + n c²`, so
  `∑ g⁺² + ∑ g⁻² ≤ ∑ (f−c)² = ∑ f² + n c²`.

- `∑_e (g⁺_u − g⁺_v)² + ∑_e (g⁻_u − g⁻_v)² ≤ ∑_e (f_u − f_v)²` (Laplacian
  monotonicity: pointwise, `(a−b)² ≥ (a₊−b₊)² + (a₋−b₋)²` where
  `a₊ = max(a,0)`, `a₋ = max(−a,0)`, etc.). This is `(a−b)² − (a₊−b₊)² − (a₋−b₋)²
  = 2·(|a|·b₋ + a₋·|b|) ≥ 0` or similar case analysis. A compact form:
  `(a − b)² ≥ (a₊ − b₊)² + (a₋ − b₋)²` on reals, provable by splitting
  on signs of `a`, `b`.

So **one of** `g⁺` or `g⁻` satisfies the weighted Rayleigh:
`∑_e (h_u − h_v)² / ∑_v (h v)² ≤ λ₂ · (‖f‖² + n c²) / ‖f‖²`  — hmm, this
is off by a factor `(1 + n c² / ‖f‖²)`. If `c = 0` (median coincides with 0)
this is exactly `λ₂`. In general you need a gentler bound.

### Cleaner version: subtract the mean, not the median

Since `∑ f = 0`, the mean is already 0, and `f` itself splits as
`f = f₊ − f₋` with disjoint supports. But `|supp f₊|` might exceed `n/2`
(if most vertices have `f ≥ 0`). **However, at least one of `f₊`, `f₋`
has support size `≤ n/2`** — because their supports are disjoint and the
set `{f = 0}` is "free":
either `|{f > 0}| ≤ n/2` or `|{f < 0}| ≤ n/2`. WLOG `|{f > 0}| ≤ n/2`
(otherwise replace `f` with `−f`, which leaves the problem invariant:
still a Fiedler vector, same `f`-level sets with roles swapped).

With `|{f > 0}| ≤ n/2`, set `h := f₊ := λ v, max (f v) 0`.

**Rayleigh bound for `h`.**

- `∑_v h(v)² = ∑_{v : f(v) > 0} f(v)² ≤ ∑_v f(v)²`.
- `∑_e (h_u − h_v)² ≤ ∑_e (f_u − f_v)²` (pointwise:
  `(max(a,0) − max(b,0))² ≤ (a − b)²` — this is standard and follows
  from the fact that `x ↦ max(x, 0)` is a 1-Lipschitz map on `ℝ`).

Hence `(∑_e (h_u − h_v)²) / (∑_v h(v)²)`
is bounded by `(∑_e (f_u − f_v)²) / (∑_v h(v)²) ≤ λ₂ · ‖f‖² / ‖h‖²`. This
is `≥ λ₂` in general — not helpful directly.

Yes — this is why the classical argument works with `h = f₊` **on its
own support**, not globally. The sweep on `h` gives threshold sets `T_t =
{v : h(v) > t} = {v : f(v) > t}` for `t > 0`, all contained in `{f > 0}`,
so automatically `|T_t| ≤ n/2`. We do **not** need Rayleigh on `h`; we
reuse the original `f` bound via **Cauchy–Schwarz applied to positive
part** directly.

### The clean unified estimate (this is the route we will formalize)

For the Fiedler vector `f`, define `S_k` as in `hcoarea`. Split
`{0, …, n−2}` into two intervals:

- `L := {k : |S_k| > n/2} = {k : n − 1 − k > n/2}` — i.e., `k ≤ ⌈n/2⌉ − 2`.
  For these `k`, `Sᶜ_k` has size `k + 1 ≤ n/2` (so `Sᶜ_k` is the small side).
- `U := {k : |S_k| ≤ n/2}` — i.e., `k ≥ ⌈n/2⌉ − 1`.
  For these, `S_k` itself has size `≤ n/2`.

For the upper interval `U` the sweep witness comes straight from pigeonhole
(see below). For the lower interval `L`, the "switched" sweep cut `Sᶜ_k`
has the small size; but `edgeBoundary G S_k = edgeBoundary G Sᶜ_k` as an
**undirected** notion (and here `interedges S Sᶜ` has the same cardinality
as `interedges Sᶜ S`). So we could reroute to use `Sᶜ_k`, but the
statement of `sweep_pigeonhole` hard-codes `S_k` as the witness.

### Simplification: restrict pigeonhole to the upper half

Because the statement only asks for existence of **one** `k`, we can just
**search `U` and ignore `L`**. The pigeonhole argument must show:

> There exists `k ∈ U` with `|∂S_k| / |S_k| ≤ √(2λ₂Δ)`.

The core inequality is the **Cheeger inequality at the level-set level**,
obtained as follows.

---

## The core Cheeger-at-levels inequality

Define two weighted sums over `k ∈ Fin (n−1)`:

- `A_k := gap_k · |∂S_k|` (gap times boundary size).
- `B_k := gap_k · |S_k|` (gap times interior size).

**Claim (master inequality).**

```
  ∑_k A_k  ≤  √(2 λ₂ Δ) · ∑_k B_k
```

If this holds then a pigeonhole argument: `∑_k gap_k · (|∂S_k| − √(2λ₂Δ) · |S_k|)
≤ 0` means some `k*` (with `gap_{k*} > 0`) has `|∂S_{k*}| ≤ √(2λ₂Δ) · |S_{k*}|`.

**Unfortunately**, as stated, this bound ranges over **all** `k` — it does
NOT restrict to `U`. To restrict: use `min(|S_k|, |Sᶜ_k|)` in `B_k`:

```
  ∑_k gap_k · |∂S_k|  ≤  √(2 λ₂ Δ) · ∑_k gap_k · min(|S_k|, |Sᶜ_k|)
```

Then a pigeonhole on this gives some `k*` with
`|∂S_{k*}| ≤ √(2λ₂Δ) · min(|S_{k*}|, |Sᶜ_{k*}|)`,
and we pick the side where `min` is `|S_{k*}|` — i.e., `k* ∈ U`.

### Deriving the master inequality

Start from the eigenvalue identity:

```
  λ₂ · ‖f‖² = ∑_e (f_u − f_v)²          (heig_eq)
```

Now Cauchy–Schwarz on the **edge** sum, clever weighted form:

```
  ∑_e |f_u² − f_v²|  =  ∑_e |f_u − f_v| · |f_u + f_v|
                    ≤  √(∑_e (f_u − f_v)²) · √(∑_e (f_u + f_v)²)
                    ≤  √(λ₂ · ‖f‖²) · √(2 Δ · ‖f‖²)   [heig_eq; edge_degree_bound applied to (a+b)² via (a+b)² ≤ 2(a² + b²)]
                    =  √(2 λ₂ Δ) · ‖f‖²
```

**But** `∑_e |f_u² − f_v²|` translates via the discrete coarea formula
**applied to `f²` (sorted)** to `∑_k (f(σ(k+1))² − f(σ(k))²) · |∂S_k|`.

And `‖f‖² = ∑_v f v² = ∑_k (f(σ(k+1))² − f(σ(k))²) · |S_k|`
by the identity `∑_v g(v) = ∑_k (t_{k+1} − t_k) · |{v : g(v) ≥ t_{k+1}}|`
for `g = f²` and `t_k = f(σ(k))²`.

**Problem.** `f²` is **not** sorted the same way as `f` — `f²` is sorted
by increasing `|f|`, not by increasing `f`. So applying coarea for `f²`
uses a **different** ordering and different level sets.

This is where the standard proof uses the sign-flip. After WLOG `|{f > 0}| ≤ n/2`,
set `h := f₊`. Then:

- `h` is non-negative, `h²` is sorted the same way as `h` (since `h ≥ 0`).
- `h²`'s sweep cuts `T_k := {v : h v² ≥ h(σ(k+1))²} = {v : h(σ(k+1)) ≤ h(v)}`
  align with `h`'s sweep cuts.
- `∑_v h² ≤ ∑_v f²`; `∑_e (h_u − h_v)² ≤ ∑_e (f_u − f_v)² = λ₂ ‖f‖²`
  (Laplacian monotonicity).

The sweep argument on `h` yields

```
  ∑_k (h(σ(k+1))² − h(σ(k))²) · |T_k|
      = ‖h‖²
  ∑_k (h(σ(k+1))² − h(σ(k))²) · |∂T_k|
      ≤ √(2 λ₂ Δ) · ‖h‖²  · √(‖f‖² / ‖h‖²)
```

Hmm, the bookkeeping is delicate. Let me lay out the cleanest known
version explicitly.

---

## Clean formalizable version (Spielman-style)

**Step 1. Reduction by sign.** Replace `f` with `−f` if necessary so that
`|{v : f v > 0}| ≤ |{v : f v < 0}|`. Both are nonempty (since `∑ f = 0`
and `f ≠ 0`), and one has cardinality `≤ (n − |{f = 0}|) / 2 ≤ n/2`.

**Step 2. Positive truncation.** Define `h v := max (f v) 0`. Then:
- `h ≥ 0`, `supp h = {v : f v > 0}` has size `≤ n/2`.
- **Sweep cuts** `T_t := {v : h v ≥ t}` for `t > 0` are subsets of `supp h`,
  hence `|T_t| ≤ n/2`.
- `‖h‖² ≤ ‖f‖²` (obvious, since `h v ∈ {0, f v}`).
- `∑_e (h_u − h_v)² ≤ ∑_e (f_u − f_v)²` (1-Lipschitz property of `max(·, 0)`).

**Step 3. Cauchy–Schwarz (`h²` sweep).** On the non-negative function `h`,
define level thresholds `0 = t_0 < t_1 < … < t_r = max h` = distinct values
of `h` sorted ascending. Using the identity `x² = ∫_0^x 2t dt` (or the
discrete sum version),

```
  ∑_v h v² = 2 ∫_0^∞ t · |T_t| dt = ∑_j (t_{j+1}² − t_j²) · |T_{t_{j+1}}|
```

And by `|a² − b²| = |a − b| · |a + b|` and Cauchy–Schwarz:

```
  ∑_e |h_u² − h_v²| = ∑_e |h_u − h_v| · (h_u + h_v)    [since h ≥ 0]
       ≤ √(∑_e (h_u − h_v)²) · √(∑_e (h_u + h_v)²)
       ≤ √(λ₂ · ‖f‖²) · √(2 Δ · ‖h‖²)            [eigenvalue + degree bound]
       ≤ √(2 λ₂ Δ) · ‖f‖ · ‖h‖
       ≤ √(2 λ₂ Δ) · ‖h‖² · (‖f‖ / ‖h‖)
```

Hmm, the `‖f‖ / ‖h‖` factor is NOT 1 in general. This is the persistent
gap; the Alon–Milman trick resolves this by the refined "doubling" of `h`
with both `f₊` and `f₋`.

### The doubling trick (final polish)

Let `h₊ v := max (f v) 0`, `h₋ v := max (−f v) 0` = `max (0, −f v)`. Both
non-negative with disjoint support; `h₊ − h₋ = f`. Then:

- `‖h₊‖² + ‖h₋‖² = ‖f‖²`.
- `∑_e (h₊_u − h₊_v)² + ∑_e (h₋_u − h₋_v)² ≤ ∑_e (f_u − f_v)²` (pointwise
  identity: `(a − b)² = (a₊ − b₊)² + (a₋ − b₋)² + 2 · (a₊ · b₋ + b₊ · a₋)`,
  with the cross term non-negative).

Applying the `h²`-sweep argument to **both** `h₊` and `h₋`:

- There is a sweep cut `S` for `h₊` with `|∂S|/|S| ≤ √(2 λ₂ Δ · ‖f‖² / ‖h₊‖²)`
  (I'll re-derive this below), and `|S| ≤ |{f > 0}| ≤ n/2` if `h₊` is the
  "small" side.
- Similarly for `h₋`.

More carefully: the `h²`-sweep Cauchy–Schwarz gives

```
  ∑_e |h²_u − h²_v|  ≤  √(∑_e (h_u − h_v)²) · √(∑_e (h_u + h_v)²)
                     ≤  √(∑_e (h_u − h_v)² · 2Δ · ‖h‖²)
                     [ since (a+b)² ≤ 2(a² + b²) and ∑_v h² times 2Δ ]
```

Now combine **both** `h₊` and `h₋`:

```
  ∑_e (|h₊_u² − h₊_v²| + |h₋_u² − h₋_v²|)
      ≤ √(∑_e ((h₊_u − h₊_v)² + (h₋_u − h₋_v)²)) · √(2Δ · (‖h₊‖² + ‖h₋‖²))
      ≤ √(λ₂ · ‖f‖²) · √(2Δ · ‖f‖²)
      =  √(2 λ₂ Δ) · ‖f‖²
```

On the LHS, use discrete coarea for `h₊²` and `h₋²`:

```
  ∑_e |h₊_u² − h₊_v²| = ∑_k gap₊_k · |∂S₊_k|
  ∑_e |h₋_u² − h₋_v²| = ∑_k gap₋_k · |∂S₋_k|
```

where `S₊_k`, `S₋_k` are sweep cuts of `h₊` (resp. `h₋`), all of size
`≤ n/2`. And `‖h₊‖² + ‖h₋‖² = ‖f‖² = ∑_k (gap₊_k · |S₊_k| + gap₋_k · |S₋_k|)`.

Hence

```
  ∑_k gap₊_k · |∂S₊_k| + ∑_k gap₋_k · |∂S₋_k|
      ≤ √(2 λ₂ Δ) · (∑_k gap₊_k · |S₊_k| + ∑_k gap₋_k · |S₋_k|).
```

Pigeonhole: some threshold `t = t_k` in one of the two sweeps satisfies
`|∂T_t| / |T_t| ≤ √(2 λ₂ Δ)`. The corresponding set `T_t` is one of
`S₊_k` or `S₋_k`, both of size `≤ n/2`.

---

## How this maps back to the Lean statement

The Lean statement uses `S_k := {w : f w ≥ f(σ(k+1))}`, **not** `h₊`/`h₋`-sweeps.
So the sign-flip + truncation trick must be compiled back to a sweep of the
original `f`. Two cases:

### Case A — `|{w : f w > 0}| ≤ n/2`

Then there exists `k` with `f(σ(k)) ≤ 0 < f(σ(k+1))`: take the smallest `k`
with `f(σ(k+1)) > 0`. For any `k' ≥ k`, `S_{k'} ⊆ {w : f w > 0}` so
`|S_{k'}| ≤ n/2`. The sweep on `h₊` uses exactly these upper `S_{k'}` as
its threshold cuts. Thus the pigeonhole yields `k* ≥ k`, matching the
Lean statement (with `S_{k*}` having `|S_{k*}| ≤ n/2`).

### Case B — `|{w : f w < 0}| ≤ n/2`

Symmetric: there exists `k` with `f(σ(k)) < 0 ≤ f(σ(k+1))`. For `k' < k`,
`Sᶜ_{k'} ⊆ {w : f w < 0}` so `|Sᶜ_{k'}| ≤ n/2`. But the Lean statement
wants `|S_{k'}| ≤ n/2`, so we must use `Sᶜ_{k'}` as the witness instead.
This requires either:

- (Option B1) Restating `sweep_pigeonhole` to allow `Sᶜ` as witness, by
  returning `S_{k*}ᶜ` when the lower half is the small side — but this
  changes the statement.
- (Option B2) Showing we can always reduce to Case A by flipping the sign
  of `f`. However, flipping `f` to `−f` reverses the sort order, so the
  sorting permutation `σ` becomes `σ ∘ rev`, and `S_k` on `−f` corresponds
  to `Sᶜ_{n−2−k}` on `f`. This is a valid but fiddly reduction.

### Recommended approach: reduce to Case A internally

Inside the `sorry`, perform:

```
obtain hcase | hcase : |{w : f w > 0}| ≤ n / 2 ∨ |{w : f w < 0}| ≤ n / 2 := by
  -- Pigeonhole on ∑ f = 0 and f ≠ 0:
  -- At least one of {f > 0}, {f < 0} is nonempty. If both have size > n/2
  -- their union (disjoint) exceeds n — impossible.
  sorry

-- In Case A, directly apply the sweep pigeonhole on f₊.
-- In Case B, apply the argument to −f (with sorting reversed), then
-- translate the resulting witness k' on −f to k := n − 2 − k' on f.
```

---

## Suggested Lean-level decomposition

**The prover should introduce the following helper lemmas (either above
`sweep_pigeonhole` in the same file, or as `have` blocks inside it):**

### Helper 1 — positive-support pigeonhole
```
lemma pos_or_neg_small (f : V → ℝ) (hfsum : ∑ v, f v = 0) (hf : f ≠ 0) :
    (Finset.univ.filter (fun w => 0 < f w)).card ≤ Fintype.card V / 2 ∨
    (Finset.univ.filter (fun w => f w < 0)).card ≤ Fintype.card V / 2
```
Proof: if both exceed `n/2`, their disjoint union exceeds `n`. A contradiction.

### Helper 2 — Laplacian positive-part monotonicity (the 1-Lipschitz step)
```
lemma edge_sum_pos_part_le (f : V → ℝ) :
    ∑ e ∈ G.edgeFinset,
      Sym2.lift ⟨fun u v => (max (f u) 0 − max (f v) 0)^2, _⟩ e ≤
    ∑ e ∈ G.edgeFinset,
      Sym2.lift ⟨fun u v => (f u − f v)^2, _⟩ e
```
Proof: pointwise `(max a 0 − max b 0)² ≤ (a − b)²`, done by splitting on
signs of `a`, `b`.

### Helper 3 — doubling edge bound
```
lemma edge_sum_pos_neg_add_le (f : V → ℝ) :
    (∑ e ∈ G.edgeFinset,
        Sym2.lift ⟨fun u v => (max (f u) 0 − max (f v) 0)^2, _⟩ e) +
    (∑ e ∈ G.edgeFinset,
        Sym2.lift ⟨fun u v => (max (− f u) 0 − max (− f v) 0)^2, _⟩ e) ≤
    ∑ e ∈ G.edgeFinset,
      Sym2.lift ⟨fun u v => (f u − f v)^2, _⟩ e
```
Proof: pointwise `(a₊ − b₊)² + (a₋ − b₋)² ≤ (a − b)²`; split on signs.

### Helper 4 — `h²` Cauchy–Schwarz on edges
```
lemma edge_sqdiff_cauchy_schwarz (h : V → ℝ) (hnn : ∀ v, 0 ≤ h v) :
    (∑ e ∈ G.edgeFinset,
        Sym2.lift ⟨fun u v => |h u ^ 2 − h v ^ 2|, _⟩ e) ^ 2 ≤
    (∑ e ∈ G.edgeFinset,
        Sym2.lift ⟨fun u v => (h u − h v) ^ 2, _⟩ e) *
    (∑ e ∈ G.edgeFinset,
        Sym2.lift ⟨fun u v => (h u + h v) ^ 2, _⟩ e)
```
Proof: factor `|a² − b²| = |a − b|(a + b)` (uses `a, b ≥ 0`), then
standard Cauchy–Schwarz (`Finset.inner_mul_le_norm_mul_norm` or
`sq_sum_le_card_mul_sum_sq`-style).

### Helper 5 — coarea for `h²` on non-negative `h`
Apply `discrete_coarea` to `h²` directly (valid because `σ_h²` — the
sort permutation for `h²` — coincides with `σ_h` when `h ≥ 0`).

### Main pigeonhole

```
-- Split into cases: f₊ or f₋ has support ≤ n/2.
-- Case A (the f₊ case):
--   Let h := fun v => max (f v) 0, let σ_h be the sort permutation for h
--   (same σ as for f since the ordering of h is the same as f on supp h
--    and h = 0 elsewhere).
--   Apply coarea to h², Cauchy–Schwarz, eigenvalue, Helper 3 + Helper 4.
--   Pigeonhole yields k with |∂T_k|/|T_k| ≤ √(2λ₂Δ), with T_k ⊆ supp h,
--   hence |T_k| ≤ n/2.
--   T_k corresponds to some S_{k'} in the original f-sweep; extract k'.
-- Case B (f₋): reduce to Case A by substituting −f (and verifying the
--   Fiedler-vector hypotheses are preserved under negation).
```

---

## Fallback if the full proof is too large for one cycle

If the prover cannot complete this in a single round, the plan agent
should decompose further by splitting off Helpers 1–5 as individual
lemmas *above* `sweep_pigeonhole` in the file. Each helper is a
self-contained ≤40-line proof in Mathlib style.

## Citations

- Alon & Milman, "λ₁, isoperimetric inequalities for graphs, and
  superconcentrators" (1985) — original proof.
- Chung, *Spectral Graph Theory* (1997), Ch. 2 (discrete Cheeger).
- Spielman, "Spectral and Algebraic Graph Theory" lecture notes — clean
  modern presentation.
