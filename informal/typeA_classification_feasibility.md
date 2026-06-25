# Can the TYPE A classification be formalized to close `typeA_slack_ge_required`?

**Verdict: NO.** The structural assumptions of the Dirichlet bridge
(`partition`, `hpp`, `hcross`, `hcore`, `hscalar`) **cannot** be derived from
`hTconn + heig + hReq`. The binding reason is that `hscalar` is *logically equivalent
to the goal itself*, so "deriving the classification" is just "proving the theorem" by
another name — no reduction has occurred, and the genuine content (Fiedler flatness on
the core) requires spectral infrastructure absent from Mathlib. There is also a
statement-level defect: the theorem as written is **false without `‖f‖ = 1`**.

Probes: `typeA_classification_probe.py` (P1, P2), `/tmp/band.py` (TASK 3 band).

---

## TASK 1 — the upstream code constructs no partition

The proof chain feeding the sorry is purely *regime dispatch*; it never mentions
ports, cores, or a partition:

```
triEnergy_le_RHS_exists (1086)        -- has hf₀norm: ∑f₀²=1, hf₀perp: ∑f₀=0, hf₀eig
  └ gapEnergy_nonneg (1060)           -- by_cases on sign of `required`
      ├ regime i  (required ≤ 0): regime_i_from_aggregate         (sorry-free)
      └ regime ii (required > 0): typeA_extremality_gap_nonneg (1048)
            └ typeA_slack_ge_required (1039)   ← THE SORRY
```

`typeA_extremality_gap_nonneg` is a one-liner: it rewrites
`gapEnergy = aggregateSlack − required` (`gap_eq_aggregateSlack_sub_required`) and calls
`typeA_slack_ge_required`. **No partition is built anywhere in this chain, and no
ports/core are identified.** The port/core split appears *only* inside the two
**conditional** bridges (`Helpers/BlockResolventBridge.lean`,
`Helpers/DirichletPartition.lean`), where it is an *input parameter*, never a construction.

A latent point surfaces here: `triEnergy_le_RHS_exists` **has** `hf₀norm : ∑ f₀² = 1` and
`hf₀perp : ∑ f₀ = 0`, but `gapEnergy_nonneg → typeA_extremality_gap_nonneg →
typeA_slack_ge_required` **drop both**. So the standalone `typeA_slack_ge_required` is
stated strictly more generally than it is ever used (see Blocker 0).

## TASK 2 — there is no port/core machinery in Lean

`grep -rn "isPort|portSet|coreSet|partition"` over `Topostability/` finds:

* `Helpers/DirichletPartition.lean` — `isPort : V → Prop` is a **free variable**; the
  three classes `cross/core/pp` are lambdas in `isPort`; `hcross/hcore/hpp/hpartition/hscalar`
  are **hypotheses** of `typeA_slack_ge_required_of_dirichlet`, never derived.
* `Helpers/BlockResolventBridge.lean` — same shape, with the resolvent bound as hypothesis.

There is **no** `def` of a port set, core set, or degree threshold anywhere in Lean. The
actual construction — the degree-gap split

```python
def split_ports(d):              # verify_block_resolvent.py
    order = argsort(d); gaps = [(d[order][i+1]-d[order][i], i) for i in range(n-1)]
    gap, idx = max(gaps)
    return set(order[:idx+1]) if (gap >= 2 and idx < n-1) else set()
```

lives **only in Python** and was used solely to *check* the bridge hypotheses numerically
on the 17-graph corpus. None of it is formalized.

## TASK 3 — what `hReq` actually gives (and what it does not)

With `λ = λ₂ > 0` (forced by `hTconn`: `T(G)` connected ⇒ `G` connected, `≥2` vertices),

```
required > 0  ⟺  λ + S²/mE − degQuad > 0  ⟺  degQuad < λ + S²/mE        (S = degLin)
```

Take the natural unit normalization `‖f‖ = 1` (which the caller supplies). Then
`degQuad = Σ_v d_v f_v²` is the `f²`-weighted mean degree, and two elementary facts pin it:

* `degQuad ≥ δ_min` (every `d_v ≥ δ_min`, `Σ f_v² = 1`);
* `λ₂ ≤ δ_min` (Fiedler: `a(G) ≤ κ(G) ≤ δ(G)`).

Substituting `λ ≤ δ_min` into `degQuad < λ + S²/mE` gives

```
Σ_v (d_v − δ_min) · f_v²  <  S²/mE.
```

So **`required > 0` says the `f²`-mass concentrates toward low-degree vertices** — the
"excess degree" carried by `f²` is bounded by `S²/mE`. Verified on the deg2d TYPE A graph
(`/tmp/band.py`): `λ₂ = 1.97 ≤ δ_min = 2`, excess `= 0.62 < S²/mE = 0.98`.

**But this is a *soft, weighted* concentration, not a partition.** It does **not** deliver:

1. **a sharp degree threshold / a degree gap ≥ 2** — the concentration is continuous; a
   smooth degree distribution can satisfy it with no gap, so `split_ports` returns `∅`;
2. **a triangle-free port set (`hpp`, `t_pp = 0`)** — a statement about the *induced
   subgraph on low-degree vertices*, invisible to the degree-weighted scalar `degQuad`;
3. **core flatness (`hscalar`)** — a statement about how the edge Dirichlet energy is
   *distributed*, which `degQuad` (a single weighted sum) cannot see.

The gap between "soft concentration of `f²`" and "hard partition + `hpp` + `hscalar`" is
exactly the unformalized content.

## TASK 4 — feasibility: NOT derivable

### Blocker 1 (binding): `hscalar` *is* the goal, repackaged

`slack_ge_required_of_triEnergy_le_RHS` rests on the algebraic identity

```
required = aggregateSlack − (RHS − triEnergy),     RHS := 2λ(2·degQuad − λ − S²/mE)
```

hence **`required ≤ aggregateSlack  ⟺  triEnergy ≤ RHS`** — an exact equivalence, not a
one-way bound. The Dirichlet bridge then proves `triEnergy ≤ RHS` from

```
hscalar :  (δ−1)·D_cross + maxt_core·D_core  ≤  RHS         (D_core via the partition identity)
```

which is **at least as strong as `triEnergy ≤ RHS`** (it is `triEnergy ≤ bound ≤ RHS`).
Therefore *deriving `hscalar` from `hReq` is exactly proving the theorem from `hReq`*. The
bridges **reformulate** the sorry into an elementary scalar inequality; they do not
**reduce** it. The real content of `hscalar` is `D_core` small, i.e. the **Fiedler is flat
on the dense core** — a spectral fact (block resolvent / Davis–Kahan eigenvector
localization). `hReq` is a *single coarse scalar inequality* (`degQuad < λ + S²/mE`) and is
strictly weaker; it provably does **not** entail the fine energy-distribution statement
`hscalar`. This is the same gap the resolvent bridge isolated, restated.

### Blocker 2: `hpp` (`t_pp = 0`) is a graph-structural fact, not implied

`hpp` asserts the *induced subgraph on the ports is triangle-free*. Nothing in
`hTconn + heig + hReq` controls the induced subgraph on low-degree vertices. It held on the
17-graph corpus only because those families are engineered with triangle-free port sets
(deg2d: a single degree-2 vertex ⇒ no port-port edges at all; twin: the two apexes are
non-adjacent, joined only through a common shared node with no triangle).

A noteworthy *tension* (probe P2, `typeA_classification_probe.py`): trying to force
`t_pp > 0` (give the ports a triangle) requires the ports to be *weakly attached* for the
Fiedler to localize enough that `required > 0`; but weak attachment makes the port edges lie
in too few triangles, **disconnecting `T(G)`** and so violating `hTconn` (search found
`required > 0 ∧ t_pp > 0 ∧ T(G) connected`: 0 hits in our families). This is only a
*tendency*, not a theorem — but it shows that even *stating* the conditions under which
`hpp` would hold is itself an open structural problem, with no proof in sight. Either way
`hpp` is **not** a consequence of the given hypotheses.

### Blocker 3: the port construction itself

The degree-gap `split_ports` needs a gap `≥ 2`. `hReq` does not guarantee one (Blocker 3a),
and for *regular* regime-ii eigenvectors the ports are empty — there the bridge degenerates
to the all-core case and `hscalar` becomes `λ ≤ d+1` (provable, the interlacing bound), but
that is the *regular* sub-case already handled by `triEnergy_le_RHS_regular`, not the TYPE A
content. So no single uniform construction covers all regime-ii instances.

### Non-blockers

`hcross`, `hcore` are **not** obstructions: once a port set is fixed, they hold by *defining*
`Cp := max` over cross edges and `Cc := max` over core edges of the triangle count. They are
mechanically true; their only role is to feed those constants into `hscalar`.

### Blocker 0 (statement defect): the bare theorem is false without `‖f‖ = 1`

`required(f) = 2λ(λ + S²/mE − degQuad)` is **not homogeneous** in `f`: `λ` is the fixed
eigenvalue while `S²/mE, degQuad` scale as `‖f‖²`. For `f = t·f₀`,

```
required(t·f₀)      = 2λ²(1 − t²) + t²·required(f₀)   → 2λ² > 0   as t → 0
aggregateSlack(t·f₀) = t²·aggregateSlack(f₀)           → 0         as t → 0
```

so `required > 0` holds while `required ≤ aggregateSlack` **fails**. Confirmed (probe P1) on
a TYPE A graph:

```
‖f‖=1.0 : required=+1.29  aggregateSlack=+3.92  holds=True
‖f‖=0.5 : required=+6.13  aggregateSlack=+0.98  holds=False   (required>0 still!)
‖f‖=0.1 : required=+7.67  aggregateSlack=+0.04  holds=False
```

So the *literal* `typeA_slack_ge_required` is false; only the unit version (`∑ f² = 1`, and
in practice `∑ f = 0`) is true and intended. The caller has both hypotheses, so this is a
cheap fix — but it must be made before any proof, and it confirms the theorem cannot be
closed "as stated".

---

## Summary table

| bridge hypothesis | derivable from `hTconn + heig + hReq`? | why |
|---|---|---|
| `hpartition` (Dirichlet identity) | **yes** | `dirichlet_partition_eq` + `Σ_E (f_i−f_j)² = 2λ` from `heig`, `‖f‖=1` |
| `hcross`, `hcore` | **yes (trivially)** | define `Cp, Cc` as per-class triangle-count maxima |
| port set `isPort` | **partially** | definable via degree gap, but a gap need not exist |
| `hpp` (`t_pp = 0`) | **no** | property of the induced low-degree subgraph; uncontrolled by the hypotheses |
| `hscalar` | **no** | equivalent to the goal `triEnergy ≤ RHS`; encodes core flatness (spectral) |
| `‖f‖ = 1` (needed for truth) | available upstream, **omitted** from the statement |

## What it would actually take

1. **Fix the statement**: thread `∑ f² = 1` (and `∑ f = 0`) from `triEnergy_le_RHS_exists`
   into `typeA_slack_ge_required`. *Trivial* (caller already has them).
2. **Prove `hscalar`** = prove core flatness `D_core ≤ budget`. This is the entire
   mathematical content and is **currently infeasible in Lean**: it needs either the
   matrix-inverse / Cauchy-interlacing route of the block resolvent (absent from Mathlib) or
   a genuinely new *elementary* flatness argument. It is **not** a finite list of routine
   lemmas — it is the same open gap the two existing bridges isolate.

The TYPE A "classification" is a *descriptor of a graph family* (deg2d, twin, …), not a
property derivable from `(hTconn, heig, hReq)`. It can package and validate the remaining
obligation (`hscalar`), but it cannot **close** `typeA_slack_ge_required`.
