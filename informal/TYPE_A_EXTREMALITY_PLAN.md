# TYPE A extremality — proof plan

Roadmap to close the last open piece of Conjecture B (TYPE A). The conjecture reduces to a single
sharp scalar inequality with a **known extremizer and value**; this document lays out the proof
strategy (TASK 0), the four monotonicities (TASKS 1–4), the scalar reduction and extension (TASK 5),
and the Lean route.

## Target theorem

> **TYPE A (`λ₂(G) < λ₂(H) =: γ`):** `gap ≥ (1/3)·eff_resist`, equivalently `gap/eff ≥ 1/3`,
> with asymptotic equality for the `d=2` twin-port model on bulk `K_N` (`N → ∞`).

Here `gap = λ₂G − B2′` and `eff_resist = R_aa+R_bb−2R_ab = (e_a−e_b)ᵀ(L_H−λ)^{-1}(e_a−e_b) > 0`
(Green's-function sum rule). Since `eff > 0`, `gap/eff ≥ 1/3 ⟹ gap > 0 ⟹ Conjecture B on TYPE A`.

## Extremizer — PROVED (`conjecture_B_typeA_twin_port_proof.md`)

Bulk `K_N`; twin ports `a,b` each adjacent to the same `{0,1}` (`a≁b`); `v₀ ~ {a,b}`. Via the 4-class
equitable quotient (`{v₀}, {a,b}, {0,1}, rest`):

| quantity | `N → ∞` limit | how |
|---|---|---|
| `λ₂` | **1** | secular `(λ−1)(λ−4)=0`; `λ₂(N)=1+4/(3N)` |
| Fiedler `(x,p,c,r)` | `(2,1,−2/N,−4/N)/√6` | quotient eigenvector |
| `eff` | **2** | antisymmetric resolvent `φ=(e_a−e_b)/(2−λ)`, `eff=2/(2−λ)` |
| `T`, `B2′`, `Σh²`, `S²/m`, `λ₂G` | `2, 3, 9, 16/3, 11/3` | edge-class sums (sympy-verified) |
| `gap` | **2/3** (`=4p²`) | `λ₂G − B2′ = 11/3 − 3` |
| **`gap/eff`** | **1/3** | — |

All limits exact rationals; quotient `gap` = direct `gap` to machine precision.

## Parameters of the complete-bulk model

A complete-bulk port model is `(d, s, a~b)`: port degree `d`, overlap `s = |N(a)∩N(b)|`, optional
edge `a~b`; plus the bulk density `ρ_bulk` (`= 1` for `K_N`). `g(d,s,a~b,ρ_bulk) := lim_{N→∞} gap/eff`.
Verified values (`ρ_bulk = 1`, `a≁b`): `g(2,0)=0.68, g(2,1)=0.52, g(2,2)=1/3`; `g(3,3)=0.66`;
`g(d,0)`: `0.19(d=1, TYPE B), 0.68, 1.22, 1.64, …→10`.

## The four monotonicities (TASKS 1–4)

Each is **verified numerically, none proved**. Proof strategy: each reduces to a **closed-form
quotient computation** of `g(·)` (the same equitable-partition method that gave `g(2,2)=1/3`), then a
sign-of-derivative argument.

### TASK 1 — `g(d)` increasing in `d` (`d=2` is the min)

- **Evidence:** `g(d,d)` (full overlap): `1/3, 0.66, 0.93, 1.14, …` increasing; `g(d,0)` likewise.
- **Strategy:** compute the 4-class quotient for the `d`-twin model (classes `{v₀},{a,b},{d ports},
  {rest N−d}`) to get a closed form `g(d)` (rational in `d`), then show `g(d+1) > g(d)` (monotone in
  the integer `d ≥ 2`). The `d=2` case (`= 1/3`) is the base.
- **Difficulty:** low — direct generalization of the proved `d=2` quotient.

### TASK 2 — `g(s)` decreasing to `s=d` (twins = min)

- **Evidence:** `d=2`: `g(2,0)=0.68 > g(2,1)=0.52 > g(2,2)=1/3`.
- **Strategy:** 5-/6-class quotient with classes `{v₀},{a,b}, common(s), a-only/b-only(d−s), rest`;
  closed form `g(d,s)`, show `∂g/∂s < 0`, minimum at `s = d` (twins).
- **Difficulty:** medium — more classes; the overlap moves mass between `common` and `single` ports.

### TASK 3 — adding `a~b` increases `g`

- **Evidence:** `g(2,0,a≁b)=0.68 → g(2,0,a~b)=2.06`.
- **Strategy:** the `a~b` edge shrinks `eff` (direct `a–b` path lowers resistance) while changing `gap`
  modestly; compare the two quotients (one extra edge in class `{a,b}`). Show the net `gap/eff` rises.
- **Difficulty:** low — a single-edge comparison in the quotient.

### TASK 4 — `g(ρ_bulk)` minimized at complete bulk

- **Evidence:** bulk-edge addition lowers `gap/eff` toward the complete-bulk limit (monotonicity
  study: bulk-bulk edge addition lowers `gap`; complete is the bulk-minimizer).
- **Strategy:** show `gap/eff` is monotone non-increasing under bulk-bulk edge addition (the *interior*
  edges, away from the ports). This is the **resolvent-rigidity** direction: a denser bulk is more
  rigid, lowering the port resolvent response. Likely via a perturbation/interlacing argument on
  `(L_H−λ)^{-1}` restricted to the bulk.
- **Difficulty:** **high** — this is the genuine analytic step; the others are quotient algebra.

## TASK 5 — scalar reduction and extension

**Scalar reduction (complete-bulk models).** If TASKS 1–4 hold:
`min over (d,s,a~b)` of `g` is at `d=2, s=2, a≁b` (by 1–3) `= 1/3`; and complete bulk minimizes over
`ρ_bulk` (by 4). Hence **`gap/eff ≥ 1/3` for every complete-bulk port model**, with equality at the
twin-port extremizer.

**Extension to general TYPE A cores (rigidity).** A general dense core `H` is not a bulk+ports graph.
Reduce as follows:
1. Identify the two lowest-degree TYPE A "ports" `a,b` (`min(d_a,d_b)` controls `gap/eff`, `r=+0.77`).
2. **Complete the bulk** `H ∖ {a,b}` to `K_{N}`: by TASK 4 (rigidity / bulk-edge monotonicity) this
   only *lowers* `gap/eff`.
3. **Adjust the ports** to the minimizing `(d=2, s=2, a≁b)` config: by TASKS 1–3 this only *lowers*
   `gap/eff`.
4. The result is the twin-port extremizer with `gap/eff = 1/3`. Hence the original `H` has
   `gap/eff ≥ 1/3`.

The validity of steps 2–3 as *one-directional* moves (each only lowers `gap/eff`, staying in TYPE A) is
exactly TASKS 1–4 in *local-move* form. **The hard content is TASK 4 (bulk rigidity) extended to
arbitrary edge additions**; TASKS 1–3 are quotient algebra on the model and provide the port-side
moves.

## Lean route

- The per-config quotient `gap` is an **exact equitable-partition reduction** (formalizable: quotient
  eigenpair ⇒ full eigenpair).
- The extremizer invariants `λ=1, eff=2, gap=2/3, gap/eff=1/3` are **exact rationals** but only in the
  `N→∞` limit (finite-`N` is cubic-irrational), so a Lean theorem targets the asymptotic limit — a
  real-analysis + construction task, heavier than the per-graph identities already formalised.
- **Pragmatic Lean target:** the structural inequality `gap ≥ (1/3)·eff` once proved on paper, stated
  with `eff > 0` from the already-available `poincare_on_block`/Courant–Fischer machinery. The
  monotonicities (TASKS 1–4) are the paper-proof prerequisites.

## Status summary

| step | statement | status |
|---|---|---|
| extremizer | `d=2` twins: `λ=1, eff=2, gap=2/3, gap/eff=1/3` | **PROVED** (quotient + sympy) |
| TASK 1 | `g(d)` ↑ in `d` | verified; proof = quotient algebra (low) |
| TASK 2 | `g(s)` ↓ to `s=d` | verified; proof = quotient algebra (medium) |
| TASK 3 | `a~b` raises `g` | verified; proof = single-edge quotient (low) |
| TASK 4 | complete bulk minimizes `g` | verified; proof = **bulk rigidity (high)** |
| TASK 5 | reduction + extension ⇒ `gap/eff ≥ 1/3` | conditional on 1–4 + rigidity |

## Risks / open issues

- **Global vs family extremality.** TASKS 1–4 establish the minimum *within the complete-bulk port
  family*. The extension (TASK 5) to *all* TYPE A graphs rests on the rigidity/monotonicity of TASK 4
  generalised to arbitrary edge additions — the one step without a clean quotient.
- **One-directional moves staying in TYPE A.** Each reduction move (complete bulk, set `d=2,s=2`) must
  preserve `λ₂(G) < γ`. Near the boundary this needs care (though the boundary is benign,
  `conjecture_B_typeA_boundary.md`).
- **`gap → 2/3` is a limit.** The clean value holds as `N→∞`; the inequality `gap/eff ≥ 1/3` is the
  target for all `N` (finite-`N` values are `> 1/3`, approaching from above — favourable).

## Next steps

Proceed TASK 1 → TASK 2 → TASK 3 (quotient computations, low/medium difficulty, likely closed forms),
then TASK 4 (the rigidity core), then assemble TASK 5. Each TASK `k` delivers a closed-form `g(·)` and
a monotonicity proof; TASK 4 delivers the bulk-rigidity lemma that also powers the general-core
extension.
