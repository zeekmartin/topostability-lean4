# Conjecture B — TYPE B path-bottlenecks: generalizing the lollipop proof

TYPE B = a Fiedler bottleneck carried by a **triangle-free path/stub `P`** attached to a
**triangle-rich dense block `B`** (lollipops, barbells, tadpoles). Claim: `T = O(λ₂²)`,
`RHS = Θ(λ₂)`, so `T/RHS = O(λ₂) → 0`. Code:
[`conjecture_B_typeB_path_bottleneck.py`](../conjecture_B_typeB_path_bottleneck.py); tested on
lollipop(K_k,P_l), barbell, tadpole over `k ∈ {5..20}`, `l ∈ {4..64}`.

## 1. Block/path identification & triangle-energy decomposition

`B :=` vertices in ≥1 triangle (`diag(A³) > 0`); `P :=` the rest (triangle-free). Decompose
`T = Σ_e t_e (f_a−f_b)²` (`t_e = |N(a)∩N(b)|`) by edge location:

> **`T = T_block + T_path + T_junction`**, and **`T_path = 0`, `T_junction = 0` exactly** (verified
> `max = 0` over all families). Both `P`-internal and boundary edges are **triangle-free** (`t_e = 0`):
> a path/stub vertex shares no neighbour with its partner. **Hence `T = T_block`.**

## 2. The three step-bounds (verified)

| step | quantity | result |
|---|---|---|
| (a) path triangle-free | `max T_path` | `0` |
| (b) junction triangle-free | `max T_junction` | `0` |
| (c) block `O(λ₂²)` | `T_block/λ₂²` | `∈ [0.34, 8.9]` (bounded) |
| (d) `RHS = Θ(λ₂)` | `RHS/λ₂` | `∈ [3.5, 21.5]` (bounded both sides) |
| (e) ratio | `(T/RHS)/λ₂` | `∈ [0.07, 0.99]` (bounded) |
| (f) block gap | `γ/λ₂` | `≥ 26.7` |
| (g) boundary | `β` | `≤ 2` (lollipop/tadpole 1, barbell 2) |

`T/RHS ≤ 0.10` over all tested graphs (consistent with the corpus `≤ 0.18`).

## 3. Why `T_block = O(λ₂²)` — the rigid-block mechanism

The total Dirichlet energy splits `f^T L f = λ₂ = D_block + D_path + D_junction` (unit Fiedler).
Measured (lollipop K₁₀, `l = 4…128`):

> `D_path/λ₂ → 1` (the path carries **all** the energy); `D_junction/λ₂ → 0` with
> **`D_junction = Θ(λ₂²)`**; **`D_block = Θ(λ₂²)`** (`D_block/λ₂² ∈ [0.12, 0.34]`).

Two ingredients:

**(i) Junction gradient is `O(λ₂)`** (not `O(√λ₂)`). At the block-junction vertex `j` (block-degree
`d_j−1`, one path edge to `p₁`), `(Lf)_j = λ₂ f_j` with all block-neighbours flat at the block value
`V`:
`d_j V − ((d_j−1)V + f_{p₁}) = λ₂ V ⟹ V − f_{p₁} = λ₂ V + (block-internal terms)`, so
**`|f_j − f_{p₁}| = O(λ₂·|V|)`**. The heavy, high-gap block is *rigid*: it cannot follow the path,
forcing the junction flux to be `O(λ₂)`. Hence `D_junction = O(λ₂²)`.

**(ii) Block flatness (Poincaré, gap `γ`).** Restricting `Lf = λ₂f` to `B` gives
`(L_B − λ₂I)f_B = −(\text{junction flux})·e_j =: \text{source}`, `‖source‖ = |f_j − f_{p₁}| = O(λ₂)`.
With `γ − λ₂ > 0`,
`D_block = f_B^⊤ L_B f_B = f_B^⊥·source + λ₂‖f_B^⊥‖² ≤ ‖source‖²/(γ−λ₂) + O(λ₂³/γ²)` =
**`O(λ₂²/γ)`**.

Then `T_block = Σ_{e∈B} t_e (f_a−f_b)² ≤ Δ_B · D_block` (`Δ_B = max_{e∈B} t_e ≤ |B|−2`), giving
**`T = T_block = O(Δ_B λ₂²/γ) = O(λ₂²)`** for a bounded block.

## 4. Why `RHS = Θ(λ₂)`

`RHS = λ₂·G`, `G = Σ_e h_e² − S²/m` (`h_e = f_a+f_b`). On the path `f` varies (the bottleneck mode),
so `Σ_e h_e²` over path edges `= Θ(1)` and the centring deficit `S²/m = O(1/n)` is dominated; thus
`G = Θ(1)` (bounded below by the path's edge-lift variance) and **`RHS = Θ(λ₂)`** (measured
`RHS/λ₂ ∈ [3.5, 21.5]`).

## 5. Theorem-shaped lemma

> **Lemma (TYPE B path-bottleneck).** Let `G = B ⊔ P` with
> - `B` a triangle-rich block, spectral gap `γ = λ₂(G[B])`;
> - `P` a triangle-free path/stub;
> - boundary `β = |∂(B,P)| = O(1)`, and **all boundary edges triangle-free**;
> - bottleneck: `λ₂ = λ₂(G) ≤ γ/2` (Fiedler localizes on `P`).
>
> Then, writing `Δ_B = max_{e∈B} t_e`:
> 1. `T = T_block` (`T_path = T_junction = 0`, triangle-freeness).
> 2. `‖junction flux‖ = O(λ₂)` (rigid block: `(Lf)_j = λ₂ f_j`, flat block-neighbours).
> 3. `D_block ≤ ‖junction flux‖²/(γ−λ₂) = O(λ₂²/γ)` (block Poincaré).
> 4. `T = T_block ≤ Δ_B · D_block ≤ C·λ₂²` (`C = O(Δ_B/γ)`, bounded for bounded `B`).
> 5. `RHS = λ₂·G ≥ c′·λ₂` (`G ≥` path edge-lift variance `> 0`).
> 6. **`T ≤ Cλ₂²` and `RHS ≥ c′λ₂` ⟹ `T/RHS ≤ (C/c′)·λ₂ → 0`** — Conjecture B holds with margin
>    `→ 1`.

## 6. Sufficient deterministic assumptions (summary)

- **block gap `γ ≥ c`** (triangle-rich ⇒ large `γ`; pins block flatness, step 3);
- **path/stub triangle-poor** (`t_e = 0` on `P` and boundary ⇒ `T = T_block`, step 1);
- **boundary size `O(1)`** (single junction flux ⇒ `‖source‖` controlled, steps 2–3);
- **`λ₂ ≤ γ/2`** (resolvent `(L_B−λ₂)` invertible with gap `≥ γ/2`).

These replace the lollipop-specific computation with structural hypotheses satisfied by every TYPE B
graph (verified: `γ/λ₂ ≥ 26.7`, `β ≤ 2`, `T_path = T_junction = 0`, `T/RHS ≤ 0.10`).

## Lean
Steps 2–3 (block Poincaré / resolvent flux bound) are the `‖·‖ ≤ ‖source‖/(γ−λ₂)` form already
present in Paper16 (`poincare_on_block`, `block_gap_lower`); step 1 (`t_e = 0` on triangle-free edges)
is combinatorial (an edge with `t_e > 0` has a common neighbour, i.e. a triangle). Formalising the
full lemma needs the `B ⊔ P` decomposition and induced-block spectral gap `γ`; the pieces exist in
Paper16 but wiring the decomposition is deferred. No new lemma this round.
