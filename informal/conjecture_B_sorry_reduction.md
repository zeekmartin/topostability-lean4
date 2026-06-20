# Conjecture B — sorry reduction of `conjectureB_regime_two` (TYPE A pinpointed)

Refactor of the regime-(ii) sorry so the open content is the *precise* TYPE A inequality, with the
`T ≤ B2′` step now formalised. Lean: `ConjectureB.lean` (build 2688 OK, 3 sorrys).

## TASK 1 — what the regime-(ii) sorry actually needs

`conjectureB_regime_two` (`Required > 0`):
`triEnergy G f ≤ 2λ(2·fᵀDf − λ − S²/mE)`. The RHS is `2·λ₂G` (`λ₂G = λ(Σh² − S²/m)`,
`Σh² = 2fᵀDf − λ`). Since `T ≤ B2′` (per-edge `t_e ≤ min(d_a,d_b)−1`) and `B2′ ≤ λ₂G` is `gap ≥ 0`,
the conclusion is exactly the chain

> **`T ≤ B2′ ≤ RHS`**, with `B2′ = Σ_{i,j}[i∼j](min(d_i,d_j)−1)(f_i−f_j)²`.

The first `≤` is combinatorial and now **proved** (`triEnergy_le_B2prime`, sorry-free). The second `≤`
is `gap = λ₂G − B2′ ≥ 0` — the genuine open content.

## TASK 2 — the exact Lean statement that closes TYPE A

The refactor isolates the open content into one lemma:

```lean
lemma B2prime_le_RHS (f : V → ℝ) (lam mE : ℝ) (hmE : 0 < mE) (hlam : 0 < lam)
    (heig : (G.lapMatrix ℝ).mulVec f = lam • f)
    (hReq : degQuad G f < lam + (degLin G f) ^ 2 / mE) :
    (∑ i, ∑ j, if G.Adj i j then ((min (G.degree i) (G.degree j) - 1 : ℕ) : ℝ) * (f i - f j)^2 else 0)
      ≤ 2 * lam * (2 * degQuad G f - lam - (degLin G f) ^ 2 / mE) := sorry
```

This **is** `gap ≥ 0` (`B2′ ≤ λ₂G`). What it would take to discharge it:

- **TYPE B:** already closed structurally — `conjectureB_regime_two_typeB` (sorry-free) proves the same
  conclusion from the block lemmas (`typeB_triEnergy_bound` ← `triEnergy_le_block_dirichlet` +
  `poincare_on_block`) plus a closing inequality. So for path-bottleneck graphs `B2prime_le_RHS`
  follows.
- **TYPE A:** the extremality program (`CONJECTURE_B_STATUS.md` §10) gives `gap/eff ≥ 1/3` with
  `eff > 0` (Green's-function sum rule). To connect this to `B2prime_le_RHS` in Lean would require:
  1. the abstract objects `gap`, `eff` as Lean terms (`eff` needs the induced-core resolvent
     `(L_H − λ)^{-1}` — induced-subgraph spectral infrastructure not yet in the dev);
  2. `eff > 0` (formalisable: `eigenpair`/Courant–Fischer, the Green's-function sum rule);
  3. `gap = eff · (gap/eff) ≥ eff/3 ≥ 0` — needs `gap/eff ≥ 1/3` (the extremality bound, paper-proved
     up to the rigour items in §10) and `gap = λ₂G − B2′` identified with the Lean expressions.

So the precise smaller sorrys for TYPE A would be: `eff_pos` (provable), `gap_eq` (an algebraic
identity linking `gap` to the Lean `B2′`/`RHS`), and `gap_ge_eff_div_three` (the extremality bound,
the genuine open inequality). The current single `B2prime_le_RHS` sorry packages all three.

## TASK 3 — the refactor (done)

`conjectureB_regime_two` is now **sorry-free**, proved by chaining:

```lean
lemma conjectureB_regime_two ... :=
  le_trans (triEnergy_le_B2prime G f) (B2prime_le_RHS G f lam mE hmE hlam heig hReq)
```

with:
- **`triEnergy_le_B2prime`** — *new, sorry-free*: `T ≤ B2′` (sum of `triCount_le_min_degree_sub_one`).
- **`B2prime_le_RHS`** — the *single remaining* regime-(ii) sorry, = `gap ≥ 0` (`B2′ ≤ RHS`), the TYPE A
  obstruction.
- **`conjectureB_regime_two_typeB`** — *sorry-free* (pre-existing): closes the same conclusion for the
  TYPE B branch from the block lemmas + closing hypothesis.

### Sorry ledger (build 2688 OK)

| sorry | statement | status |
|---|---|---|
| `aggregate_triangle_poincare` (641) | `T ≤ 2λfᵀDf` | Regime 1 irregular (regular proved) |
| **`B2prime_le_RHS` (761)** | `B2′ ≤ RHS` (= `gap ≥ 0`) | **TYPE A** (TYPE B closed via `_typeB`) — *precise, replaces the old monolithic regime-two sorry* |
| `conjectureB` (805) | `λ₂(T(G)) ≤ λ₂(G)` | projected-Fiedler lift reduction |

Still **exactly 3 sorrys**, but the regime-(ii) one is now the **precise** `B2′ ≤ RHS` (gap ≥ 0) with
`T ≤ B2′` proved separately, and `conjectureB_regime_two` itself is sorry-free.

## Conclusion

- **`T ≤ B2′` formalised** (`triEnergy_le_B2prime`, sorry-free) — the combinatorial half of regime (ii).
- **The open content is pinned** to `B2prime_le_RHS` (= `gap ≥ 0`), the exact TYPE A inequality; TYPE B
  is closed (`conjectureB_regime_two_typeB`).
- **`conjectureB_regime_two` is now sorry-free** (delegates to the two). The remaining sorry is smaller
  and precise: it is exactly the triangle-free degree inequality `B2′ ≤ λ₂G`, whose TYPE A case is the
  extremality bound `gap/eff ≥ 1/3`.

Net: the regime-(ii) obstruction is now a single, sharply-stated Lean lemma (`B2prime_le_RHS`), with
its TYPE B sub-case discharged and its TYPE A sub-case mapped to the extremality program.

## Lean
New sorry-free: `triEnergy_le_B2prime`. New precise sorry: `B2prime_le_RHS`. `conjectureB_regime_two`
now sorry-free (`le_trans`). 34 sorry-free conjecture-B theorems (28 `ConjectureB` + 6 `Paper16`); 3
sorrys total.
