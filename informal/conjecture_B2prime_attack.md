# Conjecture B — fresh attack on the sharp triangle-free target B2′

**Target.** With `f` the unit Fiedler vector of connected `G`, `d` the degree vector,
`S = Σ_v d_v f_v`, `m=|E|`, `A := fᵀDf − λ₂`:

> **(B2′)**  `W₁ := Σ_{ab∈E}(min(d_a,d_b)−1)(f_a−f_b)² ≤ λ₂·(fᵀ(D+A)f − S²/m)`  ⟹ Conjecture B.

(Reduction rigorous: projected lift `h'=Bᵀf−(S/m)1_E ⟂ 1_E` + Lean-verified
`t_{ab}≤min(d_a,d_b)−1`.) B2′ holds 9020/9020 corpus + 253 hard families, tight only
at `K_n`. Code: [`conjecture_B2prime_attack.py`](../conjecture_B2prime_attack.py).

**Headline.** Using `L_G f = λ₂ f`, B2′ expands **exactly** to a triangle-free,
min-free, **oriented degree-gradient** inequality. The triangles *and* the `min` are
both eliminated; what remains is one scalar inequality coupling the Fiedler values at
the high- and low-degree endpoints of each **degree-heterogeneous** edge. It is **not**
a sum of squares (the oriented term is negative on 81% of graphs), so the `−R″` slack
is genuinely load-bearing — but the statement is now as clean as it can be made.

---

## APPROACH 1 — algebraic expansion via the eigenvector equation (the win)

Write `min(d_a,d_b)−1 = ½(d_a+d_b) − 1 − ½|d_a−d_b|`. Then
`W₁ = LHS_sym − ½E_grad`, where
`LHS_sym = Σ((d_a+d_b)/2−1)(f_a−f_b)²` and `E_grad := Σ|d_a−d_b|(f_a−f_b)² ≥ 0`
(verified, max err 1.6e-14).

The degree-sum-weighted form reduces via `Lf=λ₂f` (verified, max err 1.4e-13):

> `Σ_{ab}(d_a+d_b)(f_a−f_b)² = 2λ₂·fᵀDf + E_disc`,  `E_disc := Σ_v f_v²·disc(v)`,
> `disc(v)=Σ_{b~v}(d_b−d_v)`.

Substituting and collecting against `RHS = λ₂(2fᵀDf−λ₂−S²/m)` gives the **exact
identity** (verified, max err **7.2e-14** over all 9020 graphs):

> **`RHS − W₁ = R″ + ½E_grad − ½E_disc`**,  where `R″ := λ₂(fᵀDf − λ₂ + 1 − S²/m)`.

So **B2′ ⟺ ½E_disc − ½E_grad ≤ R″**.

**The oriented collapse.** `E_disc` has the edge form
`E_disc = Σ_{ab}(d_b−d_a)(f_a²−f_b²)`. Orienting each edge toward its higher-degree
endpoint `h` (lower `l`), the two half-sums combine per-edge (verified, max err
**3.0e-15**):

> `½E_disc − ½E_grad = −C`,  where  **`C := Σ_{ab∈E}(d_h−d_l)·f_h·(f_h−f_l)`**.

Therefore, with **0/9020 mismatches**:

> ### B2′ ⟺ `C ≥ −R″`, i.e.
> **`Σ_{ab∈E} (d_h−d_l)·f_h·(f_h−f_l) ≥ −λ₂·(fᵀDf − λ₂ + 1 − S²/m)`**
> (`h` = higher-degree endpoint of edge `ab`).

This is the fully-reduced statement: **no triangles, no `min`, no `t_{ab}`**. Only
**degree-heterogeneous edges** (`d_h≠d_l`) contribute; degree-balanced edges vanish.
On a regular graph `C≡0` and `R″=λ₂(1−S²/m)≥0`, so B2′ is automatic — consistent with
the difficulty living entirely in degree irregularity.

**Two clean sub-facts (both verified, equality at `K_n`):**
- **`R″ ≥ 0` always** (min `≈0`), equivalently the standalone inequality
  **`fᵀDf − λ₂ + 1 ≥ S²/m`** (i.e. `A+1 ≥ S²/m`). This is a *provable-looking*
  Fiedler/degree-correlation bound in its own right and a natural first Lean lemma.
- Equality `C = −R″` (and `R″=0`) at `K_n`: there `A=−1`, `S=0`, `C=0`.

**Is `RHS − W₁` a sum of squares / manifestly nonnegative?** **No.** It equals
`R″ + ½E_grad − ½E_disc`: `E_grad ≥ 0` and `R″ ≥ 0`, but `E_disc` is signed and, in the
collapsed form, the oriented sum `C` is **negative on 81% of graphs** (corpus min
`−1.53`, hard min `−2.10`; see APPROACH 3). So no term-wise or SOS certificate exists;
`C ≥ −R″` is a genuinely *balanced* inequality where the `R″` slack is essential.

---

## APPROACH 2 — symmetric / asymmetric relaxation: FAILS (the `|Δd|` term is essential)

Relaxing `min(d_a,d_b)−1 ≤ (d_a+d_b)/2 − 1` (drop the `−½E_grad`) and testing
`LHS_sym ≤ RHS`:

| version | corpus max ratio | corpus ≤1 | hard max ratio | hard ≤1 |
|---|---|---|---|---|
| symmetric `(d_a+d_b)/2−1` | **1.698** | 7487/9020 | **6.159** | 102/253 |
| asymmetric `d_a−1` (=2·sym) | 3.395 | 0/9020 | 12.318 | 14/253 |
| **`min−1` (B2′)** | **1.0000** | **9020/9020** | 0.9872 | 253/253 |

The symmetric relaxation **fails on 1684/9273** graphs (worst 6.16 at n=35, m=402),
while `min−1` holds everywhere. Conclusion: the `½E_grad = ½Σ|d_a−d_b|(f_a−f_b)²`
correction — i.e. the **oriented degree-gradient structure** — is *not* discardable;
`min` cannot be replaced by the average. This is exactly why the reduced statement is
the oriented `C ≥ −R″` and not a symmetric quadratic form.

---

## APPROACH 3 — SOS / sufficient-condition search

- **Scalar, not a form.** For simple `λ₂` the Fiedler eigenspace is 1-dimensional, so
  `RHS − W₁` is a single number per graph; classical SOS (PSD of a quadratic form in
  free variables) does not apply. The natural surrogate — `λ₂Q − L_{min} ⪰ 0` on `1⊥`
  — is **indefinite** (already shown for the weaker `λ₂Q − L_t`, min eigenvalue `−37`,
  PSD on only 6/9020 graphs; `L_{min} ⪰ L_t` only makes it worse). So no operator/SOS
  certificate.
- **Cleaner sufficient condition `C ≥ 0`: FALSE.** Since `R″ ≥ 0`, `C ≥ 0` would imply
  B2′. But `C < 0` on **7323/9020 (81%)** corpus graphs (min `−1.53`) and **184/253**
  hard families (min `−2.10`). The negative oriented sum must be *absorbed* by `R″`;
  the inequality is tight in the balance, not in either term.
- **What a certificate must do.** Bound the signed oriented sum
  `C = Σ(d_h−d_l)f_h(f_h−f_l)` from below by `−R″ = −λ₂(A+1−S²/m)`. Because `C` is
  indefinite, any proof must use the *minimality* of `λ₂` (Fiedler `f` minimizes the
  `L_G` Rayleigh quotient on `1⊥`), not just `Lf=λ₂f` — to control where `f_h−f_l` is
  large against where `d_h−d_l` is large. This matches the global-variational finding
  that B is intrinsically an eigenvector/minimality phenomenon.

---

## APPROACH 4 — literature

No off-the-shelf result applies. Standard Fiedler theory supplies only
`λ₂ ≤ κ(G)` (vertex connectivity), the Cheeger sandwich `λ₂/2 ≤ h(G) ≤ √(2λ₂)`, and
weighted-Laplacian perturbation results (simple eigenvalues / nonzero Fiedler entries
under reweighting) — none compares a **degree-weighted edge form** to `λ₂` *on the
eigenvector*, and none gives an **oriented degree-gradient** bound. The
degree-correlation sub-fact `A+1 ≥ S²/m` (`S = ⟨f,d⟩`) also does not appear in the
surveys. The inequality `C ≥ −R″` appears to be novel.

Sources: [Algebraic connectivity (Wikipedia)](https://en.wikipedia.org/wiki/Algebraic_connectivity),
[Spectra of Laplacians of weighted graphs (arXiv:1704.01677)](https://arxiv.org/pdf/1704.01677),
[de Abreu, *Old and new results on algebraic connectivity*](https://www.math.ucdavis.edu/~saito/data/graphlap/deabreu-algconn.pdf),
[The Laplacian eigenvalues of graphs: a survey (arXiv:1111.2897)](https://arxiv.org/pdf/1111.2897).

---

## Synthesis — the reduced open problem

Conjecture B reduces, rigorously, to a single **triangle-free, min-free, oriented**
inequality on the Fiedler vector:

> Prove, for the unit Fiedler `f` of any connected non-bipartite `G`, with `h/l` the
> higher/lower-degree endpoints of each edge:
> **`Σ_{ab∈E}(d_h−d_l)·f_h·(f_h−f_l) ≥ −λ₂·(fᵀDf − λ₂ + 1 − S²/m)`.**

- **Equivalent to B2′** (0 mismatches, exact identity verified to 1e-13), hence ⟹ B.
- **Tight only at `K_n`** (both sides 0).
- **Supported on degree-heterogeneous edges** — regular graphs are automatic.
- **Sub-lemma to formalize first:** `fᵀDf − λ₂ + 1 ≥ S²/m` (`R″ ≥ 0`), a clean
  degree-Fiedler correlation bound holding with equality at `K_n`.
- **Not SOS / not operator-dominated:** `C` is negative on 81% of graphs and
  `λ₂Q−L_min` is indefinite, so a proof must invoke `λ₂`'s *minimality*, not merely
  the eigen-equation.

### Caveats
`λ₂`, `f` numerical. All identities verified to `≤7e-14` over the full 9020-graph
`n≤9` corpus; the oriented collapse and `B2′ ⟺ C≥−R″` checked with 0 mismatches on a
1500-graph sample; relaxation/SOS statistics over corpus + 253 hard families
(`K_n−e` to n=80, dense ER bottleneck graphs, large Watts–Strogatz). The reduction
`B ⟸ B2′` is rigorous; B2′ (= `C ≥ −R″`) itself remains empirically universal, unproven.
