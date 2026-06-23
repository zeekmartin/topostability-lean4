# Extremizer census — aggregate triangle Poincaré  `R = T/(λ₂·degQuad)`

**Date:** 2026-06-23 · **Repo:** topostability-lean4 · analysis only, no Lean changes.

`R = T_edges/(λ₂·degQuad)` with `T_edges = Σ_e t_e(u_a−u_b)²`, `t_e=|N_a∩N_b|`, `degQuad=Σ_v d_v u_v²`, **maximised over the λ₂-eigenspace** (the true test of the aggregate, which must hold for every Fiedler). The conjecture is `R ≤ 1`. Census: **4054 connected graphs** (complete enumeration n=6:112, n=7:853 via NetworkX atlas; n=8 is a **random sample of 3000**, NOT exhaustive — no nauty/geng in env).

## ⚠ Correction to the brief: `K_n` does NOT give `R = 1` exactly

Analytically, for `K_n` and **any** Fiedler `u` (`Σu=0`): `λ₂=n`, `degQuad=(n−1)‖u‖²`, `t_e=n−2`, `T=(n−2)·n‖u‖²`, so

```
R(K_n) = (n−2)·n / (n·(n−1)) = (n−2)/(n−1)   < 1  for all finite n.
```

`K_n` is the **asymptotic** extremizer (`R → 1` as `n→∞`), not an exact-equality case. Measured vs the closed form:

| n | R(K_n) measured | (n−2)/(n−1) |
|---|---|---|
| 20 | 0.947368 | 0.947368 |
| 40 | 0.974359 | 0.974359 |
| 80 | 0.987342 | 0.987342 |
| 160 | 0.993711 | 0.993711 |

## Synthesis — direct answers to the questions

1. **The near-equality extremizers are homogeneous dense graphs — NOT "dense core +
   sparse appendage".** Every graph in the top 50 is complete or one-edge-from-complete
   (`maxt/meant ≈ 1.0–1.08`, uniform triangle distribution, modest localisation
   `loc ≈ 3–17`). R is an essentially *monotone function of density at fixed n*: the
   ranking is `K₁₀₀ > K₅₀ > K₂₀ > K₁₂ > K₈ ≈ (near-complete n=8) > …`. **The brief's
   "dense core + sparse appendage" guess is refuted** — appendages *lower* R.

2. **Proof-hardness ≠ near-tightness (the key finding).** The families that are hard for
   the *formal* aggregate proof — the TYPE A bottlenecks `deg2dense` and `twin` — sit at
   **R = 0.03–0.65, far from 1** (TASK 5). The aggregate has its *largest* slack exactly
   on the graphs the Lean proof struggles with. Tightness of R is driven by global
   density, not by the local triangle-overlap bottleneck (`maxt ≫ degQuad`) that makes
   `aggregate_triangle_poincare` analytically awkward.

3. **The only family with R → 1 is the complete sequence `K_n`** (and near-complete
   graphs). `R(K_n) = (n−2)/(n−1)`. No bottleneck/appendage/sparse family approaches 1;
   `deg2dense(n,q)` converges to a `q`-dependent constant `< 1` as `n → ∞`
   (≈0.13 at q=0.3, ≈0.59 at q=0.5, ≈0.65 at q=0.9) with **bounded** Slack (≈2–4), and
   `twin`/lollipop/barbell are all well below. So the extremal landscape near `R=1` is a
   *single ray* through the complete graphs, isolated from the hard-proof regime.

4. **Slack `= λ₂·degQuad − T` is NOT monotone under edge deletion** (91.9% of deletions
   *decrease* it; every `K_n` deletion drops Slack by exactly 2). But this is a **scale
   artefact**: `Slack = λ₂·degQuad·(1−R)` and the `λ₂·degQuad` prefactor shrinks with each
   deletion, so absolute Slack falls even though the *normalised* gap `1−R` grows. R itself
   is also non-monotone under deletion (TASK 3). Neither is a clean monotone certificate.

**Take-away for the proof effort:** chasing the extremizer (`K_n`) will not illuminate
`aggregate_triangle_poincare`'s hard case — the binding constraint lives on low-R bottleneck
graphs where slack is large but the *eigenvector-equation cancellation* is delicate, not on
the high-R dense graphs where slack is structurally guaranteed.

## TASK 1 — Top 50 by R

| # | name | family | n | m | R | λ₂ | mult | maxt/meant | loc |
|---|------|--------|---|---|---|-----|------|-----------|-----|
| 1 | K100 | complete | 100 | 4950 | 0.98990 | 100.0000 | 99 | 1.00 | 16.7 |
| 2 | K50 | complete | 50 | 1225 | 0.97959 | 50.0000 | 49 | 1.00 | 6.4 |
| 3 | K20 | complete | 20 | 190 | 0.94737 | 20.0000 | 19 | 1.00 | 8.9 |
| 4 | K12 | complete | 12 | 66 | 0.90909 | 12.0000 | 11 | 1.00 | 3.5 |
| 5 | K8 | complete | 8 | 28 | 0.85714 | 8.0000 | 7 | 1.00 | 3.6 |
| 6 | rand8_452 | sample_n8 | 8 | 28 | 0.85714 | 8.0000 | 7 | 1.00 | 3.6 |
| 7 | rand8_561 | sample_n8 | 8 | 28 | 0.85714 | 8.0000 | 7 | 1.00 | 3.6 |
| 8 | rand8_1370 | sample_n8 | 8 | 28 | 0.85714 | 8.0000 | 7 | 1.00 | 3.6 |
| 9 | rand8_1586 | sample_n8 | 8 | 28 | 0.85714 | 8.0000 | 7 | 1.00 | 3.6 |
| 10 | rand8_1703 | sample_n8 | 8 | 28 | 0.85714 | 8.0000 | 7 | 1.00 | 3.6 |
| 11 | rand8_2021 | sample_n8 | 8 | 28 | 0.85714 | 8.0000 | 7 | 1.00 | 3.6 |
| 12 | rand8_2026 | sample_n8 | 8 | 28 | 0.85714 | 8.0000 | 7 | 1.00 | 3.6 |
| 13 | rand8_228 | sample_n8 | 8 | 27 | 0.83333 | 6.0000 | 1 | 1.08 | 4.0 |
| 14 | rand8_2145 | sample_n8 | 8 | 27 | 0.83333 | 6.0000 | 1 | 1.08 | 4.0 |
| 15 | atlas7_1252 | all_n7 | 7 | 21 | 0.83333 | 7.0000 | 6 | 1.00 | 3.0 |
| 16 | rand8_3725 | sample_n8 | 8 | 27 | 0.83333 | 6.0000 | 1 | 1.08 | 4.0 |
| 17 | rand8_1538 | sample_n8 | 8 | 27 | 0.83333 | 6.0000 | 1 | 1.08 | 4.0 |
| 18 | rand8_2265 | sample_n8 | 8 | 27 | 0.83333 | 6.0000 | 1 | 1.08 | 4.0 |
| 19 | rand8_2406 | sample_n8 | 8 | 27 | 0.83333 | 6.0000 | 1 | 1.08 | 4.0 |
| 20 | rand8_186 | sample_n8 | 8 | 27 | 0.83333 | 6.0000 | 1 | 1.08 | 4.0 |
| 21 | rand8_982 | sample_n8 | 8 | 27 | 0.83333 | 6.0000 | 1 | 1.08 | 4.0 |
| 22 | rand8_2349 | sample_n8 | 8 | 27 | 0.83333 | 6.0000 | 1 | 1.08 | 4.0 |
| 23 | rand8_21 | sample_n8 | 8 | 27 | 0.83333 | 6.0000 | 1 | 1.08 | 4.0 |
| 24 | rand8_446 | sample_n8 | 8 | 27 | 0.83333 | 6.0000 | 1 | 1.08 | 4.0 |
| 25 | rand8_1056 | sample_n8 | 8 | 27 | 0.83333 | 6.0000 | 1 | 1.08 | 4.0 |
| 26 | rand8_1679 | sample_n8 | 8 | 27 | 0.83333 | 6.0000 | 1 | 1.08 | 4.0 |
| 27 | rand8_1866 | sample_n8 | 8 | 27 | 0.83333 | 6.0000 | 1 | 1.08 | 4.0 |
| 28 | rand8_2550 | sample_n8 | 8 | 27 | 0.83333 | 6.0000 | 1 | 1.08 | 4.0 |
| 29 | rand8_3187 | sample_n8 | 8 | 27 | 0.83333 | 6.0000 | 1 | 1.08 | 4.0 |
| 30 | rand8_3524 | sample_n8 | 8 | 27 | 0.83333 | 6.0000 | 1 | 1.08 | 4.0 |
| 31 | rand8_3675 | sample_n8 | 8 | 27 | 0.83333 | 6.0000 | 1 | 1.08 | 4.0 |
| 32 | rand8_377 | sample_n8 | 8 | 27 | 0.83333 | 6.0000 | 1 | 1.08 | 4.0 |
| 33 | rand8_575 | sample_n8 | 8 | 27 | 0.83333 | 6.0000 | 1 | 1.08 | 4.0 |
| 34 | rand8_1134 | sample_n8 | 8 | 27 | 0.83333 | 6.0000 | 1 | 1.08 | 4.0 |
| 35 | rand8_1189 | sample_n8 | 8 | 27 | 0.83333 | 6.0000 | 1 | 1.08 | 4.0 |
| 36 | rand8_1424 | sample_n8 | 8 | 27 | 0.83333 | 6.0000 | 1 | 1.08 | 4.0 |
| 37 | rand8_2003 | sample_n8 | 8 | 27 | 0.83333 | 6.0000 | 1 | 1.08 | 4.0 |
| 38 | rand8_3561 | sample_n8 | 8 | 27 | 0.83333 | 6.0000 | 1 | 1.08 | 4.0 |
| 39 | rand8_3812 | sample_n8 | 8 | 27 | 0.83333 | 6.0000 | 1 | 1.08 | 4.0 |
| 40 | rand8_448 | sample_n8 | 8 | 27 | 0.83333 | 6.0000 | 1 | 1.08 | 4.0 |
| 41 | rand8_2253 | sample_n8 | 8 | 27 | 0.83333 | 6.0000 | 1 | 1.08 | 4.0 |
| 42 | rand8_278 | sample_n8 | 8 | 27 | 0.83333 | 6.0000 | 1 | 1.08 | 4.0 |
| 43 | rand8_705 | sample_n8 | 8 | 27 | 0.83333 | 6.0000 | 1 | 1.08 | 4.0 |
| 44 | rand8_2250 | sample_n8 | 8 | 27 | 0.83333 | 6.0000 | 1 | 1.08 | 4.0 |
| 45 | rand8_3036 | sample_n8 | 8 | 27 | 0.83333 | 6.0000 | 1 | 1.08 | 4.0 |
| 46 | rand8_629 | sample_n8 | 8 | 27 | 0.83333 | 6.0000 | 1 | 1.08 | 4.0 |
| 47 | rand8_1223 | sample_n8 | 8 | 27 | 0.83333 | 6.0000 | 1 | 1.08 | 4.0 |
| 48 | rand8_3268 | sample_n8 | 8 | 27 | 0.83333 | 6.0000 | 1 | 1.08 | 4.0 |
| 49 | rand8_499 | sample_n8 | 8 | 27 | 0.83333 | 6.0000 | 1 | 1.08 | 4.0 |
| 50 | rand8_523 | sample_n8 | 8 | 27 | 0.83333 | 6.0000 | 1 | 1.08 | 4.0 |

Max R over the whole census = **0.989899** (K100). All 4054 graphs satisfy R ≤ 1 (min slack = 4.915e-02).

## TASK 2 — Anatomy of the top-R graphs

| name | n | m | tri | deg(min/max/mean/std) | maxt/meant | loc | edges>50%T (k,frac) | verts>50%degQ (k,frac) |
|------|---|---|-----|----------------------|-----------|-----|--------------------|------------------------|
| K100 | 100 | 4950 | 161700 | 99/99/99.0/0.0 | 1.00 | 16.7 | 445,0.09 | 8,0.08 |
| K50 | 50 | 1225 | 19600 | 49/49/49.0/0.0 | 1.00 | 6.4 | 163,0.13 | 8,0.16 |
| K20 | 20 | 190 | 1140 | 19/19/19.0/0.0 | 1.00 | 8.9 | 17,0.09 | 2,0.10 |
| K12 | 12 | 66 | 220 | 11/11/11.0/0.0 | 1.00 | 3.5 | 11,0.17 | 3,0.25 |
| K8 | 8 | 28 | 56 | 7/7/7.0/0.0 | 1.00 | 3.6 | 5,0.18 | 2,0.25 |
| rand8_452 | 8 | 28 | 56 | 7/7/7.0/0.0 | 1.00 | 3.6 | 5,0.18 | 2,0.25 |
| rand8_561 | 8 | 28 | 56 | 7/7/7.0/0.0 | 1.00 | 3.6 | 5,0.18 | 2,0.25 |
| rand8_1370 | 8 | 28 | 56 | 7/7/7.0/0.0 | 1.00 | 3.6 | 5,0.18 | 2,0.25 |
| rand8_1586 | 8 | 28 | 56 | 7/7/7.0/0.0 | 1.00 | 3.6 | 5,0.18 | 2,0.25 |
| rand8_1703 | 8 | 28 | 56 | 7/7/7.0/0.0 | 1.00 | 3.6 | 5,0.18 | 2,0.25 |
| rand8_2021 | 8 | 28 | 56 | 7/7/7.0/0.0 | 1.00 | 3.6 | 5,0.18 | 2,0.25 |
| rand8_2026 | 8 | 28 | 56 | 7/7/7.0/0.0 | 1.00 | 3.6 | 5,0.18 | 2,0.25 |
| rand8_228 | 8 | 27 | 50 | 6/7/6.8/0.4 | 1.08 | 4.0 | 6,0.22 | 1,0.12 |
| rand8_2145 | 8 | 27 | 50 | 6/7/6.8/0.4 | 1.08 | 4.0 | 6,0.22 | 1,0.12 |
| atlas7_1252 | 7 | 21 | 35 | 6/6/6.0/0.0 | 1.00 | 3.0 | 4,0.19 | 2,0.29 |
| rand8_3725 | 8 | 27 | 50 | 6/7/6.8/0.4 | 1.08 | 4.0 | 6,0.22 | 2,0.25 |
| rand8_1538 | 8 | 27 | 50 | 6/7/6.8/0.4 | 1.08 | 4.0 | 6,0.22 | 1,0.12 |
| rand8_2265 | 8 | 27 | 50 | 6/7/6.8/0.4 | 1.08 | 4.0 | 6,0.22 | 1,0.12 |
| rand8_2406 | 8 | 27 | 50 | 6/7/6.8/0.4 | 1.08 | 4.0 | 6,0.22 | 1,0.12 |
| rand8_186 | 8 | 27 | 50 | 6/7/6.8/0.4 | 1.08 | 4.0 | 6,0.22 | 2,0.25 |
| rand8_982 | 8 | 27 | 50 | 6/7/6.8/0.4 | 1.08 | 4.0 | 6,0.22 | 1,0.12 |
| rand8_2349 | 8 | 27 | 50 | 6/7/6.8/0.4 | 1.08 | 4.0 | 6,0.22 | 1,0.12 |
| rand8_21 | 8 | 27 | 50 | 6/7/6.8/0.4 | 1.08 | 4.0 | 6,0.22 | 1,0.12 |
| rand8_446 | 8 | 27 | 50 | 6/7/6.8/0.4 | 1.08 | 4.0 | 6,0.22 | 1,0.12 |
| rand8_1056 | 8 | 27 | 50 | 6/7/6.8/0.4 | 1.08 | 4.0 | 6,0.22 | 1,0.12 |
| rand8_1679 | 8 | 27 | 50 | 6/7/6.8/0.4 | 1.08 | 4.0 | 6,0.22 | 1,0.12 |
| rand8_1866 | 8 | 27 | 50 | 6/7/6.8/0.4 | 1.08 | 4.0 | 6,0.22 | 1,0.12 |
| rand8_2550 | 8 | 27 | 50 | 6/7/6.8/0.4 | 1.08 | 4.0 | 6,0.22 | 1,0.12 |
| rand8_3187 | 8 | 27 | 50 | 6/7/6.8/0.4 | 1.08 | 4.0 | 6,0.22 | 1,0.12 |
| rand8_3524 | 8 | 27 | 50 | 6/7/6.8/0.4 | 1.08 | 4.0 | 6,0.22 | 1,0.12 |

**Family composition of top 50:** sample_n8=44, complete=5, all_n7=1

**Localisation** (top 50): loc mean = 4.31, max = 16.65 (loc=1 ⇒ uniform Fiedler, loc=n ⇒ a single vertex). **Concentration**: median edges carrying >50% of T = 22% of edges; median vertices carrying >50% of degQ = 12% of vertices.

## TASK 3 — Perturbation from K₂₀ (edge removal)

R after removing edges from K₂₀ (keeping connectivity), three removal orders. Sampled steps:

| #removed | random | triangle_poor (min t_e) | triangle_rich (max t_e) |
|---|---|---|---|
| 0 | 0.94737 | 0.94737 | 0.94737 |
| 1 | 0.94444 | 0.94444 | 0.94444 |
| 2 | 0.93827 | 0.94231 | 0.93827 |
| 5 | 0.92195 | 0.93182 | 0.91975 |
| 10 | 0.89328 | 0.89815 | 0.88889 |
| 20 | 0.83600 | 0.46894 | 0.82813 |
| 40 | 0.75340 | 0.61865 | 0.68000 |
| 60 | 0.58373 | 0.68660 | 0.48052 |
| 80 | 0.50615 | 0.77381 | 0.12727 |
| 100 | 0.35606 | 0.77525 | 0.00000 |
| 120 | 0.31683 | 0.79610 | 0.00000 |

- **random**: R is NON-monotone — 23 of 120 removals *increase* R. Final R=0.31683, start R=0.94737.
- **triangle_poor**: R is NON-monotone — 7 of 120 removals *increase* R. Final R=0.79610, start R=0.94737.
- **triangle_rich**: R is NON-monotone — 12 of 120 removals *increase* R. Final R=0.00000, start R=0.94737.

## TASK 4 — Edge-deletion monotonicity of Slack = λ₂·degQuad − T (top 20)

For each near-tight graph, remove each edge (keep connectivity) and compare `Slack(G−e)` vs `Slack(G)` (each graph's own max-R Fiedler, ‖u‖²=1). Dense graphs: 300 edges sampled.

| name | Slack(G) | edges tested | #violations (Slack drops) | sampled |
|------|---------|--------------|---------------------------|---------|
| K100 | 1.0000e+02 | 300 | 300 | yes |
| K50 | 5.0000e+01 | 300 | 300 | yes |
| K20 | 2.0000e+01 | 190 | 190 | no |
| K12 | 1.2000e+01 | 66 | 66 | no |
| K8 | 8.0000e+00 | 28 | 28 | no |
| rand8_452 | 8.0000e+00 | 28 | 28 | no |
| rand8_561 | 8.0000e+00 | 28 | 28 | no |
| rand8_1370 | 8.0000e+00 | 28 | 28 | no |
| rand8_1586 | 8.0000e+00 | 28 | 28 | no |
| rand8_1703 | 8.0000e+00 | 28 | 28 | no |
| rand8_2021 | 8.0000e+00 | 28 | 28 | no |
| rand8_2026 | 8.0000e+00 | 28 | 28 | no |
| rand8_228 | 6.0000e+00 | 27 | 12 | no |
| rand8_2145 | 6.0000e+00 | 27 | 12 | no |
| atlas7_1252 | 7.0000e+00 | 21 | 21 | no |
| rand8_3725 | 6.0000e+00 | 27 | 12 | no |
| rand8_1538 | 6.0000e+00 | 27 | 12 | no |
| rand8_2265 | 6.0000e+00 | 27 | 12 | no |
| rand8_2406 | 6.0000e+00 | 27 | 12 | no |
| rand8_186 | 6.0000e+00 | 27 | 12 | no |

**Total: 1185 violations of 1290 edge deletions tested (91.9%).** Slack is NOT monotone under edge deletion.

Sample violating edges (ΔSlack, t_e, deg_a, deg_b):
- ΔSlack=-2.000e+00, t_e=98, deg=(99,99)
- ΔSlack=-2.000e+00, t_e=98, deg=(99,99)
- ΔSlack=-2.000e+00, t_e=98, deg=(99,99)
- ΔSlack=-2.000e+00, t_e=98, deg=(99,99)
- ΔSlack=-2.000e+00, t_e=98, deg=(99,99)
- ΔSlack=-2.000e+00, t_e=10, deg=(11,11)
- ΔSlack=-2.000e+00, t_e=5, deg=(6,6)
- ΔSlack=-2.000e+00, t_e=5, deg=(6,6)
- ΔSlack=-2.000e+00, t_e=6, deg=(7,7)
- ΔSlack=-2.000e+00, t_e=6, deg=(7,7)
- ΔSlack=-2.000e+00, t_e=6, deg=(7,7)
- ΔSlack=-2.000e+00, t_e=6, deg=(7,7)

## TASK 5 — Asymptotics of deg2dense(n,q)

`deg2dense(n,q)` = dense `G(n−1,q)` block + one degree-2 vertex bridging nodes 0,1.

**q=0.1:**

| n | R | Slack | λ₂ | maxt | maxt/meant |
|---|---|-------|-----|------|-----------|
| 40 | 0.03130 | 9.6828e-01 | 0.6118 | 3 | 8.20 |
| 80 | 0.07896 | 3.8133e+00 | 1.6395 | 5 | 5.11 |
| 160 | 0.03145 | 4.0717e+00 | 1.8140 | 7 | 4.79 |

**q=0.3:**

| n | R | Slack | λ₂ | maxt | maxt/meant |
|---|---|-------|-----|------|-----------|
| 20 | 0.19855 | 3.5782e+00 | 1.7986 | 6 | 2.91 |
| 40 | 0.13448 | 3.9882e+00 | 1.8249 | 9 | 2.22 |
| 80 | 0.14531 | 3.9235e+00 | 1.9511 | 18 | 2.29 |
| 160 | 0.13642 | 3.9628e+00 | 1.9716 | 29 | 2.01 |

**q=0.5:**

| n | R | Slack | λ₂ | maxt | maxt/meant |
|---|---|-------|-----|------|-----------|
| 20 | 0.57538 | 2.0775e+00 | 1.9233 | 11 | 2.14 |
| 40 | 0.60086 | 1.9878e+00 | 1.9353 | 18 | 1.79 |
| 80 | 0.59303 | 2.0275e+00 | 1.9799 | 31 | 1.53 |
| 160 | 0.59874 | 2.0012e+00 | 1.9871 | 59 | 1.49 |

**q=0.9:**

| n | R | Slack | λ₂ | maxt | maxt/meant |
|---|---|-------|-----|------|-----------|
| 20 | 0.64934 | 1.9852e+00 | 1.9926 | 17 | 1.14 |
| 40 | 0.64910 | 1.9927e+00 | 1.9961 | 36 | 1.22 |
| 80 | 0.65173 | 2.0041e+00 | 1.9984 | 71 | 1.13 |
| 160 | 0.65336 | 2.0021e+00 | 1.9985 | 141 | 1.11 |

**K_n reference:** R=(n−2)/(n−1)→1, Slack grows ∝ n (degQuad∝n).

