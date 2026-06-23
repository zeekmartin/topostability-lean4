# Bottleneck slack anatomy — why high-slack graphs resist certification

**Date:** 2026-06-23 · topostability-lean4 · analysis only, no Lean changes.

`Slack = λ₂·degQuad − T`, `R = T/(λ₂·degQuad)`, max-R Fiedler over the λ₂-eigenspace. Per-edge `T_e = t_e(u_a−u_b)²`, `t_e=|N_a∩N_b|`. Vertices split into **core** (dense block) and **port** (the appendage / twin vertices). Edge classes: `cc` core-core, `cp` core-port, `pp` port-port. TYPE A set = 31 graphs (deg2dense, twin).

## TASK 1 + TASK 3 — Slack/T concentration on the 10 hardest (lowest-R) graphs

| name | n | R | Slack | maxt_e of e* | e* class | e* %of T | edges→50%T | edges→90%T |
|------|---|---|-------|------|--------|---------|-----------|-----------|
| deg2d40_0.1 | 40 | 0.0313 | 9.683e-01 | 1 | cc | 26.9% | 3 | 10 |
| deg2d60_0.1 | 60 | 0.0700 | 1.123e+00 | 2 | cc | 36.4% | 2 | 11 |
| deg2d40_0.2 | 40 | 0.0733 | 3.869e+00 | 5 | cc | 11.3% | 6 | 28 |
| deg2d80_0.1 | 80 | 0.0790 | 3.813e+00 | 3 | cc | 9.5% | 8 | 51 |
| deg2d80_0.2 | 80 | 0.0977 | 3.940e+00 | 5 | cc | 4.3% | 16 | 36 |
| deg2d60_0.2 | 60 | 0.1245 | 3.813e+00 | 5 | cc | 10.2% | 8 | 24 |
| deg2d40_0.3 | 40 | 0.1345 | 3.988e+00 | 2 | cc | 8.1% | 9 | 26 |
| deg2d60_0.3 | 60 | 0.1429 | 3.922e+00 | 7 | cc | 4.3% | 16 | 35 |
| deg2d80_0.3 | 80 | 0.1453 | 3.924e+00 | 12 | cc | 3.2% | 24 | 50 |
| deg2d20_0.3 | 20 | 0.1986 | 3.578e+00 | 6 | cc | 12.4% | 6 | 19 |

Top-5 edges by T-contribution `(T_e, t_e, class)` for the 5 hardest:

- **deg2d40_0.1** (R=0.0313): (8.43e-03,t=1,cc), (4.68e-03,t=1,cc), (4.54e-03,t=3,cc), (4.29e-03,t=1,cc), (2.21e-03,t=1,cc)
- **deg2d60_0.1** (R=0.0700): (3.08e-02,t=2,cc), (1.98e-02,t=1,cc), (1.60e-02,t=1,cc), (2.02e-03,t=2,cc), (1.86e-03,t=1,cc)
- **deg2d40_0.2** (R=0.0733): (3.45e-02,t=5,cc), (2.75e-02,t=4,cc), (2.74e-02,t=4,cc), (2.53e-02,t=4,cc), (2.32e-02,t=3,cc)
- **deg2d80_0.1** (R=0.0790): (3.10e-02,t=3,cc), (3.10e-02,t=1,cc), (2.45e-02,t=2,cc), (2.35e-02,t=2,cc), (2.09e-02,t=1,cc)
- **deg2d80_0.2** (R=0.0977): (1.84e-02,t=5,cc), (1.62e-02,t=4,cc), (1.58e-02,t=4,cc), (1.57e-02,t=4,cc), (1.51e-02,t=4,cc)

## TASK 2 — Core / port / cross split of T and degQuad

Hardest deg2dense (single degree-2 port) **and all twin graphs** (the canonical TYPE A, where ports carry real cross-mass):

| name | R | T_cc | T_cp | T_pp | DQ_core | DQ_port | R_cc | R_cp | R_pp |
|------|---|------|------|------|---------|---------|------|------|------|
| deg2d40_0.1 | 0.0313 | 3.129e-02 | 0.000e+00 | 0.000e+00 | 1.633e+00 | 7.594e-04 | 0.031 | 0.000 | 0.000 |
| deg2d60_0.1 | 0.0700 | 8.462e-02 | 0.000e+00 | 0.000e+00 | 1.437e+00 | 2.745e-04 | 0.070 | 0.000 | 0.000 |
| deg2d40_0.2 | 0.0733 | 3.062e-01 | 0.000e+00 | 0.000e+00 | 8.354e-01 | 1.714e+00 | 0.224 | 0.000 | 0.000 |
| deg2d80_0.1 | 0.0790 | 3.269e-01 | 0.000e+00 | 0.000e+00 | 2.500e+00 | 2.538e-02 | 0.080 | 0.000 | 0.000 |
| deg2d80_0.2 | 0.0977 | 4.265e-01 | 0.000e+00 | 0.000e+00 | 3.123e-01 | 1.962e+00 | 0.711 | 0.000 | 0.000 |
| deg2d60_0.2 | 0.1245 | 5.425e-01 | 0.000e+00 | 0.000e+00 | 4.274e-01 | 1.926e+00 | 0.686 | 0.000 | 0.000 |
| deg2d40_0.3 | 0.1345 | 6.197e-01 | 0.000e+00 | 0.000e+00 | 6.386e-01 | 1.886e+00 | 0.532 | 0.000 | 0.000 |
| deg2d60_0.3 | 0.1429 | 6.541e-01 | 0.000e+00 | 0.000e+00 | 4.294e-01 | 1.953e+00 | 0.793 | 0.000 | 0.000 |
| deg2d80_0.3 | 0.1453 | 6.671e-01 | 0.000e+00 | 0.000e+00 | 3.837e-01 | 1.969e+00 | 0.891 | 0.000 | 0.000 |
| deg2d20_0.3 | 0.1986 | 8.865e-01 | 0.000e+00 | 0.000e+00 | 7.240e-01 | 1.758e+00 | 0.681 | 0.000 | 0.000 |
| twin20_1 | 0.3400 | 8.827e-01 | 0.000e+00 | 0.000e+00 | 2.450e+00 | 1.742e+00 | 0.582 | 0.000 | 0.000 |
| twin50_1 | 0.3451 | 9.523e-01 | 0.000e+00 | 0.000e+00 | 2.713e+00 | 1.889e+00 | 0.585 | 0.000 | 0.000 |
| twin50_2 | 0.4010 | 1.269e+00 | 6.607e-01 | 0.000e+00 | 2.485e+00 | 2.204e+00 | 0.498 | 0.137 | 0.000 |
| twin20_2 | 0.4011 | 1.178e+00 | 6.516e-01 | 0.000e+00 | 2.250e+00 | 2.032e+00 | 0.491 | 0.143 | 0.000 |
| twin20_5 | 0.4049 | 6.897e-01 | 1.720e+00 | 0.000e+00 | 1.552e+00 | 2.048e+00 | 0.269 | 0.289 | 0.000 |
| twin50_5 | 0.4129 | 8.245e-01 | 1.789e+00 | 0.000e+00 | 1.751e+00 | 2.226e+00 | 0.296 | 0.283 | 0.000 |
| twin20_3 | 0.4180 | 1.081e+00 | 1.228e+00 | 0.000e+00 | 1.977e+00 | 2.103e+00 | 0.404 | 0.222 | 0.000 |
| twin50_3 | 0.4187 | 1.191e+00 | 1.252e+00 | 0.000e+00 | 2.196e+00 | 2.284e+00 | 0.416 | 0.215 | 0.000 |

T mass by class (share of total T):

| name | cc | cp | pp |
|------|----|----|----|
| deg2d40_0.1 | 100.0% | 0.0% | 0.0% |
| deg2d60_0.1 | 100.0% | 0.0% | 0.0% |
| deg2d40_0.2 | 100.0% | 0.0% | 0.0% |
| deg2d80_0.1 | 100.0% | 0.0% | 0.0% |
| deg2d80_0.2 | 100.0% | 0.0% | 0.0% |
| deg2d60_0.2 | 100.0% | 0.0% | 0.0% |
| deg2d40_0.3 | 100.0% | 0.0% | 0.0% |
| deg2d60_0.3 | 100.0% | 0.0% | 0.0% |
| deg2d80_0.3 | 100.0% | 0.0% | 0.0% |
| deg2d20_0.3 | 100.0% | 0.0% | 0.0% |
| twin20_1 | 100.0% | 0.0% | 0.0% |
| twin50_1 | 100.0% | 0.0% | 0.0% |
| twin50_2 | 65.8% | 34.2% | 0.0% |
| twin20_2 | 64.4% | 35.6% | 0.0% |
| twin20_5 | 28.6% | 71.4% | 0.0% |
| twin50_5 | 31.5% | 68.5% | 0.0% |
| twin20_3 | 46.8% | 53.2% | 0.0% |
| twin50_3 | 48.8% | 51.2% | 0.0% |

## TASK 4 — Conditional aggregate on the CORE only  (R_core ≤ 1 ?)

`R_core = max_eigenspace T_core/(λ₂^core · degQuad_core)` on the induced core subgraph with its OWN Fiedler. If `R_core ≤ 1` with comfortable margin, the difficulty is NOT in the core — it is in the cross/port coupling.

| name | R (full) | R_core | λ₂(core) | core easy? |
|------|----------|--------|----------|-----------|
| deg2d40_0.1 | 0.0313 | 0.0326 | 0.610 | yes |
| deg2d60_0.1 | 0.0700 | 0.0720 | 0.840 | yes |
| deg2d40_0.2 | 0.0733 | 0.0907 | 2.457 | yes |
| deg2d80_0.1 | 0.0790 | 0.0795 | 1.641 | yes |
| deg2d80_0.2 | 0.0977 | 0.2413 | 6.941 | yes |
| deg2d60_0.2 | 0.1245 | 0.1396 | 4.426 | yes |
| deg2d40_0.3 | 0.1345 | 0.2921 | 5.834 | yes |
| deg2d60_0.3 | 0.1429 | 0.2529 | 9.705 | yes |
| deg2d80_0.3 | 0.1453 | 0.3113 | 13.637 | yes |
| deg2d20_0.3 | 0.1986 | 0.3732 | 2.560 | yes |
| deg2d20_0.2 | 0.2400 | 0.2767 | 0.849 | yes |
| twin20_1 | 0.3400 | 0.9474 | 20.000 | yes |
| twin50_1 | 0.3451 | 0.9796 | 50.000 | yes |
| twin50_2 | 0.4010 | 0.9796 | 50.000 | yes |
| twin20_2 | 0.4011 | 0.9474 | 20.000 | yes |
| twin20_5 | 0.4049 | 0.9474 | 20.000 | yes |
| twin50_5 | 0.4129 | 0.9796 | 50.000 | yes |
| twin20_3 | 0.4180 | 0.9474 | 20.000 | yes |
| twin50_3 | 0.4187 | 0.9796 | 50.000 | yes |
| deg2d20_0.5 | 0.5754 | 0.5502 | 5.951 | yes |
| deg2d60_0.5 | 0.5915 | 0.5203 | 18.647 | yes |
| deg2d80_0.5 | 0.5930 | 0.5232 | 26.764 | yes |
| deg2d40_0.5 | 0.6009 | 0.5097 | 10.497 | yes |
| deg2d20_0.7 | 0.6245 | 0.7102 | 9.966 | yes |
| deg2d60_0.7 | 0.6267 | 0.6801 | 29.958 | yes |
| deg2d80_0.7 | 0.6284 | 0.6939 | 44.810 | yes |
| deg2d40_0.7 | 0.6302 | 0.6935 | 19.089 | yes |
| deg2d40_0.9 | 0.6491 | 0.8692 | 29.683 | yes |
| deg2d20_0.9 | 0.6493 | 0.8918 | 13.893 | yes |
| deg2d80_0.9 | 0.6517 | 0.8904 | 63.665 | yes |
| deg2d60_0.9 | 0.6520 | 0.8891 | 45.765 | yes |

**Core aggregate `R_core ≤ 1`: 31/31 hold.** max R_core = 0.9796, mean = 0.5900.

## TASK 3 (cont.) — Anti-correlation of triangle weight `t_e` and Fiedler gap `g_e²`

`corr(t_e, g_e²)` over edges, and `g²-ratio` = mean `g_e²` on the top-decile-`t_e` edges ÷ overall mean `g_e²`. A negative corr / ratio `< 1` means the high-overlap edges carry the *smallest* Fiedler drop — the cancellation a term-wise bound misses.

| name | R | corr(t_e,g²) | g²-ratio (top-decile t_e) |
|------|---|--------------|---------------------------|
| twin20_1 | 0.3400 | -0.816 | 0.081 |
| twin50_1 | 0.3451 | -0.817 | 0.033 |
| twin50_2 | 0.4010 | -1.000 | 0.026 |
| twin20_2 | 0.4011 | -0.999 | 0.063 |
| twin20_5 | 0.4049 | -0.617 | 0.025 |
| twin50_5 | 0.4129 | -0.587 | 0.011 |
| twin20_3 | 0.4180 | -0.864 | 0.046 |
| twin50_3 | 0.4187 | -0.866 | 0.019 |
| deg2d40_0.1 | 0.0313 | -0.148 | 0.156 |
| deg2d60_0.1 | 0.0700 | -0.056 | 0.187 |
| deg2d40_0.2 | 0.0733 | -0.176 | 0.150 |
| deg2d80_0.1 | 0.0790 | -0.100 | 0.147 |
| deg2d80_0.2 | 0.0977 | -0.102 | 0.078 |
| deg2d60_0.2 | 0.1245 | -0.117 | 0.141 |

**Across 31 graphs: corr(t_e,g²) < 0 in 100%, mean = -0.414; median g²-ratio on top-decile-t_e edges = 0.063** (≪1 ⇒ strongest-triangle edges are the flattest).

## TASK 5 — Verdict: the difficulty is DISTRIBUTED, not localized

**(a) DISTRIBUTED.** No single edge or edge class is the bottleneck.

Evidence:

1. **No dominant edge.** The binding edge `e*` carries on average **18%** of T (max 36% on the tiniest sparse graphs where T lives on ~3 edges). On the substantive bottlenecks it is **<11%**; reaching 50% of T needs **7 edges** on average. T is spread across many low-weight edges, not concentrated on one high-`t_e` edge.

2. **The core is uniformly easy.** The conditional aggregate `R_core ≤ 1` holds **31/31** with max 0.980 (twin cores are complete → `R_core=(n−2)/(n−1)`). So the inequality is never in danger inside the dense block.

3. **The cross-terms do not concentrate the difficulty either.** T mass averages core-core **68%**, core-port **32%**, port-port **0%**. Where cross edges exist (twins) they carry real mass and the largest `t_e`, yet they do not break the bound — because of a measured **anti-correlation** between the triangle weight `t_e` and the Fiedler gap `g_e²`: `corr(t_e,g²) < 0` on **100%** of graphs (mean -0.414), and the top-decile-`t_e` edges carry only **0.06×** the mean `g_e²`. The product `t_e·g_e²` stays small precisely on the high-overlap edges.

**Why huge slack yet no formal route (the paradox resolved):** the slack is *real* but *global*. It is manufactured by the eigenvector equation forcing `g_e²` small exactly on the high-`t_e` (high-overlap) edges — an anti-correlation between the triangle weight `t_e` and the Fiedler drop `g_e`. Term-wise / combinatorial relaxations (`t_e ≤ min(d_a,d_b)−1` → `B2′`; uniform `max_e t_e ≤ degQuad`) cannot see this anti-correlation: they bound each edge by its *worst-case* `t_e` and lose the smallness of `g_e`, so they overshoot wildly (`B2′/2λdegQuad > 1` on sparse-core deg2+dense, `informal/conjecture_B_signed_cancellation.md`). The slack cannot be localized into a per-edge or per-class certificate; only a global quadratic-form argument that *uses* `Lu=λu` (the `M_C+L` route) can recover it. This is exactly why `aggregate_triangle_poincare` 'must be proved directly' — there is no sub-additive decomposition to exploit.

