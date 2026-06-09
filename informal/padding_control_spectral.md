# Padding-artifact control: does no-padding change ρ?

**Concern.** The cross-architecture run fed text models sentences **padded to a fixed length** and got ρ_mean = 0.986 (GPT-2) and 0.938 (BERT) — far above the vision models. Pad-position attention is similar across heads, so averaging padded maps may inflate head-to-head correlation toward complete graphs (ρ → 1). This test removes padding: each text is processed **individually at its native length** (batch 1, no pad), the head–head correlation matrix is built per text and **averaged across texts** (you can't average maps of different lengths). All hierarchy math is imported verbatim from `modal_jepa.py`; threshold r > 0.3.

## Bottom line

- **ρ does NOT collapse without padding.** GPT-2 dips 0.986 → 0.915 (-0.071); BERT is flat (0.938 → 0.951, +0.013). Both stay far above the vision range (ViT 0.81, I-JEPA 0.46). The text↔vision coherence gap is **real, not a padding artifact** — at most padding added a small (~0.07) inflation to GPT-2.
- **The entropy test refutes the uniformity mechanism.** Pooled Pearson(entropy, ρ) = **-0.801** (strongly NEGATIVE) — the OPPOSITE of the padding prediction. High-ρ text attention is more **focused** (low entropy ≈0.47-0.52), not more uniform (vision ≈0.71-0.87). High ρ comes from heads sharing a common focused pattern (attention sinks / locality), not from pad-induced uniformity.
- **Hierarchy holds:** 0 violations of `λ₂(T(G)) ≤ λ₂(G)` in every condition, padded or not.

## Summary table

| Model | Condition | ρ_mean | ρ_min | ρ_max | Eligible | Violations |
|---|---|---|---|---|---|---|
| GPT-2 | padded (baseline) | 0.986 | 0.86 | 1.00 | 10 | 0 |
| GPT-2 | no-pad, same text | 0.915 | 0.60 | 1.00 | 11 | 0 |
| GPT-2 | no-pad, varying len | 0.931 | 0.64 | 1.00 | 11 | 0 |
| GPT-2 | no-pad, diverse | 0.885 | 0.50 | 1.00 | 11 | 0 |
| BERT | padded (baseline) | 0.938 | 0.74 | 1.00 | 12 | 0 |
| BERT | no-pad, same text | 0.951 | 0.61 | 1.00 | 8 | 0 |
| BERT | no-pad, varying len | 0.932 | 0.46 | 1.00 | 8 | 0 |

## Does ρ drop without padding?

- **GPT-2, same 16 sentences (the clean control):** padded ρ_mean 0.986 → no-pad ρ_mean 0.915 (**-0.071**). Removing padding **lowers** ρ — the padded value was (partly) a padding artifact.
- **BERT, same 16 sentences:** padded ρ_mean 0.938 → no-pad ρ_mean 0.951 (**+0.013**). Removing padding barely moves ρ.
- **GPT-2 content sensitivity (no-pad):** same-text 0.915, varying-length 0.931, diverse-genre 0.885. ρ is fairly stable across content.
- **Hierarchy integrity:** **0** violations of `λ₂(T(G)) ≤ λ₂(G)` across all conditions in the table — the inequality holds everywhere regardless of padding.

## TEST 4 — attention entropy vs. ρ

Per layer, mean **normalised** attention entropy (1 = uniform attention over a row's support, 0 = fully focused), paired with that layer's ρ over eligible layers. The padding hypothesis predicts a **positive** entropy↔ρ correlation (uniform heads → indistinguishable → complete graph → ρ→1).

| Model (condition) | layers paired | mean entropy | Pearson(entropy, ρ) |
|---|---|---|---|
| GPT-2 (no-pad, same) | 11 | 0.470 | -0.563 |
| BERT (no-pad, same) | 8 | 0.524 | -0.651 |
| ViT | 6 | 0.707 | -0.119 |
| I-JEPA | 16 | 0.865 | -0.262 |
| **pooled (all 4)** | 41 | — | -0.801 |

- Pooled Pearson(entropy, ρ) = **-0.801** (negative): **contradicts** the simple uniformity story — more focused attention goes with higher ρ here.
- Mean normalised entropy by model: I-JEPA 0.865, ViT 0.707, BERT (no-pad, same) 0.524, GPT-2 (no-pad, same) 0.470 — higher = more uniform attention.

## Per-condition detail

### GPT-2 — no-pad, same 16 sentences

- Token lengths (native, no pad): min 10, max 15, mean 12.2.
- Eligible layers: **11/12**; violations: **0**; ρ_mean 0.915 (range [0.60, 1.00]).
- Global graph: τ=0.96, 1745 edges, 68 components; FI(base) 0.003.
- SAL mask 48/144: FI 0.003 → 0.004.

### GPT-2 — no-pad, varying length

- Token lengths (native, no pad): min 4, max 93, mean 34.7.
- Eligible layers: **11/12**; violations: **0**; ρ_mean 0.931 (range [0.64, 1.00]).
- Global graph: τ=0.96, 1301 edges, 83 components; FI(base) 0.003.
- SAL mask 48/144: FI 0.003 → 0.004.

### GPT-2 — no-pad, diverse genres

- Token lengths (native, no pad): min 29, max 56, mean 40.1.
- Eligible layers: **11/12**; violations: **0**; ρ_mean 0.885 (range [0.50, 1.00]).
- Global graph: τ=0.96, 524 edges, 90 components; FI(base) 0.021.
- SAL mask 48/144: FI 0.021 → 0.026.

### BERT — no-pad, same 16 sentences

- Token lengths (native, no pad): min 12, max 17, mean 13.9.
- Eligible layers: **8/12**; violations: **0**; ρ_mean 0.951 (range [0.61, 1.00]).
- Global graph: τ=0.84, 556 edges, 60 components; FI(base) 0.032.
- SAL mask 48/144: FI 0.032 → 0.045.

### BERT — no-pad, varying length

- Token lengths (native, no pad): min 6, max 100, mean 37.0.
- Eligible layers: **8/12**; violations: **0**; ρ_mean 0.932 (range [0.46, 1.00]).
- Global graph: τ=0.8, 678 edges, 57 components; FI(base) 0.015.
- SAL mask 48/144: FI 0.015 → 0.029.

## Caveats

- No-pad signatures are built by **averaging per-text head–head correlation matrices** (each text at its native length), not by averaging attention maps; this is the only way to drop padding when texts differ in length, and it changes the aggregation order vs. the padded baseline. The padded baseline rows are carried over from `cross_architecture_spectral.json` (average-maps protocol).
- Short texts yield small (L²-dim) signatures, so their per-text correlations are noisier; the average over 16 texts smooths this.
- Normalised entropy divides each attention row's entropy by log(#valid keys) so causal (GPT-2) and bidirectional (BERT/ViT) models are comparable; rows with <2 valid keys (causal position 0) are skipped.
- Single seed, 16 texts/images per condition, unweighted graphs. All graph/hierarchy/masking math imported verbatim from `modal_jepa.py`.

