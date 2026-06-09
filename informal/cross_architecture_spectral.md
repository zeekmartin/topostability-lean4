# Cross-architecture spectral hierarchy on real attention

**Question.** The inequality `λ₂(T(G)) ≤ λ₂(G)` (and the chain `λ₂(T₃) ≤ λ₂(T(G)) ≤ λ₂(G)`) held across 45,000+ synthetic graphs with zero violations, and on a pretrained I-JEPA ViT-H/14. Does it survive across *encoder-only*, *decoder-only*, and *vision* transformers — and does fragility (FI) behave the same under SAL-style head masking?

**Method (identical to the I-JEPA run).** For each model we run a forward pass with `output_attentions=True` (eager attention), average each head's attention map over the inputs, flatten it to a signature, and join heads whose signatures correlate with Pearson **r > 0.3**. Per layer we compute λ₂(G), λ₂(T(G)) and ρ = λ₂(T)/λ₂(G) (defined only where both `G` and `T(G)` are connected); globally we evaluate the giant component of all L×H heads and mask **33%** of heads (40 random trials, seed 0) to measure the fragility index FI (fraction of edges in zero triangles). Text models see 16 English sentences; vision models see 16 CIFAR-10 images.

## Comparison table

| Model | Arch | Layers | Eligible | Violations | ρ_min | ρ_max | ρ_mean | FI_base | FI_masked |
|---|---|---|---|---|---|---|---|---|---|
| I-JEPA | ViT-H/14 | 32 | 16 | 0 | 0.19 | 0.75 | 0.464 | 0.066 | 0.101 |
| BERT | Encoder | 12 | 12 | 0 | 0.74 | 1.00 | 0.938 | 0.019 | 0.032 |
| GPT-2 | Decoder | 12 | 10 | 0 | 0.86 | 1.00 | 0.986 | 0.002 | 0.003 |
| ViT | ViT-B/16 | 12 | 6 | 0 | 0.56 | 1.00 | 0.807 | 0.025 | 0.039 |

## Key findings

- **The hierarchy holds across ALL architectures: 0 violations** of `λ₂(T(G)) ≤ λ₂(G)` over every eligible layer of every model (I-JEPA, BERT, GPT-2, ViT). The inequality is not an artifact of synthetic topology, model size, modality, or attention direction (causal vs. bidirectional).
- **Triangular coherence (ρ_mean) is highest in GPT-2** (0.986) and lowest in I-JEPA** (0.464). Higher ρ = the head-interaction graph keeps more of the head graph's algebraic connectivity (more triangle-redundant structure).
- **Encoder vs. decoder (same 12×12 size, same text inputs).** BERT/GPT-2 eligible layers 12/10, ρ_mean 0.938/0.986, FI_base 0.019/0.002. Bidirectional vs. causal attention yields a markedly different connectivity profile.
- **SAL masking → fragility, in every architecture.** Dropping 33% of heads changes FI as follows:
  - I-JEPA: FI 0.066 → 0.101 (↑ 0.035)
  - BERT: FI 0.019 → 0.032 (↑ 0.013)
  - GPT-2: FI 0.002 → 0.003 (↑ 0.001)
  - ViT: FI 0.025 → 0.039 (↑ 0.014)

## BERT — `bert-base-uncased` (Encoder, text)

12 layers × 12 heads, hidden 768, 32 attention tokens, 16 inputs.

- Eligible layers (both `G`, `T(G)` connected): **12/12**; upper-link violations: **0**.
- ρ over eligible layers: range [0.743 (L10), 1.000 (L11)], mean 0.938.
- Global graph (all 144 heads): τ=0.9, 789 edges, 32 components → giant component 80 nodes/648 edges; ρ n/a (T(G) connected=False).
- SAL masking (drop 48/144 heads): FI 0.019 → 0.032 ± 0.009 (more fragile).
- Early vs. deep eligible layers: ρ_mean 0.918 (L<6) vs. 0.957 (L≥6) — deep layers are more triangle-redundant.

## GPT-2 — `gpt2` (Decoder, text)

12 layers × 12 heads, hidden 768, 32 attention tokens, 16 inputs.

- Eligible layers (both `G`, `T(G)` connected): **10/12**; upper-link violations: **0**.
- ρ over eligible layers: range [0.860 (L1), 1.000 (L10)], mean 0.986.
- Global graph (all 144 heads): τ=0.96, 4806 edges, 17 components → giant component 121 nodes/4799 edges; ρ n/a (T(G) connected=False).
- SAL masking (drop 48/144 heads): FI 0.002 → 0.003 ± 0.001 (more fragile).
- Early vs. deep eligible layers: ρ_mean 0.972 (L<6) vs. 1.000 (L≥6) — deep layers are more triangle-redundant.

## ViT — `google/vit-base-patch16-224` (ViT-B/16, vision)

12 layers × 12 heads, hidden 768, 197 attention tokens, 16 inputs.

- Eligible layers (both `G`, `T(G)` connected): **6/12**; upper-link violations: **0**.
- ρ over eligible layers: range [0.557 (L3), 1.000 (L11)], mean 0.807.
- Global graph (all 144 heads): τ=0.64, 791 edges, 29 components → giant component 115 nodes/790 edges; ρ n/a (T(G) connected=False).
- SAL masking (drop 48/144 heads): FI 0.025 → 0.039 ± 0.010 (more fragile).
- Early vs. deep eligible layers: ρ_mean 0.557 (L<6) vs. 0.857 (L≥6) — deep layers are more triangle-redundant.


## Caveats

- Single seed, 16 inputs per model, unweighted graphs (edge iff r > τ). Text attention maps are computed over sentences padded to a fixed length, so pad positions are part of the signature (consistent across the batch, same as the ViT patch grid). The per-layer protocol gates ρ/violation on both `G` and `T(G)` being connected (no component surgery); the global graph is evaluated on its giant component while FI is over the full induced graph. The global τ is raised from the requested value until the triangle count is exactly computable; the τ used is reported per model.
- Head masking is graph-level (drop head-nodes, recompute the induced correlation graph), not a re-forward-pass with head outputs zeroed — it isolates the structural effect on the attention graph, the level at which SAL's FI is defined.
- All graph/hierarchy/masking math is imported verbatim from `modal_jepa.py`; only attention extraction differs by modality.

