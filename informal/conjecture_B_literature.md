# Conjecture B — literature: is "Fiedler flat at high-degree vertices" known?

Track B of the two-track push. The Track A analysis
([`conjecture_B_proof_v4.md`](conjecture_B_proof_v4.md)) reduced the open lock to
a single **hub-flatness** statement: the Fiedler vector `f` (`L_G f = λ₂ f`) has
small value and small gradient at high-degree vertices
(`corr(deg, f²) ≈ −0.8`, `corr(deg, per-edge gradient) ≈ −0.7`). This document
searches the literature for that phenomenon and for tools that could prove it.

**Bottom line.** No published theorem states "the Fiedler vector is flat at
high-degree vertices." The well-known **hub-localization** results are for the
**opposite end of the spectrum** (largest eigenvalues), where eigenvectors are
*large* at hubs. The closest supporting evidence is (a) Fiedler **extreme-value**
results on trees (extremes occur at **degree-1** vertices) and (b) general
low-frequency **smoothness / delocalization**. A quantitative hub-flatness bound
for `λ₂` would be, as far as this search found, **new**.

---

## 1. Fiedler-vector localization and degree sequence

- **Localization from degree fluctuations.** In spectral partitioning, localized
  eigenvectors "emerge because of degree fluctuations… weight concentrated around
  a few defects, the vertices with characteristic degrees," especially in sparse
  graphs with bimodal degree distributions
  ([Kawamoto–Kabashima, arXiv:1502.06775](https://arxiv.org/pdf/1502.06775)).
  This concerns *localization* (concentration), not the *gradient-flatness at
  hubs* we need, and is a sparse/threshold phenomenon.
- **Fiedler perturbation** under graph changes is studied
  ([arXiv:2306.04327](https://arxiv.org/pdf/2306.04327)) but gives no
  degree-vs-gradient bound.

**Relevance:** tangential — localization ≠ the smoothness-at-hubs we need.

## 2. Eigenvector "flat/small at hubs" — but only at the TOP of the spectrum

- **Hub-driven high-lying eigenvectors.** Very high-degree vertices "give rise to
  high-lying, localized eigenvectors" with "very large vector elements for these
  hub vertices and small elements for all other vertices"
  ([Newman et al., spectral community detection, arXiv:1307.7729](https://arxiv.org/pdf/1307.7729);
  [largest Laplacian eigenvalue, arXiv:1502.04207](https://arxiv.org/pdf/1502.04207);
  [spectra with arbitrary expected degrees, arXiv:1208.1275](https://arxiv.org/pdf/1208.1275)).

**Relevance:** this is the **opposite** of what we need. At the *top* of the
spectrum the eigenvector is **large** at hubs; we need the *bottom* (Fiedler),
where empirically it is **small** at hubs. These hub-localization theorems do
**not** transfer to `λ₂`.

## 3. Nodal domains and degree

- **Courant / Fiedler:** the eigenvector of the `k`-th eigenvalue has ≤ `k` nodal
  domains; the Fiedler vector has exactly **2** sign-domains (generically)
  ([Biyikoglu–Leydold–Stadler, *Graph Laplacians, Nodal Domains, Hyperplane
  Arrangements*](https://www.tbi.univie.ac.at/newpapers/Abstracts/02-09-046.pdf);
  [arXiv:1007.4132](https://arxiv.org/pdf/1007.4132)).
- **Random graphs:** for `G(n,p)`, non-leading eigenvectors have exactly two
  nodal domains of nearly equal size
  ([arXiv:1905.00447](https://arxiv.org/pdf/1905.00447)).

**Relevance:** consistent with our finding that the Fiedler cut carries the large
gradients — **but** the Track A data show cut edges are **not** lower-degree, so
nodal-domain structure alone does not produce the degree–gradient anticorrelation
(A3 was refuted). No nodal-domain result ties sign-crossings to vertex degree in
the needed way.

## 4. Delocalization on irregular graphs

- **Bulk delocalization.** For critical/sparse Erdős–Rényi graphs the spectrum has
  a delocalized bulk (eigenvector entries of similar magnitude) and semilocalized
  edges ([Erdős–Rényi delocalization, PMC8550299](https://www.ncbi.nlm.nih.gov/pmc/articles/PMC8550299/);
  [graph uncertainty principle & delocalization, arXiv:2306.15810](https://arxiv.org/html/2306.15810)).
- **Bilu–Linial / Ramanujan:** existence of near-optimal-spectral-gap irregular
  (bipartite) graphs via 2-lifts / interlacing families
  ([Marcus–Spielman–Srivastava](https://www.cs.yale.edu/homes/spielman/PAPERS/Marcus_Spielman_SrivastavaIFI.pdf)).

**Relevance:** delocalization says entries are *comparable*, not that gradients are
*small at hubs*. It bounds extremes, not the degree-weighted gradient profile.

## 5. Triangle-weighted / common-neighbour Dirichlet forms vs λ₂

- No result was found bounding `Σ_{ab} t_{ab}(f_a−f_b)²` (triangle/common-neighbour
  weights) or the min-degree-weighted form by `λ₂`. Lower bounds on `λ₂` itself are
  few and "far from sharp"
  ([de Abreu survey](https://www.math.ucdavis.edu/~saito/data/graphlap/deabreu-algconn.pdf);
  [Laplacian eigenvalues survey, arXiv:1111.2897](https://arxiv.org/pdf/1111.2897)),
  with the only directly usable classical fact being `λ₂ ≤ δ`.

---

## The one genuinely supportive result, and the tools

- **Fiedler extreme values on trees** occur at **degree-1 (pendant) vertices**, and
  the Fiedler vector is monotonic along branches
  ([*Extreme values of the Fiedler vector on trees*, PMC11619034](https://pmc.ncbi.nlm.nih.gov/articles/PMC11619034/)).
  This is the **only** found result pointing the right way: the extremes of `f` sit
  at **low-degree** vertices — exactly our `corr(deg, f²) < 0`. It is restricted to
  trees, but it is the natural seed for a general hub-flatness statement.

- **Tools that might prove the lock (none give it directly):**
  - the **normalized Laplacian** `L = I − D^{-1/2}AD^{-1/2}` / random-walk view:
    low-frequency eigenvectors are "smooth" w.r.t. the random walk, which weights
    by degree — a promising reframing of hub-flatness;
  - the **Trevisan sweep / improved Cheeger** machinery (already in this repo's
    Paper 12 lineage) localizes spectral mass along the Fiedler order and may bound
    `D_v⁺` per level set;
  - **eigenvector perturbation** (degree as a diagonal perturbation of a regular
    base) to transfer the trivially-true regular case to the irregular one.

---

## Conclusion

The hub-flatness phenomenon we need (Fiedler gradient small at high-degree
vertices) is **empirically robust but not a named theorem**. The literature's
hub results concern the *opposite* spectral end; the only aligned rigorous result
is the trees extreme-value theorem. Proving the reduced lock
(`Σ_v(d_v−δ)D_v⁺ ≤ R''`) therefore appears to require a **new** quantitative
hub-flatness lemma for `λ₂`, most plausibly via the normalized-Laplacian /
random-walk smoothness route or a Trevisan-style level-set argument — not an
off-the-shelf citation.

### Sources
- [Localization of eigenvectors in spectral partitioning (arXiv:1502.06775)](https://arxiv.org/pdf/1502.06775)
- [Perturbation of the Fiedler vector (arXiv:2306.04327)](https://arxiv.org/pdf/2306.04327)
- [Spectral methods for community detection / hub eigenvectors (arXiv:1307.7729)](https://arxiv.org/pdf/1307.7729)
- [Largest eigenvalue of the Laplacian (arXiv:1502.04207)](https://arxiv.org/pdf/1502.04207)
- [Spectra of graphs with arbitrary expected degrees (arXiv:1208.1275)](https://arxiv.org/pdf/1208.1275)
- [Graph Laplacians, Nodal Domains, Hyperplane Arrangements (Biyikoglu–Leydold–Stadler)](https://www.tbi.univie.ac.at/newpapers/Abstracts/02-09-046.pdf)
- [Nodal domains of G(n,p) eigenvectors (arXiv:1905.00447)](https://arxiv.org/pdf/1905.00447)
- [λ₂ multiplicity and Courant nodal theorem (arXiv:1007.4132)](https://arxiv.org/pdf/1007.4132)
- [Erdős–Rényi delocalization transition (PMC8550299)](https://www.ncbi.nlm.nih.gov/pmc/articles/PMC8550299/)
- [Graph uncertainty principle & eigenvector delocalization (arXiv:2306.15810)](https://arxiv.org/html/2306.15810)
- [Interlacing families / Ramanujan graphs (Marcus–Spielman–Srivastava)](https://www.cs.yale.edu/homes/spielman/PAPERS/Marcus_Spielman_SrivastavaIFI.pdf)
- [Extreme values of the Fiedler vector on trees (PMC11619034)](https://pmc.ncbi.nlm.nih.gov/articles/PMC11619034/)
- [Old and new results on algebraic connectivity (de Abreu)](https://www.math.ucdavis.edu/~saito/data/graphlap/deabreu-algconn.pdf)
- [The Laplacian eigenvalues of graphs: a survey (arXiv:1111.2897)](https://arxiv.org/pdf/1111.2897)
