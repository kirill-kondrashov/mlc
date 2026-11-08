# B3 sources

The [targeted publication-novelty screening](research/B3_publication_screening.md)
contains the complete comparison, equivalent map forms, subsequent work,
and public-code audit.

## Closest results and contribution screening

- Bonnot–Braverman–Yampolsky,
  [*Thurston equivalence to a rational map is decidable*, 2010v1](https://arxiv.org/abs/1009.5713v1),
  §2, preprint pp. 3–4: our map and its known invariant equator.
  Use for the initial marking and pullback calibration.
- Bartholdi–Dudko–Pilgrim,
  [*Correspondences on Riemann surfaces and non-uniform hyperbolicity*, 2025v2](https://arxiv.org/abs/2407.15548v2),
  Corollary B, §1.1: attractors with four postcritical points;
  §1.3: strategy for more points. For computations use §§2.5, 5.1 on bisets.
  No ready conclusion for B3 has been obtained from these sections.
- Wu,
  [*On the Global Curve Attractor for polynomial gluing*, 2026v2](https://arxiv.org/abs/2605.00633v2),
  Main Theorem, §§2.2–2.3: gluing two polynomials along finite basins.
  Its inapplicability to B3 and all iterates is proved
  [using local degrees](research/B3_candidate.md).
- Pilgrim,
  [*An algebraic formulation of Thurston's characterization of rational functions*](https://www.numdam.org/article/AFST_2012_6_21_S5_1033_0.pdf),
  Theorem 1.4, printed p. 1039; §§5, 7: the mapping-class virtual
  endomorphism and finite-attractor criterion.
  Our map fails contraction: $\rho(\varphi_F)\ge1$.
  [Complete proof](research/B3_novelty_audit.md), §§4–6.
- Parry–Pilgrim,
  [*Characterizations of contracting Hurwitz bisets*, 2025v1](https://arxiv.org/abs/2506.23222v1),
  Theorems 1.1–1.2, §§2–4, 6.5–6.6: Hurwitz-biset contraction,
  obstructions in its semigroup, and moduli correspondence.
  Strong contraction is excluded for B3; this neither proves nor
  disproves an attractor of the fixed map.
- Pilgrim,
  [*On the pullback relation on curves induced by a Thurston map*, 2021v1](https://arxiv.org/abs/2102.12402v1),
  §§3.3, 4.1: computation of the relation and known mechanisms.
  Use as a reference map to primary theorems.
- Koch–Pilgrim–Selinger,
  [*Pullback invariants of Thurston maps*](https://arxiv.org/abs/1212.4568v1),
  Theorem 7.2: both criteria are excluded for B3 in the publication screening.
- Bonk–Hlushchanka–Lodge,
  [*Thurston's pullback map, invariant covers, and the global dynamics on curves*](https://arxiv.org/abs/2411.00732v1),
  Theorems 1–2, Corollary 6: four marked points.
- Smith,
  [*Curve attractors for marked rational maps*](https://arxiv.org/abs/2401.16636v1),
  Theorems 1.2–1.3: four marked points; §6: future strategy.
- Wang–Zhang,
  [*Polynomial curve systems are exponentially decaying*, 2026v4](https://arxiv.org/abs/2601.04871v4),
  Main Theorem: quantitative curve control for polynomials.

## For the next computation

- Shepelevtseva–Timorin,
  [*Invariant spanning trees for quadratic rational maps*, 2021v4](https://arxiv.org/abs/1808.05489v4),
  §2.2: the formal rabbit–Basilica mating tree;
  Theorem 5.6: its biset construction. Match the model to B3's labels and basis.
- Bartholdi–Dudko I,
  [§2](https://arxiv.org/abs/1512.08539): left-free biset, basis,
  recursion, and basis change. Use to obtain the section words in (C5).
- Bartholdi–Dudko II,
  [§§2, 3.1, 6](https://arxiv.org/abs/1603.04059): sphere bisets,
  multicurves, and mapping class groups. Preserve peripheral classes
  and match the curve pullbacks.
- Farb–Margalit,
  [*A Primer on Mapping Class Groups*](https://doi.org/10.23943/princeton/9780691147949.001.0001),
  §1.2 and §§3.1–3.2: simple curves, Dehn twists, intersection numbers.
  Read the definitions and proofs used for arbitrary-exponent families.

Use Lyubich's [book](https://www.math.stonybrook.edu/~mlyubich/book.pdf)
for a specific analytic step if needed.
Local version: `refs/Lyubich_book_vol_I-II_2023.pdf`.
Mikhailov–Passi,
[*Lower Central and Dimension Series of Groups*](https://link.springer.com/book/10.1007/978-3-540-85818-8),
remains a source on commutators and quotients for the earlier direction.

## Completed comparisons

- [B1-R](../../study/research/B1_novelty_audit.md), [B2-N](../../study/research/B2_novelty_audit.md):
  *p-Basilica Groups*, Lemma 3.2, Theorems 3.3, 4.7(i), 4.10(i),
  Corollary 4.11; exact reductions and links are retained in the audits.
- [B1/B2 prior-art map](../../study/research/B1_prior_art.md).
- [Project bibliography](../../refs/README.md).
