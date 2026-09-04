# Audit summary: Pacman renormalization and noncommutative motives

The note compares Pacman renormalization with BGT universal localizing
motives and Efimov's rigid relative localizing motives. The categorical
Pacman construction and its parameter realization are additional data; they
are not consequences of the universal properties of motives.

## Source inventory

The source files are committed under `refs/`:

| arXiv | Version | Extracted source | Archive/metadata |
|---|---:|---|---|
| [2510.17010](https://arxiv.org/abs/2510.17010) | v1 | `arxiv-2510.17010/Rigidity_Mot_loc.tex` | `arxiv-2510.17010-source.tar.gz`, `arxiv-2510.17010.xml` |
| [2502.04123](https://arxiv.org/abs/2502.04123) | v2 | `arxiv-2502.04123.tex` | `arxiv-2502.04123-source.tex.gz`, `arxiv-2502.04123.xml` |
| [2603.08653](https://arxiv.org/abs/2603.08653) | v2 | `arxiv-2603.08653/K_theory_ab_cats.tex` | `arxiv-2603.08653-source.tar.gz`, `arxiv-2603.08653.xml` |

The source inventory and the extracted files are intentionally kept in the
repository so the research plan does not depend on copies outside the
worktree.

## What the three papers actually provide

### Efimov, *Rigidity of the category of localizing motives*

The introduction states that the universal finitary localizing invariant
`U_loc : Cat^perf -> Mot^loc` has mapping spectra recovering nonconnective
`K`-theory, and proves rigidity of `Mot^loc`
(`Rigidity_Mot_loc.tex`, lines 505--552). The relative theorem gives the same
rigidity for motives over a rigid monoidal base (line 552 onward). The main
technical consequences relevant here are:

- dualizable/nuclear modules and trace-class refinement maps;
- inverse-limit descriptions of morphisms in localizing motives
  (`th:morphisms_in_Mot^loc_via_limits`, around lines 1931--2012);
- internal-Hom descriptions through Calkin categories and `K`-theory.

These results can organize a Pacman refinement tower once such a tower has
been constructed as a tower of dualizable stable categories. They do not
construct a Pacman category, a renormalization functor, a parameter locus, or
a map to the complex parameter plane.

### Efimov, *Localizing invariants of inverse limits*

The paper identifies continuous `K`-theory of suitable dualizable inverse
limits with inverse limits of `K`-theory spectra. The relevant hypotheses are
strong Mittag--Leffler conditions and a homological-epimorphism statement,
not merely the existence of an inverse diagram
(`arxiv-2502.04123.tex`, `def:strong_ML`, `th:hom_epi_for_ML`, and
`th:local_invar_of_inverse_limits`). In particular,
`cor:K_theory_of_limit_of_ML` gives

```text
K^cont(lim^dual C_n) ≃ lim K^cont(C_n)
```

for a strongly Mittag--Leffler sequence.

This is a credible tool for a future categorical renormalization tower:
finite-level Pacman models could be approximated by `C_n`, and their
`K_n`- or localizing-invariant data could be compared through the tower.
The theorem has no conclusion about connectedness of a realization in
`TopCat / ℂ`, and it does not supply the required Mittag--Leffler or
realization hypotheses.

### Efimov, *Theorem of the heart for Weibel's homotopy K-theory*

The paper proves the theorem of the heart for `KH` for dualizable
`t`-categories and gives coconnectivity estimates controlled by Ext groups
(`K_theory_ab_cats.tex`, `th:theorem_of_the_heart_for_KH`,
`th:coconnectivity_estimates`, and `th:devissage_for_K_and_KH`). These results
are useful only after a Pacman model has been given a stable category,
compatible `t`-structure, and a coherently assembled heart. No such
structure exists in the repository, and the results do not convert a
`K`/`KH` equivalence into a topological connectedness theorem.

## Exact relation to the MLC frontier

The current frontier is the categorical form of

```text
{c' | green_function c (c' - c) < 2^(-n)} ∩ MandelbrotSet
```

in the straddling case. It is equivalent to the existing set-level
statement by `greenSublevelIntersectionCategoricalData_iff`. The repository
already proves the connected un-intersected Green-sublevel translate and
reduces the remaining step to the carving interface
`ParaPieceCarvedByMotion` in `Mlc/ParaPuzzleCarvingReduction.lean`.

Efimov's results leave three independent bridges to be proved:

1. **Model bridge.** Construct marked Pacman models, morphisms, spectral
   enhancements, perfect/dualizable stable categories, and refinement maps.
2. **Realization bridge.** Construct a realization functor to
   `TopCat / ℂ` and prove that the realized finite-level locus is exactly the
   Green-sublevel/Mandelbrot pullback.
3. **Connectivity bridge.** Prove that the realization of the relevant
   categorical construction is a connected image, or otherwise prove the
   `ParaPieceCarvedByMotion` statement.

Only the first bridge is in the natural scope of noncommutative motives.
The second and third are the Douady--Hubbard/Yoccoz phase--parameter
correspondence. A localizing invariant is additive/exact and can detect
categorical differences; it does not by itself detect connectedness of a
subset of the parameter plane. In particular, a `K_n` equivalence cannot be
used as a connectedness proof without a new conservative realization theorem.

## Decision for the current Lean development

The Efimov papers do not discharge
`MLC.green_sublevel_intersection_categorical`. No new axiom or opaque
K-theoretic substitute is introduced. The sound near-term target is a
conditional interface that packages:

- a strongly Mittag--Leffler Pacman refinement tower;
- its realization as an approximation in `TopCat / ℂ`;
- an equality between the realized parameter locus and the current pullback;
- a space-holomorphic carving map from the already-connected Green-sublevel
  translate.

The final item is precisely the existing `ParaPieceCarvedByMotion` target.
Once it is supplied by genuine dynamics, the existing connected-image theorem
discharges the frontier. Until then, Efimov's results organize a possible
later $K_n$ layer but do not reduce the checked axiom count.

## Existing note scope

The proposed finite marked-model system still contains:

- marked Pacman models and morphisms;
- spectral enhancements and perfect stable categories;
- refinement functors;
- a categorical renormalization endofunctor;
- parameter loci `Q_n(P)` defined by a separate realization predicate.

Connectedness, compactness, nesting, and an MLC-compatible neighborhood basis
for `Q_n(P)` remain open construction problems. In particular, no theorem in
the three Efimov sources identifies a `Q_n(P)` with the frozen Green-sublevel
intersection above.

Related background:

- BGT, *A universal characterization of higher algebraic K-theory*;
- the existing Pacman bridge note and `Mlc/ParaPuzzleCarvingReduction.lean`;
- `Mlc/CategoricalTopologicalApproximation.lean` for the current
  over-category/pullback formalization.
