# Audit summary: Pacman renormalization and noncommutative motives

The note compares Pacman renormalization with BGT universal localizing
motives and Efimov's rigid relative localizing motives. The categorical
Pacman construction and its parameter realization are additional data; they
are not consequences of the universal properties of motives.

## Source inventory

The source files are committed under `refs/`:

| arXiv | Version | Extracted source | Archive/metadata |
|---|---:|---|---|
| [2405.12169](https://arxiv.org/abs/2405.12169) | v3 | `arxiv-2405.12169/Continuous_K_theory.tex` | `arxiv-2405.12169-source.tex.gz`, `arxiv-2405.12169.xml` |
| [2502.04123](https://arxiv.org/abs/2502.04123) | v2 | `arxiv-2502.04123.tex` | `arxiv-2502.04123-source.tex.gz`, `arxiv-2502.04123.xml` |
| [2505.13260](https://arxiv.org/abs/2505.13260) | v2 | `arxiv-2505.13260/Devissage.tex` | `arxiv-2505.13260-source.tar.gz`, `arxiv-2505.13260.xml` |
| [2510.17010](https://arxiv.org/abs/2510.17010) | v1 | `arxiv-2510.17010/Rigidity_Mot_loc.tex` | `arxiv-2510.17010-source.tar.gz`, `arxiv-2510.17010.xml` |
| [2603.08653](https://arxiv.org/abs/2603.08653) | v2 | `arxiv-2603.08653/K_theory_ab_cats.tex` | `arxiv-2603.08653-source.tar.gz`, `arxiv-2603.08653.xml` |

The source inventory and the extracted files are intentionally kept in the
repository so the research plan does not depend on copies outside the
worktree.

## What the five relevant papers actually provide

### Efimov, *K-theory and localizing invariants of large categories*

The new source `arxiv-2405.12169/Continuous_K_theory.tex` defines continuous
nonconnective `K`-theory for dualizable presentable stable infinity-categories
and proves its universal extension property for localizing invariants
(`th:main_intro`, around lines 521--531). It also computes the invariant on
sheaves over locally compact Hausdorff spaces, including the finite-CW
comparison (`cor:sheaves_on_finite_CW_complexes_intro`, around lines 533--536).

This is the strongest new structural input for the repository's proposed
layer: a genuine Pacman category could carry `K^cont`, and a sheaf-valued
realization could produce a space-indexed invariant. Neither result supplies
a Pacman category, a parameter map, or a criterion that makes `K^cont`
conservative for connectedness of a subset of `\mathbb C`.

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

### Efimov, *Some remarks on Quillen's Dévissage theorem*

The source `arxiv-2505.13260/Devissage.tex` proves a short-exact-sequence
construction for quasi-abelian categories and derives `K`-theory
dévissage from the theorem of the heart (`th:key_construction_intro` and
`th:Barwick`, around lines 476--530). This can help construct the hearts and
finite-stage comparison functors of a future stable Pacman model, but it has
no parameter-plane or dynamical conclusion.

### Efimov, *Theorem of the heart for Weibel's homotopy K-theory*

The paper proves the theorem of the heart for `KH` for dualizable
`t`-categories and gives coconnectivity estimates controlled by Ext groups
(`K_theory_ab_cats.tex`, `th:theorem_of_the_heart_for_KH`,
`th:coconnectivity_estimates`, and `th:devissage_for_K_and_KH`). These results
are useful only after a Pacman model has been given a stable category,
compatible `t`-structure, and a coherently assembled heart. No such
structure exists in the repository, and the results do not convert a
`K`/`KH` equivalence into a topological connectedness theorem.

## Breadth/depth search completed on 2026-09-04

The author search was cross-checked against Alexander I. Efimov's
[Google Scholar profile](https://scholar.google.com/citations?user=fSukKOwAAAAJ&hl=en)
and the arXiv author feed. The feed reports `2603.08653v2` as the newest
relevant result and also identifies `2405.12169v3` and `2505.13260v2`,
which are now archived above.

The five extracted TeX sources were searched for the exact MLC-side concepts
`Mandelbrot`, `Julia`, `Green`, `renormalization`, `holomorphic motion`,
`connectedness`, `local connectivity`, `Douady`, `Yoccoz`, `dynamical`, and
`parameter plane`. There are no matches. This is a source-level check, not a
claim that the papers are informal: the papers contain complete proofs of
their stated categorical and `K`-theoretic theorems, but none states the
missing parameter carving theorem.

The only viable Efimov-driven proof architecture is therefore:

1. Construct actual dualizable stable Pacman levels and strongly continuous
   transition functors.
2. Verify Efimov's strong Mittag--Leffler conditions, including the
   homological-epimorphism hypothesis needed by
   `th:local_invar_of_inverse_limits`.
3. Apply `K^cont` or another accessible localizing invariant, with
   `KH`/dévissage used only when a compatible bounded or coherently assembled
   `t`-structure has been built.
4. Independently construct a conservative realization into
   `Over (TopCat.of \mathbb C)` and prove that its image is exactly the
   Green-sublevel/Mandelbrot intersection.
5. Use a connected-source image theorem to finish the frontier.

Steps 1--3 are the legitimate Efimov contribution. Steps 4--5 are still
Douady--Hubbard/Yoccoz dynamics and are not consequences of any theorem in
the five sources.

## Exact relation to the MLC frontier

The current frontier is the categorical form of

```text
{c' | green_function c (c' - c) < 2^(-n)} ∩ MandelbrotSet
```

in the straddling case. It is equivalent to the existing set-level
statement by `greenSublevelIntersectionCategoricalData_iff`. The repository
already proves the connected un-intersected Green-sublevel translate. The
remaining checked declaration is the explicit axiom
`MLC.green_sublevel_intersection_categorical` in
`Mlc/ParaPuzzleConnectivity.lean`. The new
`Mlc/EfimovCategoricalBridge.lean` names the missing input as
`SpaceHolomorphicCarvingData`: its source is fixed to the connected
translated Green sublevel, and it requires an actual differentiable map and
an exact image equality with the intersection. The module does not provide an
instance of that data.

Efimov's results leave three independent bridges to be proved:

1. **Model bridge.** Construct marked Pacman models, morphisms, spectral
   enhancements, perfect/dualizable stable categories, and refinement maps.
2. **Realization bridge.** Construct a realization functor to
   `TopCat / ℂ` and prove that the realized finite-level locus is exactly the
   Green-sublevel/Mandelbrot pullback.
3. **Connectivity bridge.** Prove that the realization of the relevant
   categorical construction is a connected image, or otherwise prove the
   corresponding Douady--Hubbard/Yoccoz carving statement.

Only the first bridge is in the natural scope of noncommutative motives.
The second and third are the Douady--Hubbard/Yoccoz phase--parameter
correspondence. A localizing invariant is additive/exact and can detect
categorical differences; it does not by itself detect connectedness of a
subset of the parameter plane. In particular, a `K_n` equivalence cannot be
used as a connectedness proof without a new conservative realization theorem.

## Finite-etale `K₀` component shadow

The current Lean development now isolates the smallest consequence of a
degree-zero finite-etale/localizing invariant that is relevant to the
frontier. In `Mlc/EfimovCategoricalBridge.lean`,

```lean
abbrev FiniteEtaleKZeroProbe (S : Set ℂ) := LocallyConstant S Bool
```

is used as a component probe. For nonempty `S`, Mathlib proves the exact
equivalence

```text
IsConnected S ↔ every `FiniteEtaleKZeroProbe S` is constant.
```

This is deliberately not identified with actual algebraic or continuous
`K₀`: it is the finite-etale two-point shadow, where a nonconstant probe is a
clopen decomposition. The proof forwards to the standard locally-constant
and preconnectedness APIs, so it adds no project axiom.

Two Efimov-shaped obligations are exposed over this probe:

- `FiniteEtaleKZeroDescentData` requires every target probe to descend to a
  connected finite stage of an inverse system. This is the topological
  component analogue of strong Mittag--Leffler descent.
- `FiniteEtaleKZeroRestrictionSurjective` requires restriction from the
  connected translated Green sublevel to the target intersection to be
  surjective. With the target's existing nonemptiness and the ambient
  connectedness theorem, restriction-surjectivity is proved equivalent to
  target connectedness. Hence
  `greenSublevelIntersectionCategoricalData_iff_finiteEtaleKZeroExcisionData`
  is an exact relative-excision reformulation, not a weaker substitute.

`EfimovGreenSublevelKZeroBridge` packages this component data alongside the
rigid tower, strong-Mittag--Leffler fields, graded invariant, limit comparison,
and `TopCat` realization. The package sharpens the missing input but does not
instantiate it: Efimov's papers still do not provide the Mandelbrot
realization, the restriction-surjectivity proof, or the
Douady--Hubbard/Yoccoz carving theorem. The checked root axiom set therefore
remains unchanged.

## Decision for the current Lean development

The Efimov papers do not discharge
`MLC.green_sublevel_intersection_categorical`. No new axiom or opaque
K-theoretic substitute is introduced. The sound conditional interface is now
implemented in `Mlc/EfimovCategoricalBridge.lean` and packages:

- a strongly Mittag--Leffler Pacman refinement tower;
- its realization as an approximation in `TopCat / ℂ`;
- an equality between the realized parameter locus and the current pullback;
- a space-holomorphic carving map from the already-connected Green-sublevel
  translate, together with a proof that its image is the current pullback.

Once these data are supplied by genuine dynamics, the standard connected-image
argument can discharge the frontier. Until then, Efimov's results organize a
possible later $K_n$ layer but do not reduce the checked axiom count.

## Existing note scope

The proposed finite marked-model system still contains:

- marked Pacman models and morphisms;
- spectral enhancements and perfect stable categories;
- refinement functors;
- a categorical renormalization endofunctor;
- parameter loci `Q_n(P)` defined by a separate realization predicate.

Connectedness, compactness, nesting, and an MLC-compatible neighborhood basis
for `Q_n(P)` remain open construction problems. In particular, no theorem in
the five Efimov sources identifies a `Q_n(P)` with the frozen Green-sublevel
intersection above.

Related background:

- BGT, *A universal characterization of higher algebraic K-theory*;
- this Pacman bridge note and `Mlc/ParaPuzzleConnectivity.lean` for the
  checked categorical frontier;
- `Mlc/CategoricalTopologicalApproximation.lean` for the current
  over-category/pullback formalization.
