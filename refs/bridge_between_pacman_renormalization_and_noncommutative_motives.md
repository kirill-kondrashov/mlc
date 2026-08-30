# External bridge note: Pacman renormalization and noncommutative motives

Source:
https://github.com/kirill-kondrashov/raw/blob/fix_render_bridge_pacman/bridge_between_pacman_renormalization_and_noncommutative_motives.md

Retrieved and audited on 2026-08-30.

## Scope

The note compares Pacman renormalization with BGT universal localizing motives
and Efimov's rigid relative localizing motives. It explicitly labels the
categorical Pacman construction and the parameter realization as additional
structures, not consequences of BGT or Efimov.

The note's proposed finite marked-model system contains:

- marked Pacman models and morphisms;
- spectral enhancements and perfect stable categories;
- refinement functors;
- a categorical renormalization endofunctor;
- parameter loci `Q_n(P)` defined by a separate realization predicate.

The note then states that connectedness, compactness, nesting, and the
MLC-compatible neighborhood basis for `Q_n(P)` are still open construction
problems.

## Relevance to the current frontier

Efimov's rigidity, relative tensor products, trace-class maps, and nuclearity
can organize refinement and renormalization data. BGT/Efimov universal
properties do not by themselves imply connectedness of a subset of the
parameter plane. A theorem connecting a categorical decomposition to a
topological clopen decomposition is required.

The current frozen target

```text
{c' | green_function c (c' - c) < 2^(-n)} ∩ MandelbrotSet
```

is not one of the independently defined parameter loci in the note. No
phase-parameter comparison identifies it with a `Q_n(P)` in the repository.
This note therefore supports an alternative research direction and does not
discharge the existing Lean axiom.

The Efimov source used for the current plan is arXiv:2510.17010v1,
*Rigidity of the category of localizing motives*. The canonical raw copies
are kept outside this repository at
`/home/kir/pers/raw/refs/efimov-rigidity-category-localizing-motives-2510.17010v1.pdf`
and
`/home/kir/pers/raw/refs/efimov-rigidity-category-localizing-motives-2510.17010v1.tex`.

Related source texts named by the note:

- BGT, "A universal characterization of higher algebraic K-theory";
- Efimov, "Rigidity of the category of localizing motives".
