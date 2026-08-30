# PLAN 05: Efimov/noncommutative-motive alternative for the frozen straddling frontier

**Status:** EXPLORATORY; not a replacement proof plan yet  
**Date:** 2026-08-30  
**Depends on:** `PLAN_00_frontier_overview.md`, `PLAN_04_parameter_connectivity.md`

## Executive conclusion

The Pacman/noncommutative-motives note supplies a useful language for
renormalization, refinement, gluing, and scaling, but it does not contain a
direct proof of

```lean
MLC.green_sublevel_translate_inter_mandelbrot_connected_straddling
```

The note explicitly treats its finite marked-model categories and its
parameter realization as additional constructions. Its parameter-locus
requirements are essentially the missing phase-parameter geometry in a new
notation.

The viable alternative is therefore a **two-layer route**:

1. construct an independently defined topological realization of finite
   marked Pacman data and prove a phase/component-attachment theorem;
2. use Efimov's relative motives to control refinement, renormalization,
   trace-class behavior, and possibly shrinking.

Efimov's universal localizing motive cannot be used as a stand-alone
connectedness theorem. No new Lean axiom is justified by this direction.

## Exact current obstruction

Write

```text
T(c,n) = {c' | green_function c (c' - c) < 2^(-n)} ∩ MandelbrotSet.
```

The repository already proves connectedness of the un-intersected translated
Green sublevel. The live gap is the straddling intersection `T(c,n)`.

The linked note proposes parameter loci of the form

```text
Q_n(P) = {c in MandelbrotSet | Real_n(P,c)}
```

where `Real_n` records marked-hybrid realization of a finite Pacman model.
The note requires `Q_n(P)` to be compact, connected, nested, and
MLC-compatible, but does not derive those properties. The repository has
neither `Real_n` nor a theorem identifying `Q_n(P)` with `T(c,n)`.

Thus the immediate blocker is unchanged:

- a categorical motive has not been connected to a parameter subset;
- the frozen target has not been connected to a canonical moving parameter
  locus;
- no component-attachment or no-separation theorem has been formalized.

## What Efimov/BGT can legitimately contribute

### 1. Finite marked renormalization objects

The note's marked Pacman models, spectral enhancements, and perfect module
categories give a possible home for finite first-return data. A refinement
from depth `n` to depth `n+1` could become an exact functor after the mapping
spaces and Morita choices are actually constructed.

This would organize data already present informally in the repository:

- first-return branches;
- gluing and discarded sectors;
- external-ray and bubble incidence;
- finite renormalization triangulations.

None of these constructions currently exists in Lean in the required
categorical form.

### 2. Relative motives for rotation data

For a fixed rotation class, a coefficient category `E_theta` could encode
the relative Siegel/Pacman structure. Efimov's relative localizing motives
could then make refinement and renormalization maps amenable to duality,
relative tensor products, trace-class criteria, and nuclearity arguments.

This is more naturally aligned with the residual virtual near-Molecule
renormalization package than with the finite frozen intersection itself.

### 3. Quantitative refinement and scaling

If a realization functor and a finite-dimensional realization of the motive
were constructed, traces or eigenvalues could provide quantitative control of
refinement. Such control might prove shrinking of parameter loci or diameter
estimates.

Shrinking is not connectedness. It cannot replace the missing theorem that
each finite-level locus has one parameter component.

## Candidate route M1: a motivic component/no-separation theorem

This is the only route in which motives could plausibly help prove
connectedness rather than merely organize renormalization.

### Independent objects required

1. Define a finite marked Pacman model `P` from actual quadratic-like
   first-return data, without mentioning connectedness.
2. Define `Real_n(P,c)` using domains, branches, gluing, and markings.
3. Define `Q_n(P)` from `Real_n(P,c)`.
4. Define a topological or exit-path/incidence category whose objects include
   the components and attachments of the realization locus.
5. Construct a functor from the marked-model category to that topological
   category, then to a stable or spectral category.

### Non-circular theorem contracts

The following must be proved, not placed in a data structure as assumptions.

1. **Realization compactness:** `Q_n(P)` is compact and lies in the
   Mandelbrot set.
2. **Phase-parameter bridge:** the finite dynamical marking and the parameter
   realization determine the same boundary/attachment data.
3. **Conservativity on separation:** a nontrivial relatively clopen
   decomposition of `Q_n(P)` produces a nontrivial idempotent or split exact
   decomposition in the chosen incidence category.
4. **Categorical indecomposability:** the relevant marked model or its
   relative motive has no such decomposition, proved from the actual
   first-return/attachment geometry rather than from an axiom.
5. **Frozen comparison:** either prove `Q_n(P(c,n)) = T(c,n)` for a
   canonically extracted `P(c,n)`, or replace the finite-side consumer by the
   canonical `Q_n(P)` and prove that the replacement supplies the required
   local-connectivity windows.

The intended contradiction is:

```text
Q_n(P) disconnected
 -> nontrivial clopen decomposition
 -> nontrivial categorical idempotent
 -> forbidden by independently proved marked-model indecomposability.
```

The crucial warning is that the last two arrows do not follow from the
universal property of `U_loc`. They require a conservative realization
theorem. `K`, `THH`, or `TC` values alone are not a substitute.

### First falsification test

Before implementing any large infinity-categorical construction, specify the
incidence category and prove the separation-to-idempotent implication for one
finite marked model. If this implication cannot be stated without assuming
the desired connectedness, route M1 is not a real reduction.

## Candidate route M2: use motives for the moving-piece replacement

Instead of proving the frozen equality, define the finite parameter object
`Q_n(P)` independently and migrate the finite-side MLC consumer to a
connectedness-window interface based on `Q_n(P)`.

Required results:

- nonemptiness and compactness of `Q_n(P)`;
- connectedness from a genuine phase/component theorem;
- refinement nesting;
- compatible-chain intersection;
- a neighborhood-basis or shrinking theorem;
- a theorem that the resulting windows cover every finitely
  renormalizable parameter used by `MainConjecture.lean`.

Efimov motives may help with the refinement and shrinking clauses, but the
phase-parameter theorem remains a classical dynamical input. This route can
remove the frozen axiom from the dependency graph without proving that the
frozen expression was the correct parameter object, provided the downstream
consumer is migrated honestly.

## Candidate route M3: use relative motives for the residual renormalization

The rotation-relative Efimov framework is a better fit for
`residualOpenVirtualNearMoleculeAxiom`:

- encode finite satellite/Pacman renormalizations over `E_theta`;
- model the refinement tower by strongly continuous functors;
- prove trace-class or nuclear transition maps;
- use relative localizing invariants and traces to compare periodic and
  near-periodic data;
- only then seek uniform modulus or shrinking estimates.

This may inform Problems 4.3 and 4.4, but it is not a proof of the finite
parameter intersection connectivity. The two frontier axioms must remain
separate in `check_axioms.lean`.

## Lean integration order

No infinity-category implementation should be started until the geometric
consumer is fixed. The least speculative order is:

1. add source and audit notes (done in this refresh);
2. write a non-circular `Real_n`/`Q_n` interface specification with no
   `IsConnected` field;
3. select one explicit finite marked model and prove its attachment
   topology independently;
4. state and test the separation-to-incidence-category theorem;
5. only if that theorem compiles at the mathematical interface, introduce the
   smallest categorical structure needed for the chosen realization;
6. add relative-motive/refinement data only where it is consumed by a proved
   geometric or shrinking theorem;
7. migrate the finite-side MLC consumer and remove the frozen axiom only after
   `make check` confirms it is unused.

The existing Böttcher, path-chain, loop-product, and local transition modules
remain valid infrastructure, but none is silently promoted to the required
realization theorem.

## Go/no-go gates

Proceed only if all of the following can be proved without new axioms:

- `Real_n` is an actual finite marked-data predicate;
- `Q_n(P)` is not defined by connectedness or an exact-image existential;
- a clopen parameter split has a formally defined categorical consequence;
- the relevant motive/realization is conservative enough to forbid that split;
- the bridge to the finite-side MLC consumer is not equivalent to the target
  connectivity proposition.

Stop and retain the current frontier if any gate fails. In particular, do not
replace the frozen axiom by `Q_n(P)` plus an assumed connectedness field.

## Decision

The Efimov direction is retained as an exploratory bridge and as a possible
renormalization/scaling program. It is not yet a discharge route for
`green_sublevel_translate_inter_mandelbrot_connected_straddling`.

The immediate mathematical target remains a genuine phase/component-attachment
theorem for an independently defined finite parameter object. Motives can
support that theorem only after a conservative topological realization has
been constructed.
