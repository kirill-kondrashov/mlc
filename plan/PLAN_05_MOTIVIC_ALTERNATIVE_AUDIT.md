# PLAN 05: Efimov/noncommutative-motive route for the straddling frontier

**Status:** ACTIVE DESIGN / CONDITIONAL ROUTE; no discharge claimed
**Date:** 2026-08-30
**Depends on:** `PLAN_00_frontier_overview.md`, `PLAN_04_parameter_connectivity.md`
**Primary source:** Efimov, *Rigidity of the category of localizing motives*,
arXiv:2510.17010v1
**Canonical raw references:**

- `/home/kir/pers/raw/refs/efimov-rigidity-category-localizing-motives-2510.17010v1.pdf`
- `/home/kir/pers/raw/refs/efimov-rigidity-category-localizing-motives-2510.17010v1.tex`

The PDF and extracted TeX source are refreshed from arXiv and checksum-checked.
The repository does not duplicate these large source files in `refs/`;
migration into the repository reference policy is a separate task.

## Executive decision

Efimov's paper supplies a rigorous categorical support layer, not a direct
proof of

```lean
MLC.green_sublevel_translate_inter_mandelbrot_connected_straddling
```

The route is therefore a three-gate chain:

1. construct finite marked parameter data and its realization locus without
   mentioning connectedness;
2. prove a conservative separation-to-idempotent theorem and independent
   indecomposability for the marked model;
3. prove the exact comparison with the frozen translated-Green target.

Only after all three gates are proved can the straddling axiom be removed.
Replacing it by a connectedness field, an exact-image witness, or an opaque
motivic indecomposability assumption is not an acceptable step.

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

## Source-backed Efimov interfaces

The following interfaces are present in arXiv:2510.17010v1 and are the only
parts of the motivic route treated as source-backed infrastructure.

### Universal and relative localizing motives

Efimov uses the Blumberg--Gepner--Tabuada universal finitary localizing
invariant

```text
U_loc : Cat^perf -> Mot^loc
```

with

```text
Hom_Mot^loc(U_loc(Sp^omega), U_loc(C)) ~= K(C).
```

Theorem `th:rigidity_over_Sp_intro` proves that `Mot^loc` is rigid symmetric
monoidal. The general Theorem `th:dualizability_and_rigidity` gives the
relative form: for a rigid `E_1`-monoidal base `E`, `Mot^loc_E` is dualizable,
and it is rigid when `E` is `E_2`-monoidal (in particular symmetric).

For this project the relative notation is:

```text
E_P       = coefficient category for the finite marking symmetry,
C_n(P)    = stable category of the finite marked model at depth n,
M_n(P)    = U_loc,E_P(C_n(P)).
```

The notation is a target specification, not a Lean definition or an added
axiom.

### Trace-class refinement and nuclear towers

Definition `def:nuclear_E_modules` and Proposition `prop:nuclear_equiv_cond`
give the usable refinement contract: an ind-system is nuclear when its
transition functors are eventually right trace-class over `E`. This is the
appropriate interface for depth refinement and discarded-sector
attachments.

Theorem `th:morphisms_in_Mot^loc_via_limits` identifies morphisms from a
nuclear source with inverse limits of continuous K-theory spectra, and gives
the corresponding internal-Hom statement in the symmetric case. Theorem
`th:morphisms_in_Mot^loc_via_internal_Hom` supplies the compact/proper Calkin
description when a finite model satisfies the required compactness or
properness hypotheses.

These results can organize a refinement tower and prove compatibility of
finite truncations. They do not prove that any parameter locus is connected
or that a refinement tower shrinks in the parameter plane.

### Equivariant and local-system variants

Theorem `th:G_equivariant_motives` treats a group action using the rigid
convolution category

```text
Loc(BG) = product_{g in G} Sp.
```

It proves dualizability and self-duality of the corresponding equivariant
motives. The paper also records the analogous construction for a connected
space `X`; for a disconnected `X`, the motive category is a product over the
connected components.

The first implementation must use a finite, explicit marking group `G_P`,
so that the source-backed group-action theorem applies directly. A general
parameter-space local-system version is optional and must not be used before
its hypotheses are formalized.

### Rigidification

Theorem `th:localizing_motives_over_rigidification` can be used if the chosen
analytic coefficient category is only locally rigid. This is a secondary
technical option, not a way to obtain the missing geometric realization.

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

## Chosen finite categorical model

For a finite marked Pacman model `P`, use the following target shape.

1. Let `G_P` be the finite group of marking/rotation symmetries actually
   present in `P`. Do not introduce a formal group action unless the finite
   boundary and return data define it.
2. Set `E_P := Loc(BG_P)`, equivalently the finite convolution category
   `product_{g in G_P} Sp`. The trivial-symmetry case is the absolute base
   `Sp`.
3. Build a small idempotent-complete stable incidence category `C_n(P)`
   from the finite branches, boundary arcs, gluing maps, and discarded
   sectors. A model of the form `Perf(A_n(P))` for a finite spectral or dg
   incidence algebra is allowed, but `A_n(P)` must be constructed from the
   geometry and not postulated.
4. Prove that `C_n(P)` is dualizable over `E_P`, and preferably proper or
   relatively compactly generated. Define `M_n(P) := U_loc,E_P(C_n(P))`.
5. For a genuine refinement `P_{n+1} -> P_n`, construct an exact strongly
   continuous `E_P`-linear functor in a stated direction. Prove eventual
   trace-class behavior (or a stronger finite properness statement) before
   invoking Efimov's inverse-limit theorems.

The finite incidence category is the bridge between the geometric model and
the motive. It must be specified before any claim about a motivic
indecomposability invariant is made.

## Route M1: a motivic component/no-separation theorem

This is the only route in which motives could plausibly help prove
connectedness rather than merely organize renormalization.

### Independent objects required

1. Define a finite marked Pacman model `P` from actual quadratic-like
   first-return data, without mentioning connectedness.
2. Define `Real_n(P,c)` using domains, branches, gluing, and markings.
3. Define `Q_n(P)` from `Real_n(P,c)`.
4. Define a topological or exit-path/incidence category whose objects include
   boundary arcs, first-return branches, and attachment morphisms. It must be
   defined before components of `Q_n(P)` are known.
5. Construct a functor from the finite marked-model category to that
   incidence category, then to the stable/spectral category `C_n(P)`.
6. Construct the comparison from locally constant integer-valued functions on
   `Q_n(P)` to categorical idempotents, with a proof that nontriviality is
   preserved.

### Non-circular theorem contracts

The following must be proved, not placed in a data structure as assumptions.

1. **Realization compactness:** `Q_n(P)` is compact and lies in the
   Mandelbrot set.
2. **Phase-parameter bridge:** the finite dynamical marking and the parameter
   realization determine the same boundary/attachment data.
3. **Incidence functor:** the boundary/attachment graph maps to `C_n(P)` and
   this map is conservative for the finite decomposition data being used.
4. **Separation to idempotent:** a nontrivial clopen decomposition of
   `Q_n(P)` produces a nontrivial idempotent in the endomorphisms of the
   selected incidence object or of `M_n(P)`. The existing
   `C(Q, Z)` construction in `Mlc/MotivicIntersectionNoGo.lean` is only the
   topological input; the comparison map is still missing.
5. **Categorical indecomposability:** the selected incidence object or
   relative motive has no such nontrivial idempotent, proved from the actual
   finite first-return/attachment graph. This cannot be inferred from
   rigidity, the universal property of `U_loc`, `K`, `THH`, or `TC`.
6. **Frozen comparison:** either prove `Q_n(P(c,n)) = T(c,n)` for a
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

The exact-target route requires item 6. A moving-piece replacement without
item 6 may be mathematically useful, but it does not discharge the named
frozen theorem and must be reported as a consumer migration instead.

### Lean frontier capture

The categorical sentence is recorded as the non-axiomatic proposition
`MLC.Motivic.GreenSublevelStraddlingMotivicFrontier` in
`Mlc/MotivicConnectednessFrontier.lean`. For each straddling target it asks
for a realization set `Q` equal to the frozen target, together with an
abstract endomorphism monoid standing for
`π₀ End_{Mot^loc_E}(M_n(P))`. Its
`SeparationReflectingIndecomposable` payload requires:

```text
nontrivial clopen split of Q
  -> nontrivial idempotent in the motive endomorphism monoid
and
no nontrivial idempotent in that monoid.
```

The file proves the conditional implication from this contract to
`IsConnected Q`. It deliberately does not claim that the abstract monoid is
already an Efimov motive, nor that `Q` has already been constructed
independently of the target. Those are the geometric and categorical
implementation obligations still separating the contract from a discharge.

### First falsification test

Before implementing any large infinity-categorical construction, specify the
incidence category and prove the separation-to-idempotent implication for one
finite marked model. If this implication cannot be stated without assuming
the desired connectedness, route M1 is not a real reduction.

### Finite incidence gate (2026-08-30)

The first algebraic incidence gate is now implemented in
`Mlc/MotivicFiniteIncidence.lean`. For a graph `G`, it defines

```text
IncidenceEndomorphismRing(G)
  = {f : V(G) -> Z | f is constant on every incidence edge}.
```

The theorem
`incidenceCenter_noNontrivialIdempotent` proves, without any topological or
connectedness assumption on a parameter locus, that a connected incidence
graph has no nontrivial idempotent in this ring. Its proof propagates the
value of an idempotent along graph walks and uses
`e(v)^2 = e(v)` in `Z`.

The module also defines `boundaryIncidenceGraph` on the finite subtype of
arcs supplied by `FiniteParapuzzleBoundary.lean`; adjacency is distinctness
plus nonempty carrier intersection. The theorem
`boundaryIncidenceGraph_connected_iff_carrier_connected` proves that, for this
finite arc model, a connected union of carriers is equivalent to a connected
attachment graph. The type
`IncidenceMotiveBridge` isolates the genuinely missing comparison

```text
C(Q, Z) -> IncidenceEndomorphismRing(G)
```

and requires only preservation of nontrivial clopen characteristic functions.
The conditional theorem
`connectedSpace_of_incidenceMotiveBridge` feeds this comparison and the
independently proved graph indecomposability into the existing motivic
connectedness contract. The exact-target consumers
`green_sublevel_translate_inter_mandelbrot_connected_of_incidenceMotiveBridge`
and
`green_sublevel_translate_inter_mandelbrot_connected_of_boundaryIncidenceMotiveBridge`
also prove the target's nonemptiness from `c ∈ M` and wire the contract to
the frozen set. No Efimov motive, realization predicate, or root axiom is
introduced by this module.

### Checked topological gate (2026-08-30)

The first gate is now formalized in
`Mlc/MotivicIntersectionNoGo.lean`, which is imported by `Mlc.lean`.

1. The generic implication

   ```text
   S and K connected + S open + S ∩ K nonempty + S ⊄ K
   -> S ∩ K connected
   ```

   is false. A checked counterexample is the punctured plane
   `S = ℂ \ {0}` and the embedded segment
   `K = [-1,1] ⊂ ℝ ⊂ ℂ`. Both ambient sets are connected, the segment
   meets the punctured plane, and the intersection is disconnected by the
   intermediate value theorem.

2. The elementary topological realization
   `integerValuedRealization X := C(X, ℤ)` passes the
   separation-to-idempotent test: every nontrivial clopen subset produces a
   continuous characteristic function `e` with `e * e = e`, `e ≠ 0`, and
   `e ≠ 1`.

This is a necessary-condition test, not a proof of the frontier. It confirms
that a future Pacman incidence realization must carry information beyond the
two ambient connectedness statements. The module contains no Pacman
connectedness assumption, no motive axiom, and no `sorry`.

The gate does **not** yet provide the missing finite marked Pacman model or a
conservative functor from it to `C(Q_n(P), ℤ)`. Consequently M1 remains
blocked at the phase/component-attachment and conservativity steps; no
infinity-categorical implementation is justified by this test alone.

## Route M2: use motives for the moving-piece replacement

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

For the current goal this is a fallback, not success: it must not be reported
as a discharge of
`green_sublevel_translate_inter_mandelbrot_connected_straddling` unless the
exact comparison in M1.6 is also proved.

## Route M3: use relative motives for the residual renormalization

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

1. keep the arXiv PDF and TeX source in the canonical raw reference location
   (done in this refresh);
2. write a non-circular `Real_n`/`Q_n` interface with no `IsConnected` field;
3. instantiate the main-cardioid base case at `c = 0` and one finite level
   using `FiniteParapuzzleBoundary.lean`;
4. prove compactness, boundary separation, component attachment, and nesting
   for that model before introducing motives;
5. formalize the finite `C(Q_n(P), Z)` separation test and state the
   conservative comparison theorem;
6. only if the comparison theorem has a non-circular statement, introduce the
   finite incidence category and the smallest categorical structures needed
   for it;
7. prove indecomposability independently from the marked attachment graph;
8. add `E_P`, refinement functors, and Efimov trace-class/nuclear data, then
   use the inverse-limit/internal-Hom theorems for compatibility and
   shrinking;
9. prove the exact comparison with the frozen target and only then migrate
   the finite-side MLC consumer and delete the straddling axiom.

No infinity-categorical implementation is justified before steps 4 and 5
have checked the geometric and conservative gates. A Lean structure with
fields containing the desired conclusions is not an implementation.

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
- the exact comparison to the frozen target is proved if the named theorem,
  rather than only a replacement consumer, is to be discharged.

Stop and retain the current frontier if any gate fails. In particular, do not
replace the frozen axiom by `Q_n(P)` plus an assumed connectedness field.

## Current decision

The Efimov direction is now an active, source-backed conditional route:

```text
finite parameter geometry
  -> Q_n(P) and incidence category
  -> conservative separation-to-idempotent theorem
  -> independent motive indecomposability
  -> Q_n(P) connected
  -> exact frozen-target comparison
  -> delete the straddling axiom
```

Efimov supplies the relative motive, rigidity, trace-class/nuclear, and
equivariant/local-system interfaces in the middle of this chain. The first
and last arrows remain the decisive geometric obligations. The checked axiom
frontier is unchanged until those obligations are proved.
