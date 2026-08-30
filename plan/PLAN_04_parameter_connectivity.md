# PLAN 04: Discharge the straddling parameter-connectivity frontier honestly

**Status:** ACTIVE  
**Depends on:** `PLAN_00_frontier_overview.md`

## Goal

Remove the live frontier axiom

```lean
MLC.green_sublevel_translate_inter_mandelbrot_connected_straddling
```

by a theorem, without hiding uncovered content inside exact-image existence or
connected-witness packaging.

## Checked formal facts

### 0. Current Route-C analytic milestone

The exact frozen translated-Green target remains the downstream objective. The
active constructive route is now the independently meaningful near-infinity
Böttcher family and its parametrized inverse, not a definition of the target as
a motion image.

The checked modules
`Mlc/Quadratic/Complex/Bottcher/BottcherParamHolo.lean`,
`BottcherParamInverse.lean`, and `BottcherParamMotion.lean` now provide a local
parameter inverse and a nontrivial space-holomorphic motion of an explicit
connected closed disk. The inverse identity is tracked simultaneously in the
parameter and dynamical coordinates.

This is infrastructure only. The disk is not yet an equipotential or
parapuzzle boundary, and no theorem identifies its image with a Mandelbrot
parameter piece or with the frozen target. The straddling axiom is therefore
unchanged.

### 1. The live frontier is the straddling case only

`Mlc/ParaPuzzleConnectivity.lean` no longer exposes a single unrestricted frontier
statement as primitive. The current theorem

```lean
MLC.green_sublevel_translate_inter_mandelbrot_connected
```

is derived by a subset/straddling split, and the only remaining axiom is

```lean
MLC.green_sublevel_translate_inter_mandelbrot_connected_straddling
```

for the case when the translated Green sublevel is not contained in
`MandelbrotSet`.

### 2. One attempted motion route is formally dead on the live stratum

`Mlc/ParaPuzzleCarvingReduction.lean` proves

```lean
not_paraPieceCarvedByMotion_of_straddling
```

showing that on the live straddling stratum, `ParaPieceCarvedByMotion` is
impossible. Its associated conditional theorem
`isConnected_greenSublevel_inter_mandelbrot_of_carvedByMotion` remains logically
correct, but it is unusable for the remaining frontier because its hypothesis is
refuted exactly where the frontier lives.

### 3. The other motion-image route is not a reduction

`Mlc/Quadratic/Complex/Bottcher/Slodkowski.lean` proves

```lean
paraPieceIsMotionImage_iff_connected
```

so `ParaPieceIsMotionImage c n` is equivalent to the target connectedness claim
itself. It is therefore connectivity packaging, not a smaller Douady–Hubbard
input and not a reduction of the frontier.

### 4. The current parameter object is a frozen-base translate

`ParaPuzzlePieceAt c n` is currently defined as a translated frozen-base dynamical
piece and, for `c ∈ MandelbrotSet`, identified with a translated frozen-base
Green sublevel. It is **not** presently defined from parameter wakes, moving
parameter graphs, parameter rays, or a phase-parameter component construction.

### 5. Finite-branch usage does not by itself justify the old narrative

The repository does feed the universal target plus shrinking hypotheses into
`LocallyConnectedAt`, but calling the remaining gap merely a routine
finitely-renormalizable Yoccoz formalization omission is not justified by the
current code. The missing content is bound up with the repository’s actual
frozen-base target and classwise global route.

## Mathematical interpretation

The current formal target is:

```lean
IsConnected ({c' | green_function c (c' - c) < (1 / 2 : ℝ) ^ n} ∩ MandelbrotSet)
```

with the translated Green sublevel already known connected before intersecting
with `MandelbrotSet`.

This should currently be interpreted as a repository-specific parameter
connectivity frontier motivated by classical parapuzzle mathematics, not as an
already formalized finite-level parameter wake theorem.

## Literature-sensitive questions requiring a separate sourced audit

The following are not treated as settled by the present repository alone and must
be tracked separately if needed:

1. whether a classical Douady–Hubbard/Yoccoz finite-level parameter-piece theorem
   directly implies the repository’s frozen-base translated-Green target;
2. which exact literature statement should mediate between the present target and
   a genuine parameter-boundary/wake construction;
3. whether the intended global route should continue through the current target or
   should first replace it with a canonically defined parameter object.

## Completed Phase 0 — guardrails

The following guardrails are now checked facts:

- `not_paraPieceCarvedByMotion_of_straddling` blocks the self-carving exact-image
  route on the live frontier;
- `paraPieceIsMotionImage_iff_connected` shows that arbitrary connected-source
  exact-image existence is equivalent to the target and cannot be counted as a
  reduction.

### Phase 0 no-go rule

Do **not** resume any plan step that proposes to solve the frontier by adding:

- an existential exact-image witness,
- a connected reference-set package,
- a transport datum equivalent to `∃ S, IsConnected S ∧ S = target`, or
- a motion-image hypothesis whose only consumer is the target connectedness claim.

Those routes are formally dead as reductions.

## Phase 1 — choose and specify the intended parameter object

Choose one of the following, explicitly and without ambiguity.

### Option A — keep the frozen-base translated-Green target

Keep the target exactly as it exists now and identify an independent mathematical
statement that implies

```lean
IsConnected ({c' | green_function c (c' - c) < (1 / 2 : ℝ) ^ n} ∩ MandelbrotSet)
```

without introducing connectivity packaging.

Required output:
- a named theorem statement from the literature or a repo-internal geometric
  theorem with independently defined hypotheses;
- a precise explanation of why its target is genuinely the current frozen-base
  set and not a different classical parapuzzle object.

### Option B — replace the target by a genuine finite-level parameter object

Define a parameter object independently of connectedness, for example via
parameter boundaries/rays/wakes plus a component construction, and then compare
it to the current frozen-base target only if mathematically justified.

Required output:
- an independently specified finite-level parameter piece definition;
- its boundary/separation data;
- a clear theorem target to replace or mediate to the current translated-Green
  formulation.

### Phase 1 success criterion

A concrete object/theorem pair is fixed, and neither side is defined by an
exact-image existential or connected-witness package.

## Phase 2 — restricted canonical construction

Work first in one explicit parameter class and one finite level.

Required deliverables:
1. choose the class and explain why it is the correct first nontrivial model;
2. define the source object, boundary motion or phase map, and target
   independently of connectedness;
3. prove connectivity from component/separation topology, not from a packaged
   exact image of a connected set.

### Route-C progress inside Phase 2

The first local analytic substage is complete. For every base parameter, the
checked parametrized Böttcher inverse supplies a positive-radius neighborhood
and an explicit nontrivial translation motion of a connected closed disk.
Space-holomorphy, injectivity, source connectedness, and nontriviality are
proved without a new project axiom.

This does not satisfy the Phase-2 parameter-piece deliverable: the source is
not an equipotential or parapuzzle boundary, and the
Douady–Hubbard parameter/dynamical correspondence is still absent. It advances
the analytic base without changing the frontier status.

### Phase 2 go/no-go rule for analytic infrastructure

Do **not** resume λ-lemma, Słodkowski, or full-basin Böttcher development for this
frontier unless there is already a canonical, independently defined geometric
consumer in the repository for that analytic machinery.

Analytic work may resume only if all of the following are true:
- the target parameter object is fixed independently of connectedness;
- there is a theorem statement requiring actual analytic transport rather than a
  logically equivalent packaging predicate;
- the theorem’s conclusion is not already equivalent to the desired
  connectedness statement by identity-motion witnesses.

## Phase 3 — classwise coverage audit and global assembly

Enumerate every class actually consumed by the MLC route and mark each as one of:

- **proved in repo**;
- **literature-backed but not yet formalized**;
- **genuinely open / residual frontier**.

This audit must cover the full route to `mlc_conjecture`, including finite,
primitive infinitely renormalizable, satellite/tower, and residual near-molecule
content.

### Phase 3 assembly rule

No uncovered class may be hidden inside:
- exact-image existence,
- transport data equivalent to connectedness,
- an unnamed “standard parapuzzle correspondence” placeholder.

## Short-term success criteria

1. The next task chooses Option A or Option B explicitly.
2. Any proposed construction names a target object independent of connectedness.
3. No new route proposal relies on `ParaPieceCarvedByMotion` or
   `ParaPieceIsMotionImage` as a frontier reduction.

## Full success criteria

1. The straddling axiom is replaced by a theorem.
2. `make check` no longer lists
   `MLC.green_sublevel_translate_inter_mandelbrot_connected_straddling`.
3. No weaker replacement axiom is introduced.
4. The final route makes uncovered mathematical content visible class by class.

## Alternative direction audit: Efimov and noncommutative motives

The external Pacman/motive note is now recorded in
`refs/bridge_between_pacman_renormalization_and_noncommutative_motives.md` and
expanded in `plan/PLAN_05_MOTIVIC_ALTERNATIVE_AUDIT.md`.

This direction is exploratory rather than a new axiom-A proof. Efimov's
relative localizing motives can organize finite marked renormalizations,
refinement maps, trace-class/nuclear behavior, and scaling. They do not imply
that a parameter-plane locus is connected. The note's own `Q_n(P)` parameter
realization is an additional object whose compactness, connectedness, nesting,
and MLC neighborhood property remain to be constructed.

The only potentially useful connectivity mechanism is a conservative
topological realization:

```text
disconnected parameter locus
 -> nontrivial clopen split
 -> categorical idempotent/split exact decomposition
 -> contradiction with independently proved marked-model indecomposability.
```

The two arrows involving categorical data are not supplied by BGT or Efimov
and must not be assumed. The frozen translated-Green target still has no
verified comparison with `Q_n(P)`. Therefore the immediate target remains a
genuine phase/component-attachment theorem, with motives used only after the
geometric object and its consumer are fixed.

The generic topological shortcut is now formally ruled out in
`Mlc/MotivicIntersectionNoGo.lean`: connected ambient sets, openness, a common
point, and a straddling hypothesis do not imply connectedness of the
intersection. The same module checks the elementary clopen-to-idempotent
implication in `C(X, ℤ)`, but supplies neither the Pacman realization nor its
conservative comparison.
