# GPT-5.4 Worker Task 09: Specify the canonical Option B parameter piece

**Repository:** `/home/kir/pers/mlc`  
**Mode:** research and architecture audit; result report only  
**Result file:** `plan/GPT54_RESULT_09_SPECIFY_CANONICAL_PARAMETER_PIECE.md`

## Safety and communication

Write only the result report, via atomic rename. Do not edit Lean sources,
plans, docs, notebooks, or prior artifacts; do not commit.

Use local primary sources in `refs/` and exact source locations. Internet lookup
is authorized when needed, but prefer primary sources and provide stable links.

## Goal

Give a precise, non-circular specification for the first genuine finite-level
parameter piece that should replace or mediate the frozen-base
`ParaPuzzlePieceAt`. Identify the smallest repository refactor boundary and one
restricted theorem suitable for initial formalization.

Do not propose a connected-source exact-image existential, a packaged
connectivity hypothesis, or either retired motion predicate.

## A. Select one concrete classical construction

Choose exactly one finite-level construction from a primary source, preferably a
simple Yoccoz/parapuzzle piece in a wake away from neutral degeneracies. State:

- the base parameter class;
- admissible combinatorics and depth;
- the parameter wake/domain;
- the finite parameter boundary graph (rays, equipotential arcs, landing/root
  data);
- whether the piece is an open component, closed component, closure, or full
  continuum;
- the distinguished component containing the base parameter.

Every object must be defined independently of its desired connectedness.
Defining it canonically as a connected component of an independently defined
complement/domain is allowed and should be distinguished from existential
connected-witness packaging.

## B. Pin the source precisely

For the chosen construction provide:

- full bibliography and stable URL/local ref path;
- exact section, theorem/proposition/lemma, and PDF page;
- faithful hypotheses and conclusion;
- at most 25 quoted words per source;
- a clear account of which connectivity/topology property follows by definition
  and which requires a theorem.

If no source available to you gives enough precision, choose decision
“source-blocked” rather than inventing the interface.

## C. Produce a Lean-facing specification

Write proposed Lean signatures (not implementations) for the minimal layers:

1. parameter external coordinate/ray/equipotential data already available or
   missing;
2. finite parameter boundary graph;
3. canonical component-based `GenuineParaPuzzlePieceAt`;
4. openness/connectedness/compact-closure facts;
5. the exact shrink or neighborhood-basis theorem required by
   `LcAtOfShrink.lean`.

For each signature label every hypothesis as:

- already proved in repo;
- existing Mathlib API;
- sourced classical theorem to formalize;
- genuinely missing definition;
- open mathematics.

Do not include a field or premise that directly assumes the desired piece is
connected if connectivity follows from the component construction.

## D. Downstream migration audit

Trace every substantive consumer of `ParaPuzzlePieceAt` and classify it:

- purely topological and reusable after changing the set family;
- dependent on the frozen translation identity;
- dependent on dynamical puzzle containment;
- axiom/transport packaging that should be retired;
- unrelated/off-path.

Give exact files/declarations and propose the smallest abstraction, if any, that
lets `LcAtOfShrink` consume a genuine nested connected neighborhood family
without mentioning frozen Green translates.

The abstraction must expose concrete properties (membership, relative
neighborhood, connectedness, nesting/shrinkage); it must not be a renamed bundle
whose only field is the full target theorem.

## E. First restricted milestone

Propose one bounded initial theorem for one explicit parameter class/depth. It
must have:

- a canonically defined target;
- hypotheses fixed independently of connectivity;
- a source-backed proof outline;
- a concrete downstream consumer or validation theorem;
- a clear list of missing Mathlib/project foundations.

Estimate feasibility as high/medium/low and identify the first likely Lean
blocker.

## F. Decision

Choose exactly one:

1. specification ready for Lean implementation;
2. specification ready but one source theorem must be pinned more precisely;
3. source-blocked—name the exact missing source/page;
4. architecture-blocked—name the unresolved mathematical mismatch.

Then provide the exact next worker task, but do not create its task file.

## Report contract

Include:

1. executive decision;
2. selected construction and exact source;
3. mathematical definition stack;
4. Lean-facing signatures with dependency labels;
5. downstream consumer/migration table;
6. first restricted milestone and feasibility;
7. blockers and final decision;
8. proposed next worker task;
9. exact searches/commands/tool limits;
10. complete `git status --short` and safety/no-commit confirmation.

The final result file is the completion signal. Stop afterward.
