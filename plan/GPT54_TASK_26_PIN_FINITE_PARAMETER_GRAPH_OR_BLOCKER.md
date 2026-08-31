# GPT-5.4 Worker Task 26: Pin a finite parameter graph or identify its exact blocker

**Repository:** `/home/kir/pers/mlc`
**Mode:** read-only, tightly bounded source/API audit
**Result file:** `plan/GPT54_RESULT_26_PIN_FINITE_PARAMETER_GRAPH_OR_BLOCKER.md`

## Safety and route constraint

Write only the result report, via atomic rename. Do not edit Lean sources,
dependencies, plans, or prior artifacts; do not commit. Use `/tmp` for extraction
and Lean signature probes.

Read Task 25, Result 25, Supervisor Review 25, and the focused progress report.

The following are out of scope and must not be selected as the answer:

- `M(g)` or `M°`;
- renormalization windows/little Mandelbrot copies;
- straightening;
- generic family structures with connectedness stored as a field;
- exact-image/motion packaging;
- the frozen set `G_c(c'-c)` as the definition of a parameter piece.

## Goal

Resolve one binary question:

> Can the current repository define a genuine finite parameter graph from moving
> parameter rays and an equipotential now, or is a precise parameter-external-
> coordinate foundation missing?

## A. Repository capability audit

Search all Lean files and dependencies for concrete declarations implementing:

- the parameter Böttcher/uniformization map `Φ_M : ℂ \ M → ℂ \ closedDisk`;
- its inverse;
- parameter external rays at an angle;
- parameter equipotentials at a potential/radius;
- landing points of rational parameter rays;
- wakes or components of complements of finite parameter graphs.

For every apparent match give the exact signature, file/line, axiom/sorry
dependency, and whether it is a dynamical-plane object or genuinely a
parameter-plane object. Do not infer parameter rays from dynamical rays without a
proved phase–parameter theorem.

## B. One exact source definition

Directly inspect a locally available primary/expository source and select one
specific finite graph definition, including:

- the finite angle set;
- parameter ray segments;
- the parameter equipotential arc/level;
- landing/root points where required;
- the connected component containing the base parameter;
- open versus closed piece convention.

Give exact source pages/extracted lines and a short compliant quote. State all
hypotheses on the base parameter and depth. If no local source provides enough
detail, report that precisely rather than substituting a different object.

## C. Minimal independent Lean definitions

If the required parameter external-coordinate API exists, give and compile-test
concrete `def` signatures for:

```lean
finiteParameterGraph
openParameterPiece
closedParameterPiece
```

The piece must be obtained from a connected component of the complement of the
graph (and closure if appropriate), not from a connectedness hypothesis.

If the API does not exist, specify the first missing definitions in dependency
order, beginning with the parameter external coordinate. Give compile-oriented
signatures only for mathematically defined data—not axioms or structures storing
their desired properties.

## D. Elementary topology boundary

Determine exactly what follows merely from defining the piece as a connected
component:

- preconnectedness/connectedness;
- openness of a component in the relevant locally connected ambient open set;
- basepoint membership;
- what does **not** follow about intersection with `MandelbrotSet`, nesting, or
  shrinkage.

Identify exact Mathlib lemmas where available.

## E. First implementation task

Choose the earliest real, non-axiomatic implementation milestone on the dependency
chain. It may be:

- a parameter external-coordinate definition from already proved Böttcher data;
- a parameter ray/equipotential definition;
- a generic finite-graph component definition after those objects exist.

It must have a concrete future consumer in the selected finite parameter graph and
must not store connectivity as input.

## F. Decision

Choose exactly one:

1. the finite parameter graph definitions are ready for implementation;
2. parameter external coordinate exists, but rays/equipotentials are missing;
3. parameter external coordinate itself is the immediate missing foundation;
4. the source definition remains too underspecified.

Give the exact next worker task but do not create its file.

## Report contract

Include exact source locations, repository signatures, searches, tested code,
complete `git status --short`, and confirmation that only the result artifact was
written and no commit was made.
