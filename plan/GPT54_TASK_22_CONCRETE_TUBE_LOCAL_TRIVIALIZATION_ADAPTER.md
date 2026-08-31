# GPT-5.4 Worker Task 22: Design a concrete tube local-trivialization adapter

**Repository:** `/home/kir/pers/mlc`
**Mode:** read-only Lean API design and compilation audit
**Result file:** `plan/GPT54_RESULT_22_CONCRETE_TUBE_LOCAL_TRIVIALIZATION_ADAPTER.md`

## Safety

Write only the result report, via atomic rename. Do not edit repository sources,
dependencies, plans, or prior artifacts; do not commit. Use `/tmp` for Lean probes.

Read Result 21 and Supervisor Review 21.

## Goal

Replace Result 21's opaque `Prop` placeholders with concrete local-trivialization
data for a tube represented as `total : Set (ℂ × ℂ)` over an open parameter set.
Determine whether a small adapter to Mathlib's `Pretrivialization` is feasible or
whether a project-local chart structure is cleaner.

## A. Fixed fiber model

Determine the correct fixed model types for open and closed Jordan disks, e.g.
subtypes of the unit open disk and closed disk. Audit existing project/Mathlib names
for these disks and their topology. Explain whether the source's phrase “Jordan
disks (either open or closed)” requires two tube variants or a type parameter for
the model fiber.

Do not encode “is a Jordan disk” as an unexplained proposition. Local
homeomorphisms to a fixed disk should supply the concrete content.

## B. Mathlib adapter feasibility

Using exact signatures from `Pretrivialization`, `Trivialization`, `PartialEquiv`,
and `Homeomorph`, determine how to represent a local chart for the projection from
the subtype `total` to the subtype `Λ`.

Compile-test one actual chart structure/type, not just `#check` commands. It must
concretely contain:

- an open base set/neighborhood;
- the restricted source in the concrete total subtype;
- target equal to base neighborhood times the fixed disk model;
- a local homeomorphism/equivalence;
- first-coordinate/projection compatibility.

If adapting Mathlib `Pretrivialization` is blocked, give the exact type mismatch and
compile a project-local structure with equivalent concrete fields.

## C. Atlas / local triviality

Give a concrete structure that assigns a valid chart to every parameter point and
proves the point lies in its chart's open base set. This structure, not a bare
`local_trivial : Prop`, must encode local triviality.

Show how the chart data imply:

- projection surjectivity over the parameter domain;
- each fiber is homeomorphic to the chosen disk model;
- compatibility with the first-coordinate projection.

The last two may be proposed theorem signatures if their full proofs are beyond
the audit, but the data needed to prove them must be present concretely.

## D. Integration signature

Propose and compile-test a `QuadraticLikeTube` structure tied to one total space of
`AnalyticQuadraticLikeFamilyCore`, and a wrapper supplying source and target tubes.
Avoid duplicate total sets when a dependent field can refer directly to
`core.totalU` or `core.totalV`.

Do not add properness, unfolding, equipment, tubing in the source's later sense,
straightening, or connectedness conclusions.

## E. Decision

Choose exactly one:

1. a concrete tube adapter and family wrapper are ready for implementation;
2. the Mathlib adapter is blocked, but a concrete project-local chart layer is
   ready;
3. one named topology/homeomorphism foundation is still missing;
4. tube formalization should be deferred and the analytic core retained alone.

Give the exact next worker task but do not create its file.

## Report contract

Include complete tested code, exact imports and commands, compilation results,
API signatures, full `git status --short`, and confirmation that only the result
artifact was written and no commit was made.
