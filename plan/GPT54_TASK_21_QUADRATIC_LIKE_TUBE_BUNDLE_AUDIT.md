# GPT-5.4 Worker Task 21: Audit the quadratic-like tube bundle layer

**Repository:** `/home/kir/pers/mlc`
**Mode:** read-only source, topology, and Lean-API audit
**Result file:** `plan/GPT54_RESULT_21_QUADRATIC_LIKE_TUBE_BUNDLE_AUDIT.md`

## Safety

Write only the result report, via atomic rename. Do not edit repository sources,
dependencies, plans, or prior artifacts; do not commit. Use `/tmp` for extraction
and compilation probes.

Read Result/Review 19 and Result/Review 20, plus
`Mlc/AnalyticQuadraticLikeFamilyCore.lean`.

## Goal

Specify the smallest source-faithful tube/fiber-bundle layer needed to promote the
analytic core toward a complete quadratic-like family. Determine whether Mathlib
already has a usable fiber-bundle/local-trivialization API or whether a focused
project structure is preferable.

## A. Direct source semantics

Revisit the directly extracted tube definition around full-text lines
`11708–11711` and enough surrounding text to determine:

- whether “fiber bundle” means locally trivial or globally trivial in this source;
- the model fiber and structure maps, if specified;
- whether open and closed tubes are separate notions;
- whether the source and target of a quadratic-like family must both be tubes;
- whether Jordan-disk fibers are part of the tube definition or already supplied
  by the fiber maps;
- what compatibility with projection `π : ℂ² → ℂ` is required.

Search earlier chapters/definitions for the first use or fuller definition of
“tube.” Give exact extracted line ranges and short compliant quotes. Do not infer
global triviality from the phrase “fiber bundle” without evidence.

## B. Mathlib API audit

Search Mathlib for fiber bundles, local trivializations, bundles over subtypes,
`FiberBundle`, `LocalTriv`, `Bundle.Trivial`, and relevant homeomorphism APIs.
For every plausible reusable declaration report exact file, namespace, signature,
and whether it fits a subset `totalU ⊆ ℂ × ℂ` projected to an open subtype
`parameterSet`.

Distinguish:

- local triviality of a projection;
- one global homeomorphism with `Λ × D`;
- merely continuous variation of Jordan domains.

## C. Representation options

Compare at least:

1. reuse a Mathlib fiber-bundle/local-trivialization structure;
2. store an atlas of local fiber-preserving homeomorphisms;
3. introduce a deliberately stronger global fiber-preserving homeomorphism to a
   fixed Jordan disk;
4. postpone local triviality and define only a named source-compatible interface.

Reject any option stronger than the source unless it is explicitly labeled and
justified for the concrete renormalization window.

## D. Integration with the analytic core

Propose compile-oriented signatures for a tube layer over one of
`F.totalU`/`F.totalV` and for a complete family wrapper extending or containing
`AnalyticQuadraticLikeFamilyCore`.

Avoid duplicating fiber sections or Jordan-domain facts already provided through
`GenuineBMol`. Do not store properness, unfolding, equipment, straightening, or
connectedness conclusions.

State what theorem/field ensures the local trivializations commute with first
coordinate projection.

## E. Temporary compilation

Compile-test the recommended minimal tube structure and complete-family wrapper in
`/tmp` with `lake env lean`. If the appropriate Mathlib bundle API is too involved
or unavailable, compile-test the smallest honest project-local alternative and
state its limitations.

## F. Decision

Choose exactly one:

1. a source-faithful tube layer is ready for a small Lean implementation;
2. Mathlib bundle machinery needs one preliminary adapter;
3. the source is too ambiguous to formalize tube local triviality yet;
4. only the analytic core should be retained for the current renormalization-locus
   milestone.

Give the exact next worker task but do not create its file.

## Report contract

Include direct sources, exact API signatures, tested code and commands, compilation
outcomes, full `git status --short`, and confirmation that only the result artifact
was written and no commit was made.
