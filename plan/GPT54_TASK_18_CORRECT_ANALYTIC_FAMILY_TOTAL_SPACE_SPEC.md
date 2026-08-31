# GPT-5.4 Worker Task 18: Correct the analytic-family total-space specification

**Repository:** `/home/kir/pers/mlc`
**Mode:** read-only corrective source/API audit
**Result file:** `plan/GPT54_RESULT_18_CORRECT_ANALYTIC_FAMILY_TOTAL_SPACE_SPEC.md`

## Safety

Write only the result report, via atomic rename. Do not edit Lean sources,
dependencies, plans, or prior artifacts; do not commit. Use `/tmp` for extraction
and Lean compilation tests.

Read Task 17, Result 17, and Supervisor Review 17.

## A. Direct source extraction

Directly inspect `refs/Conformal Geometry and Dynamics of Quadratic Polynomials.pdf`
around Chapter 10 §42. Extract the exact definitions of:

- a tube over `Λ` and its fibers;
- a quadratic-like family;
- properness of a family;
- equipment/holomorphic motion and tubing.

Give exact PDF/text page or extracted-line locations and short compliant quotes.
State whether total spaces contain only points over `Λ`, whether their projections
are all of `Λ`, and what openness/fiber topology is required. Do not rely solely
on prior result summaries.

## B. Correct total-space scoping

Design a Lean representation in which `totalU` and `totalV` cannot have unrelated
components over parameters outside `parameterSet`.

Compare:

1. total sets plus projection-containment and section-equality laws;
2. total sets defined from subtype-indexed fiber domains;
3. an open ambient total set intersected with `parameterSet ×ˢ univ`.

Recommend the smallest representation that matches the source. Include any
surjectivity/nonempty-fiber property required by “tube over `Λ`”. Be precise about
open sets when `parameterSet` itself is open.

## C. Separate stored and derived data

The structure may store primitive data and laws only. Define section sets outside
the structure, for example in its namespace, and prove membership lemmas there.
Do not store `fiberU`, `fiberV`, or tautological membership equivalences as fields.

Give a corrected compile-oriented structure containing only:

- parameter domain data;
- subtype-indexed genuine fibers;
- scoped open total spaces;
- a global representative of the joint evaluation map;
- fiber/total-space agreement laws;
- analyticity on the actual total source.

Explain why using a global representative is harmless although only its restriction
to the total source is mathematical.

## D. Fiber agreement and redundancy

Determine whether storing both total spaces and `fiber : parameterSet → GenuineBMol`
creates acceptable proof-carrying redundancy or whether one should be derived from
the other. Check which direction is easiest in Lean while preserving openness and
the existing `GenuineBMol` API.

Specify exact laws for `U`, `V`, and `f`. Ensure equality/agreement is stated only
where meaningful but is strong enough to rule out incoherent family data.

## E. Temporary Lean compilation

Compile the corrected structure plus external section definitions, `[simp]`
membership lemmas, projection/scoping lemmas, and evaluation agreement lemma in a
temporary file with `lake env lean`.

Report the complete tested code, command, and result. Check that no field has a
default implementation that makes derived data overridable.

## F. Decision

Choose exactly one:

1. corrected minimal family data are ready for implementation;
2. source tube semantics require one further topology abstraction;
3. storing both total spaces and `GenuineBMol` fibers is fundamentally unsuitable.

Give the exact next worker task but do not create its file.

## Report contract

Include exact sources, extraction commands, complete temporary code and compilation
outcome, full `git status --short`, and confirmation that only the result artifact
was written and no commit was made.
