# GPT-5.4 Worker Task 10: Specify the connected renormalization locus

**Repository:** `/home/kir/pers/mlc`  
**Mode:** read-only research/architecture task  
**Result file:** `plan/GPT54_RESULT_10_RENORMALIZATION_LOCUS_SPECIFICATION.md`

## Safety and communication

Write only the result report, via atomic rename. Do not edit repository sources,
plans, docs, notebooks, or prior artifacts; do not commit.

Use the local primary/expository source
`refs/Conformal Geometry and Dynamics of Quadratic Polynomials.pdf`, especially:

- Chapter 7 §45.2.1, Propositions 7.41–7.42;
- Chapter 10 §§42.1–42.3, Theorem 10.1 and Corollary 10.3;
- Chapter 10 §43, Theorem 10.15.

## Goal

Correct Task 09 by specifying the connected **renormalization locus inside a
window**, not merely the ambient connected window. Determine whether this locus
can furnish a restricted, genuine parameter-piece family useful to the existing
local-connectivity route.

## A. Separate the three sets

For one primitive superattracting base parameter of period `p > 1`, define on
paper and compare:

1. the open complex renormalization window `W°`/`Λ`;
2. `Λ ∩ MandelbrotSet`;
3. the source's renormalization/connectedness locus `M°` or `M(g)`.

Give exact source definitions. State every proved inclusion/equality among these
sets and flag anything not stated. In particular, do not assume
`M° = Λ ∩ M` unless the source proves it.

Explain which set Theorem 10.15 says is canonically homeomorphic to `M` and why
that yields connectedness.

## B. Normalize the quadratic-like family data

Extract the exact mathematical data required by Theorem 10.1:

- parameter domain `Λ`;
- quadratic-like family `g_λ : U_λ → U'_λ`;
- properness;
- unfolded/winding-one condition;
- equipment/holomorphic motion of the fundamental annulus;
- tubing and connectedness locus `M(g)`.

For the primitive complex window, identify which propositions construct each
item and where root/tip completion enters Theorem 10.15.

## C. Lean-facing definitions—not constants or axioms

Propose signatures using `def`/`structure` for mathematical data and theorems for
properties. Do not propose bare `constant` declarations.

At minimum specify:

1. `QuadraticLikeFamilyData` (or reuse an exact existing repository structure if
   present);
2. `connectednessLocus : QuadraticLikeFamilyData → Set ℂ` defined by connected
   filled Julia set;
3. a concrete restricted primitive-window family constructor;
4. `PrimitiveRenormalizationLocus` including the source-prescribed root/tip
   completion;
5. the straightening map and homeomorphism theorem corresponding to Theorem
   10.15;
6. connectedness/fullness corollaries derived from the homeomorphism, not stored
   as structure fields.

For each declaration label existing repository support, Mathlib support, sourced
theorem, missing foundation, or open mathematics.

Search existing renormalization/tower/quadratic-like structures before proposing
new duplicates.

## D. Downstream usefulness test

Determine exactly what the locus provides to `LcAtOfShrink`:

- Does it contain the chosen base parameter?
- Is it a relative neighborhood of the base in `M`, or only a compact copy?
- Can varying depth/combinatorics give an antitone family?
- What theorem would show intersection shrinks to `{c}`?
- Which parameter classes can use this family?

Separate finite hyperbolic validation from the infinitely-renormalizable nested
little-copy route. If one window does not furnish a neighborhood basis, say so.

Do not claim that connectedness of one little copy proves local connectivity.

## E. First honest Lean milestone

Propose one theorem whose implementation would add real foundations without
assuming straightening, connectivity, or exact target equality. Candidate shapes
include:

- define a connectedness locus from an already existing quadratic-like-family
  structure;
- prove a purely definitional membership equivalence;
- prove that a supplied homeomorphism from a locus to `M` implies locus
  connectedness/fullness as a generic topology lemma.

The milestone must have a concrete future consumer and must not merely restate
Theorem 10.15 as a hypothesis bundle.

Estimate feasibility and identify the first missing foundation after it.

## F. Decision

Choose exactly one:

1. ready for a small Lean foundation task;
2. architecture ready but quadratic-like family foundations missing;
3. source equality/inclusion unresolved;
4. unsuitable for the local-connectivity consumer.

Give the exact next worker task but do not create its file.

## Report contract

Include:

1. executive decision;
2. three-set comparison with exact sources;
3. normalized Theorem 10.1/10.15 inputs;
4. repository foundation inventory;
5. Lean-facing definitions and dependency labels;
6. downstream usefulness analysis;
7. first honest milestone and feasibility;
8. final decision and next task;
9. exact commands/search limitations;
10. complete `git status --short` and no-edit/no-commit confirmation.

The final result file is the completion signal. Stop afterward.
