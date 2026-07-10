# GPT-5.4 Worker Task 17: Specify analytic quadratic-like families on total spaces

**Repository:** `/home/kir/pers/mlc`
**Mode:** read-only mathematical and compile-oriented API audit
**Result file:** `plan/GPT54_RESULT_17_ANALYTIC_QUADRATIC_LIKE_FAMILY_TOTAL_SPACE_AUDIT.md`

## Safety

Write only the result report, via atomic rename. Do not edit Lean sources,
dependencies, plans, or prior artifacts; do not commit.

Read Results/Reviews 10, 14, and 16, plus `Mlc/GenuineBMol.lean` and the vendored
`Molecule/BMol.lean`.

## Goal

Specify the smallest honest analytic-family layer for quadratic-like maps over a
complex parameter domain. Model analyticity on the actual open total source space
of the family, not on all of `Λ × ℂ` and not through the discrete topology on
`BMol`.

## A. Source definition

Extract from the local Lyubich source (Chapter 10 §42 and any directly relevant
earlier definition) the precise meaning of a quadratic-like family/tube over
`Λ`. Identify:

- whether `Λ` is open/connected/Jordan;
- total spaces `𝒰, 𝒱 ⊆ Λ × ℂ` and their fibers;
- openness and projection/fiber requirements;
- joint holomorphicity of the evaluation map;
- how properness of the family differs from fiberwise properness;
- which data belong only to an equipped family.

Quote sparingly and give exact local page/section locations. Separate what the
source explicitly requires from a convenient Lean representation.

## B. Mathlib complex-analytic audit

Determine the correct Mathlib predicate for a complex-valued function on
`ℂ × ℂ` to be analytic/holomorphic on an open subset. Check scalar/module
instances and exact signatures for `AnalyticOn`, `DifferentiableOn ℂ`, and any
relevant product-space lemmas.

Clarify whether `AnalyticOn ℂ F totalU` is appropriate when `totalU` is open, or
whether a different predicate is preferable. Do not use `parameterSet ×ˢ univ`
unless the source truly requires a global spatial extension to be analytic.

## C. Total-space representation

Compare at least two representations:

1. store open total sets `totalU totalV : Set (ℂ × ℂ)` and define fibers by
   sections;
2. store `U V : ℂ → Set ℂ` and separately require openness of their sigma/total
   spaces.

Recommend one and give compile-oriented definitions for fiber extraction and
membership simp lemmas. Explain how the structure ensures fibers agree with
`GenuineBMol.toBMol.U/V/f` on parameters in `Λ`.

The family must include:

- `parameterSet : Set ℂ` with the appropriate openness/domain properties;
- `fiber : ℂ → GenuineBMol` or a scoped alternative;
- a joint evaluation map on `ℂ × ℂ`;
- agreement with each fiber map only where mathematically needed;
- analyticity on `totalU`.

Avoid storing connectedness, straightening, fullness, or conclusions as fields.

## D. Domain-scoping and off-domain fibers

Lean functions `fiber : ℂ → GenuineBMol` assign fibers outside `Λ`. Compare this
with a subtype-indexed map `fiber : parameterSet → GenuineBMol` and with total
functions plus on-domain laws. Assess ergonomics for sections, joint maps,
connectedness loci, and later root/tip boundary completion. Recommend one.

## E. Proper/unfolded/equipped boundary

Give separate proposed named predicates/structures for what is **not** part of the
minimal analytic family:

- proper family condition;
- unfolded/winding-one condition;
- holomorphic-motion equipment;
- tubing.

Only give concrete fields where the source and existing APIs support them. Mark
the exact missing foundations otherwise; do not hide them in generic `Prop`
fields.

## F. Temporary compilation

Compile-test the recommended minimal analytic-family structure, total-space fiber
definitions, and basic membership/agreement lemmas in `/tmp` using
`lake env lean`. Do not edit repository sources.

## G. Decision

Choose exactly one:

1. minimal analytic-family data are ready for a small Lean implementation;
2. total-space topology is ready but joint analyticity needs one preliminary
   Mathlib lemma/API layer;
3. the current `GenuineBMol` wrapper cannot be reconciled with varying total
   spaces without redesign.

Give the exact next worker task but do not create its file.

## Report contract

Include exact sources, signatures, commands, temporary compilation outcomes,
complete `git status --short`, and confirmation that only the result artifact was
written and no commit was made.
