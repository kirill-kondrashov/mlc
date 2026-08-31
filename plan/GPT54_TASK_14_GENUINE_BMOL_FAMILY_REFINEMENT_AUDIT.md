# GPT-5.4 Worker Task 14: Audit a genuine BMol family refinement layer

**Repository:** `/home/kir/pers/mlc`
**Mode:** read-only architecture and compile-oriented Lean API audit
**Result file:** `plan/GPT54_RESULT_14_GENUINE_BMOL_FAMILY_REFINEMENT_AUDIT.md`

## Safety

Write only the result report, via atomic rename. Do not edit Lean sources,
vendored dependencies, plans, or prior artifacts; do not commit.

Read:

- `Mlc/BMolFilledJulia.lean`;
- `plan/GPT54_RESULT_13_IMPLEMENT_BMOL_FILLED_JULIA_FOUNDATION.md`;
- `plan/GPT54_REVIEW_13_IMPLEMENT_BMOL_FILLED_JULIA_FOUNDATION.md`;
- the vendored `Molecule/BMol.lean` definition;
- Result 10's normalized Theorem 10.1 input package.

## Goal

Design the smallest honest local refinement over the existing vendored `BMol`
that can eventually support a Lyubich-style quadratic-like parameter family.
Address genuine relative compactness and parameter dependence explicitly without
editing the dependency or using its discrete topology as analytic structure.

## A. Mathematical and Mathlib audit

Pin the precise conditions on a quadratic-like map `g : U → V` relevant here:

- `U` and `V` topological disks / simply connected domains;
- genuine `U ⊂⊂ V` relative compactness;
- proper holomorphic degree two map.

Compare those with every current `QuadraticLikeMap` field. Determine the exact
missing property. Search Mathlib for the canonical formulation and names for
relative compactness, compact closure, and compact containment. Give exact
signatures and imports.

Distinguish a merely strict subset from compact containment. Do not treat
`closure U ⊆ V` alone as sufficient on an unbounded ambient space.

## B. Refinement design without vendored edits

Compare at least these local designs:

1. a named predicate on `BMol`, such as compactness of `closure g.U` in addition
   to the existing inclusion;
2. a structure bundling `g : BMol` with that proof;
3. a subtype of `BMol` satisfying the predicate.

Recommend one based on downstream usability, coercions, namespaces, and the need
to reuse `filledJuliaSet`. Provide compile-oriented Lean signatures. Avoid opaque
placeholder propositions: every field/predicate must expand to concrete topology.

State whether the existing “degree two” encoding (unique simple critical point)
is sufficient for this foundation layer or requires a separate future correction.

## C. Honest parameter dependence

The vendored `BMol` has a discrete placeholder topology. Do not use
`Continuous F.map` or `Holomorphic F.map` into that topology as the intended
family condition.

Propose an explicit pointwise/joint family representation over a complex
parameter domain, including at minimum:

- parameter set `Λ : Set ℂ`;
- fiber domains `U λ`, `V λ` or a refined `BMol` fiber;
- a joint evaluation map `g : ℂ → ℂ → ℂ` (or equivalent);
- the concrete analytic predicate Mathlib can express for dependence on `λ` and
  `z`, clearly separating what is ready now from what needs new foundations.

Compare this with the implemented `BMolParameterFamily`. Explain whether to
extend it, wrap it, or introduce a separate analytic-family structure. Do not
store conclusions such as connectedness or straightening as fields.

## D. Import and compilation audit

Test whether `Mlc/BMolFilledJulia.lean` can replace
`import Mlc.RenormalizationTypes` with a smaller direct import without changing
its declarations. Use a `/tmp` copy/test and `lake env lean`; do not edit the repo.

Also compile-test the recommended refinement and family skeleton in `/tmp`.
Report exact commands and outcomes.

## E. Source-to-field map

Map each Theorem 10.1 requirement to one of:

- already represented faithfully;
- handled by the proposed refinement;
- intentionally deferred (proper family, unfolded/winding one, equipment,
  holomorphic motion, tubing);
- blocked by a named missing Mathlib/project foundation.

This task must not claim that the skeleton already satisfies Theorem 10.1.

## F. Decision

Choose exactly one:

1. a small local refinement/import-cleanup implementation is ready;
2. relative compactness is ready but analytic-family representation needs a
   separate audit;
3. the vendored `BMol` representation is too weak to refine safely without
   upstream redesign.

Give the exact next worker task but do not create its file.

## Report contract

Include sources, exact declarations, temporary compilation evidence, exact files
and commands inspected, full `git status --short`, and confirmation that only the
result artifact was written and no commit was made.
