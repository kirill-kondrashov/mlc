# GPT-5.4 Worker Task 11: Audit the first quadratic-like family foundation

**Repository:** `/home/kir/pers/mlc`
**Mode:** read-only architecture and Lean-API audit
**Result file:** `plan/GPT54_RESULT_11_QUADRATIC_LIKE_FAMILY_FOUNDATION_AUDIT.md`

## Safety

Write only the result report, via atomic rename. Do not edit Lean sources, plans,
docs, notebooks, or prior artifacts; do not commit.

Read:

- `plan/GPT54_RESULT_10_RENORMALIZATION_LOCUS_SPECIFICATION.md`;
- `plan/GPT54_REVIEW_10_RENORMALIZATION_LOCUS_SPECIFICATION.md`;
- all existing `BMol`, quadratic-like, filled-Julia, and renormalization type APIs
  that are relevant to a parameter family.

## Goal

Design the smallest non-axiomatic Lean foundation for a quadratic-like parameter
family and its connectedness locus.  This is an API audit, not an implementation
task and not an attempt to formalize straightening or Theorem 10.15.

## A. Existing-type audit

Locate the exact definitions of `BMol`, its domain/codomain/fiber data, filled
Julia sets, Julia sets, connectedness predicates, `parameterToBMol`, and every
family-like or renormalization structure.  For each relevant declaration give:

- file and line;
- exact Lean signature;
- whether it is definitional, theorem-backed, or axiom-dependent;
- whether it can be reused without weakening the mathematics.

Do not propose a duplicate structure before completing this audit.

## B. Axiom/sorry audit

Trace dependencies for every candidate used in the milestone.  In particular,
identify whether connectedness of a filled Julia set, connectedness of
`MandelbrotSet`, or conversion from a parameter to `BMol` uses `axiom`, `sorry`,
`admit`, or an opaque hypothesis bundle.  A theorem that merely consumes
`mandelbrot_set_connected` is not a non-axiomatic milestone.

## C. Minimal family data

Propose one concrete Lean signature for the smallest useful family object.  Prefer
reusing `BMol` as the fiber type if faithful.  Separate raw data from mathematical
properties: do not use placeholder fields such as `quadraticLike : Prop`,
`motion : Prop`, or `properties : Prop` unless each is an already defined named
predicate whose contents are shown.

The proposal must state:

- parameter carrier/type and parameter domain;
- fiber map into an existing quadratic-like object, if possible;
- which continuity/holomorphic dependence is intentionally deferred;
- the exact connected-fiber predicate used by the locus.

If no honest connected-fiber predicate exists, identify the minimal missing
definition and give its intended expansion from existing objects.

## D. Connectedness locus milestone

Give compile-oriented declarations for:

1. the minimal family data;
2. `connectednessLocus`;
3. `mem_connectednessLocus_iff` proved by `rfl`/simplification or elementary set
   reasoning;
4. one concrete future consumer showing why the definitions are useful.

The milestone must introduce no axioms and assume neither straightening nor
connectedness of the locus.  Check names and namespace collisions against the
repository and Mathlib.  State required imports.

## E. Correct topology boundary

Record explicitly:

- an abstract homeomorphism between subspaces transports `IsConnected` once
  target connectedness is available;
- it does **not** in general transport planar fullness;
- the current repository status of non-axiomatic connectedness of
  `MandelbrotSet`;
- what stronger data or direct theorem would be required for fullness.

Do not propose the generic fullness lemma from Result 10.

## F. Decision and next task

Choose exactly one:

1. signatures are ready for a small Lean implementation task;
2. `BMol` needs one preliminary filled-Julia/connected-fiber definition;
3. existing foundations are too placeholder/axiom-dependent and require a deeper
   redesign.

Give the exact next worker task, but do not create its file.

## Report contract

Include exact commands, files inspected, full `git status --short`, and confirmation
that only the result artifact was written and no commit was made.
