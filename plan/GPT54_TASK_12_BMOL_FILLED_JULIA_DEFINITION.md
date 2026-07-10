# GPT-5.4 Worker Task 12: Specify the intrinsic BMol filled Julia set

**Repository:** `/home/kir/pers/mlc`
**Mode:** read-only mathematical and Lean-API specification
**Result file:** `plan/GPT54_RESULT_12_BMOL_FILLED_JULIA_DEFINITION.md`

## Safety

Write only the result report, via atomic rename. Do not edit Lean sources, plans,
docs, dependencies, or prior artifacts; do not commit.

Read Result 11 and Supervisor Review 11 before beginning.

## Goal

Specify an intrinsic filled Julia set for `Molecule.QuadraticLikeMap` / `BMol`,
using the map and its domain rather than `MLC.Quadratic.K (criticalValue g)`.
Determine whether that definition and a minimal parameter-family connectedness
locus are ready for a small Lean implementation.

## A. Mathematical definition

Using a primary or standard authoritative source already available locally if
possible, pin the filled Julia set of a polynomial-like/quadratic-like map
`g : U → V`. State the iteration/domain convention precisely. Compare at least:

```text
{z | ∀ n, (g.f^[n]) z ∈ g.U}
{z ∈ g.U | ∀ n, (g.f^[n]) z ∈ g.U}
⋂ n, (g.f^[n]) ⁻¹' g.U
```

Explain their definitional/provable equivalence or any difference. Address the
fact that `g.f` is represented globally even though the quadratic-like map is
conceptually restricted to `U → V`.

Do not identify this set with `MLC.Quadratic.K (criticalValue g)`.

## B. Existing API and naming audit

Search the repository, Mathlib, and vendored dependencies for existing names such
as `filledJuliaSet`, `FilledJulia`, `nonEscapingSet`, or an iteration-domain API.
Report exact signatures and collisions. Inspect how `Function.iterate` is used in
the project and determine the imports needed.

Also audit whether the weak field `closure U ⊆ V` versus genuine compact
containment affects the *definition* (as opposed to later theorems). Flag the
issue; do not silently repair the dependency structure.

## C. Compile-oriented proposal

Give exact declarations, namespaces, and imports for:

1. an intrinsic `BMol` filled Julia set;
2. its membership equivalence;
3. an intrinsic connected-fiber predicate defined as `IsConnected` of that set;
4. a minimal `BMolParameterFamily (α : Type*)` with a parameter domain and fiber
   map;
5. its `connectednessLocus` and definitional membership lemma.

Prefer an explicit type parameter on the family structure over storing a universe
inside the structure unless compilation requires otherwise. Avoid every
placeholder `Prop` field.

Use a temporary file under `/tmp` to test the proposed declarations with
`lake env lean`. Do not add a repository source file.

## D. Normalized quadratic compatibility

Determine what can honestly be proved for `parameterToBMol c`:

- whether its intrinsic BMol filled Julia set is definitionally or propositionally
  equal to `MLC.Quadratic.K c`;
- whether the choice-based specification exposes enough equality of `f`, `U`, and
  `V` to prove that equality;
- whether `parameterToBMol_spec` must be strengthened to expose domains.

Do not claim compatibility merely from equality of critical values. If it is not
currently provable, give the exact missing specification theorem.

## E. Scope and decision

Separate the definitional milestone from later theorems:

- connectivity iff the critical point does not escape;
- invariance under hybrid conjugacy/straightening;
- connectedness or fullness of a parameter locus;
- holomorphic dependence of a family.

Choose exactly one:

1. intrinsic definitions compile and are ready for a small Lean implementation;
2. a precise representation issue in `QuadraticLikeMap` blocks an honest
   definition;
3. the definition works, but normalized-quadratic compatibility needs a separate
   strengthening first.

Give the exact next worker task but do not create its file.

## Report contract

Include sources, exact commands, temporary compilation results, complete
`git status --short`, and confirmation that only the result artifact was written
and no commit was made.
