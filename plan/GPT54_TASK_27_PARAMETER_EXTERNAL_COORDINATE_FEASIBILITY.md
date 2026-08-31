# GPT-5.4 Worker Task 27: Audit axiom-clean parameter external coordinate feasibility

**Repository:** `/home/kir/pers/mlc`
**Mode:** read-only dependency and Lean-signature audit
**Result file:** `plan/GPT54_RESULT_27_PARAMETER_EXTERNAL_COORDINATE_FEASIBILITY.md`

## Safety and route constraint

Write only the result report, via atomic rename. Do not edit Lean sources,
dependencies, plans, or prior artifacts; do not commit. Use `/tmp` for Lean probes.

Read Result/Review 26 and the focused progress report. Stay on the parameter-plane
external-coordinate route. Do not return to renormalization, tube bundles, frozen
Green sets, or connectivity packaging.

## Goal

Determine whether the current **axiom-clean** dynamical Böttcher development is
sufficient to define

```lean
parameterExternalCoord (c : {c : ℂ // c ∉ MandelbrotSet}) := B_c(c)
```

and prove that its value lies outside the closed unit disk. If not, identify the
single earliest missing theorem/definition.

## A. Candidate inventory and dependency audit

Inspect every plausible coordinate in `BottcherCore`, `BottcherOutsidePlan`, the
constructive basin files, parameter/joint analytic files, inverse files,
`BottcherOnMDefs/Theory`, `BottcherAxioms`, and proxy declarations.

For each candidate give its exact signature, mathematical domain, normalization,
and transitive dependence on `axiom`, `sorry`, `admit`, or hypothesis bundles.
Identify one preferred axiom-clean coordinate, if any. Do not treat structures
supplied as hypotheses as constructed coordinates.

## B. Domain bridge from `c ∉ MandelbrotSet`

Starting from the repository definition, prove or locate:

1. `c ∉ M` means the critical orbit of `0` escapes;
2. the critical value `c = f_c(0)` lies in the basin of infinity;
3. `c` lies in the preferred coordinate's domain;
4. its coordinate norm is strictly greater than `1`.

Separate orbit-shift facts from escape/basin theorems. Give exact signatures and
compile proofs in `/tmp` wherever APIs suffice.

## C. Definition shape

Compare a subtype-valued coordinate into `{w : ℂ // 1 < ‖w‖}`, an unbundled
complex-valued definition plus theorems, and a partial total function. Recommend
the smallest honest API for ray/equipotential preimages. Compile-test it. No
constants or axioms.

## D. Holomorphicity and conformality boundary

Audit continuity, analyticity on `ℂ \ M`, asymptotics, injectivity, surjectivity,
and conformal equivalence for `c ↦ B_c(c)`. Separate what definitions require from
later graph topology and landing. Do not import Theorem 6.10 as an axiom bundle.

## E. First implementation milestone

If definition plus norm proof are axiom-clean and compile, propose adding exactly
those declarations. If blocked, propose the earliest missing lemma with a concrete
proof path, not a property-carrying structure.

## F. Decision

Choose exactly one:

1. coordinate and outside-disk theorem are ready to implement;
2. coordinate evaluation is definable, but outside-disk theorem is missing;
3. evaluation at the critical value is blocked by the coordinate domain;
4. all usable candidates remain axiom/hypothesis dependent.

Give the exact next worker task but do not create its file.

## Report contract

Include exact declarations and dependency evidence, complete temporary Lean code
and outcomes, searches/commands, full status, and confirmation that only the result
artifact was written and no commit was made.
