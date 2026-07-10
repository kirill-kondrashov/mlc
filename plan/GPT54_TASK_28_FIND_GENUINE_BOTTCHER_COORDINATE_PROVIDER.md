# GPT-5.4 Worker Task 28: Find the genuine axiom-clean Böttcher coordinate provider

**Repository:** `/home/kir/pers/mlc`
**Mode:** read-only dependency and theorem audit
**Result file:** `plan/GPT54_RESULT_28_FIND_GENUINE_BOTTCHER_COORDINATE_PROVIDER.md`

## Safety and hard exclusion

Write only the result report, via atomic rename. Do not edit Lean sources,
dependencies, plans, or prior artifacts; do not commit. Use `/tmp` for Lean probes.

Read Result/Review 27.

`polar_green_map` and `proxy_bottcher_map` are explicitly excluded as providers of
the classical Böttcher coordinate. Their norm identities may be reused only as
Green-radius facts, never as external-angle or conjugacy facts.

Stay on the parameter external-coordinate route. Do not return to renormalization,
tubes, frozen Green pieces, or abstract connectivity packages.

## Goal

Determine whether the repository contains an actual axiom-clean Böttcher coordinate
`B_c` satisfying the dynamical conjugacy and normalization needed to define
`Φ_M(c)=B_c(c)` on `c ∉ M`. If it exists only near infinity, identify the exact
first missing theorem needed to extend/evaluate it at the critical value.

## A. Necessary acceptance criteria

A candidate counts as a genuine Böttcher coordinate only if checked theorems give,
on a mathematically specified domain:

1. holomorphicity/conformality or at least analyticity with nonzero derivative;
2. functional equation `B_c(f_c z) = (B_c z)^2`;
3. normalization `B_c(z)/z → 1` at infinity or an equivalent uniqueness
   normalization;
4. codomain outside the unit disk on the basin;
5. enough uniqueness to rule out arbitrary angle choices.

Audit exact signatures for every candidate and mark which criteria are proved.

## B. Constructive files and dependency trace

Inspect the complete implementations and imports of:

- product/log-series Böttcher files;
- near-infinity parameter and joint-analytic files;
- constructive basin coordinate files;
- inverse and parameter-inverse files;
- any monodromy/continuation or basin extension file;
- older axiom-backed Böttcher files.

For each candidate map, trace whether it is a `def`, a chosen witness from a proved
existence theorem, a structure supplied as a hypothesis, or an axiom. Search
transitive imports for `axiom`, `sorry`, and `admit` relevant to the candidate.

## C. Near-infinity versus full basin

If a genuine coordinate exists near infinity, state its exact domain and prove or
locate whether an escaping critical value `c` necessarily lies in that domain. It
usually need not lie in a fixed near-infinity region immediately.

Audit the standard extension formula using iterates and roots/functional equation:
what exact monodromy or branch-independence theorem is required to extend from near
infinity to the entire basin when the filled Julia set is disconnected?

Be careful: for `c ∉ M`, the basin may not admit a globally univalent coordinate
to the disk exterior without critical-point/covering qualifications. Match the
exact source theorem `Φ_M(c)=B_c(c)` and explain why evaluation at the critical
value remains well-defined even if a global basin coordinate has branching issues.

## D. Minimal next lemma

If an acceptable provider already exists, compile the exact definition of
`parameterExternalCoord` and the functional/norm facts it inherits.

If not, identify one earliest missing lemma with a concrete statement and proof
strategy. Do not propose a structure containing the five acceptance criteria as
fields and do not use the proxy as a fallback.

## E. Decision

Choose exactly one:

1. a genuine full provider exists and parameter evaluation is ready;
2. a genuine near-infinity provider exists, and one explicit continuation lemma is
   missing;
3. genuine constructions exist only as local/inverse fragments insufficient for
   evaluation at `c`;
4. all genuine providers are still axiom/hypothesis dependent.

Give the exact next worker task but do not create its file.

## Report contract

Include exact criteria evidence, declarations, dependency searches, temporary Lean
code/outcomes, full status, and confirmation that only the result artifact was
written and no commit was made.
