# TASK 76 — Parameter exterior-coordinate uniformization gate

## Current blocker

The finite boundary graph foundation is complete, but Prompt 75 found no actual
parameter-plane external coordinate. The next theorem must address that source
gap directly.

## Audit

Determine whether the checked repository and Mathlib provide all ingredients
for a normalized conformal coordinate on `MandelbrotSetᶜ`:

1. the complement is an open unbounded domain;
2. the domain is simply connected/full in the required sense;
3. a Riemann mapping/uniformization theorem applies;
4. the map or inverse has a normalization at infinity;
5. a closed finite parameter ray/equipotential segment follows with continuity,
   injectivity, and exterior membership.

Use existing project axioms only for comparison/reporting; do not add any new
axiom or use the frozen straddling axiom.

## Action

If every hypothesis is proved and the relevant uniformization API exists,
implement the smallest non-axiomatic exterior-coordinate theorem and construct
one `BoundaryArc`.

Otherwise make no source edits and report the first missing theorem. The likely
blockers are:

- fullness/simple connectedness of `MandelbrotSetᶜ`;
- a usable unbounded Riemann mapping theorem;
- normalization at infinity;
- continuity of the inverse on the required closed arc.

## Constraints

- no `external_ray_map_exists`;
- no frozen para-puzzle alias;
- no placeholder coordinate;
- no new axiom, `sorry`, or `admit`;
- no provider or root migration yet;
- do not commit.

## Result

Write:

`plan/GPT54_RESULT_76_PARAMETER_EXTERNAL_COORDINATE_UNIFORMIZATION_GATE.md`
