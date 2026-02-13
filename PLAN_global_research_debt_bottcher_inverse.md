# Plan: Eliminate `MLC.Quadratic.quadratic_map_iter_eq_imp_eq`

## Status (2026-02-13)
- [ ] Not eliminated yet.
- [ ] `make check` still lists `MLC.Quadratic.quadratic_map_iter_eq_imp_eq`.
- [ ] Only remaining production use-site:
  `Mlc/MainConjecture.lean:272`.

## What Is Already Done
- [x] Main theorem wiring is parameterized:
  - `mlc_conjecture_of_iter_eq_imp`
  - `mlc_conjecture_of_iter_eq_imp_via_pullback_root`
  - `mlc_conjecture_of_quadratic_left_inverse`
  - `mlc_conjecture_of_pullback_root`
  - `mlc_conjecture_of_eventual_slit_global_extension`
- [x] Reduction chain from a basin left inverse of `quadratic_map` to iterate-equality implication is formalized.
- [x] Pullback-root formulation is formalized (`BasinQuadraticPullbackRoot` and consequences).
- [x] `mlc_conjecture` itself remains unchanged in signature (no extra hypotheses).
- [x] No new axioms were introduced in this line of work.
- [x] Viability check for the left-inverse target is now formalized:
  - `quadratic_map_not_injOn_basin`
  - `not_quadratic_map_left_inverse_on_basin`
  This shows `quadratic_map` is not injective on `basin_of_infinity c`, so a
  global basin left inverse cannot exist.

## Ruled-Out Routes (Formal Obstructions)
- [x] Escape-time candidate route is inconsistent:
  - `not_EventualSlitEscapeIterateLeftInverse`.
- [x] Current bridge predicate is inconsistent:
  - `not_EventualSlitGlobalInverseExtensionBridge`
  - `not_eventual_slit_global_bridge_data`.
- [x] Global fixed-slit and rotated-slit branch assumptions are inconsistent.
- [x] Global single-`sqrt` basin branch assumption is inconsistent.
- [x] Basin-wide left-inverse target is inconsistent with current dynamics model:
  - `quadratic_map_not_injOn_basin`
  - `not_quadratic_map_left_inverse_on_basin`.

## Remaining Work (Single Real Blocker)
- [ ] Reformulate the elimination target: the previous “prove a basin left inverse”
  route is impossible, so `quadratic_map_iter_eq_imp_eq` cannot be replaced by that
  statement.
- [ ] Identify and prove the minimal *true* replacement needed in the main path
  (`Mlc/MainConjecture.lean`), likely by avoiding any requirement equivalent to
  injectivity of `quadratic_map` on the whole basin.

## Execution Steps Left
- [ ] Step 1: Refactor the bottcher-injectivity chain so it does not depend on
  `quadratic_map_iter_eq_imp_eq` (or any equivalent basin-injective surrogate).
- [ ] Step 2: Replace the wrapper instantiation at `Mlc/MainConjecture.lean:272`
  with the refactored route.
- [ ] Step 3: Run `make check` and confirm `MLC.Quadratic.quadratic_map_iter_eq_imp_eq` disappears.
- [ ] Step 4: Run `scripts/verify_output.sh` and update README axiom section to match final output.

## Completion Checklist
- [ ] `rg -n "Quadratic\\.quadratic_map_iter_eq_imp_eq\\b" Mlc` has no production use-site in main MLC path.
- [ ] `make check` no longer reports `MLC.Quadratic.quadratic_map_iter_eq_imp_eq`.
- [ ] README axiom block is synchronized with final `make check` output.
