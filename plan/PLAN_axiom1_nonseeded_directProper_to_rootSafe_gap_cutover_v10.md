# PLAN v10: Nonseeded DirectProper->RootSafe Gap Cutover

**Status:** `██████████` **100%**
**State:** `DONE`
**Relevance:** ⭐⭐⭐⭐⭐
**Last Updated:** 2026-02-27

## Goal
Isolate the exact non-seeded gap needed to move from `DirectProperLocalWitnessTwo` to `RootSafeOutsideOpenInjWitnessTwo`, and wire root closure through that gap.

## Completed
- Added gap interface:
  - `NonseededDirectProperToRootSafeGapTwo`
- Added root substitute constructor from the gap:
  - `rootClosureSubstituteTwo_of_nonseededDirectProperToRootSafeGapTwo_of_directProperLocalWitnessTwo`
- Added root closure theorem from the gap:
  - `mlc_conjecture_of_nonseededDirectProperToRootSafeGapTwo_of_directProperLocalWitnessTwo`
- Added route-matrix closure wrapper:
  - `mlc_conjecture_of_nonseededDirectProperToRootSafeGapTwo_of_directProperLocalWitnessTwoRouteMatrixV10`

## Outcome
- The elimination target is now explicit as one theorem obligation:
  `DirectProperLocalWitnessTwo -> RootSafeOutsideOpenInjWitnessTwo`.
