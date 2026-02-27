# PLAN v12: Nonseeded Local-Seam Gap Equivalence And Cutover

**Status:** `██████████` **100%**
**State:** `DONE`
**Relevance:** ⭐⭐⭐⭐⭐
**Last Updated:** 2026-02-27

## Goal
Refactor the remaining elimination blocker into a local-seam gap form and prove it is equivalent to the existing non-seeded root-safe gap.

## Completed
- Added local-seam gap interface:
  - `NonseededDirectProperToLocalSeamGapTwo`
- Added both-direction bridge to root-safe gap:
  - `nonseededDirectProperToRootSafeGapTwo_of_nonseededDirectProperToLocalSeamGapTwo`
  - `nonseededDirectProperToLocalSeamGapTwo_of_nonseededDirectProperToRootSafeGapTwo`
- Added equivalence theorem:
  - `nonseededDirectProperToRootSafeGapTwo_iff_nonseededDirectProperToLocalSeamGapTwo`
- Added cutover theorem from local-seam gap:
  - `mlc_conjecture_of_nonseededDirectProperToLocalSeamGapTwo_of_directProperLocalWitnessTwo`

## Outcome
- The blocker is now represented in two equivalent minimal formulations,
  improving target precision for witness search.
