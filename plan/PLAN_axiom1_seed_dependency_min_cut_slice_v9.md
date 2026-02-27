# PLAN v9: Seed Dependency Min-Cut Slice

**Status:** `██████████` **100%**
**State:** `DONE`
**Relevance:** ⭐⭐⭐⭐☆
**Last Updated:** 2026-02-27

## Goal
Isolate the minimal root entry dependency boundary around `greenRayLogGtAnchorTwo_seed`.

## Completed
- Added min-cut interface:
  - `SeedDependencyMinCutSliceTwo`
- Added canonical witness:
  - `seedDependencyMinCutSliceTwo_canonical`

## Outcome
- Seed dependency boundary is explicitly represented and stable for future cutover work.
