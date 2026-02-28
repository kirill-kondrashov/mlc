# PLAN v27-A: Seed Dependency Boundary Cleanup

**Status:** `██████████` **100%**
**State:** `DONE`
**Relevance:** ⭐⭐⭐⭐⭐
**Last Updated:** 2026-02-28

## Goal
Make seed dependencies explicit in core seam/injectivity wrappers so the
remaining frontier debt is localized and measurable.

## Completed
- Added:
  - `greenFunctionStrictMonoAlongRayBasinTwo_of_greenRayLogGtAnchorTwoSeam`
  - `greenRayUniquePreimageTwoAnchorSeam_of_greenRayLogGtAnchorTwoSeam`
- Updated:
  - `injOn_outside_open_two_of_greenFunctionStrictMonoAlongRayBasinTwoSeam`
    now takes explicit `GreenRayLogGtAnchorTwoSeam` input.
  - `injOn_outside_open_two_strictMono_seeded` passes both seam seeds
    explicitly.
  - `injOn_outside_open_two_of_greenRayLogGtAnchorTwoSeam` now avoids
    hidden strict-mono seeded uniqueness replay.

## Outcome
- Hidden seed usage was reduced in key wrappers.
- The single unresolved debt is now more clearly: constructive replacement of
  seam/uniqueness bridge, not wrapper normalization.
