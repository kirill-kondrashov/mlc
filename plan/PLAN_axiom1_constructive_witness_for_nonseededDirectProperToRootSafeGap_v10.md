# PLAN v10: Constructive Witness For Nonseeded DirectProper->RootSafe Gap

**Status:** `██████░░░░` **60%**
**State:** `STUCK`
**Relevance:** ⭐⭐⭐⭐⭐
**Last Updated:** 2026-02-27

## Goal
Construct a frontier-safe proof of:
`DirectProperLocalWitnessTwo -> RootSafeOutsideOpenInjWitnessTwo`.

## Completed
- Introduced explicit target interface:
  - `NonseededDirectProperToRootSafeGapTwo`
- Added seeded fallback marker:
  - `nonseededDirectProperToRootSafeGapTwo_seeded_fallback`

## Dead-End / Self-Repetition Check
- Existing known non-seeded source families for outside-open injectivity are
  already blocked/inconsistent in the current model.
- Route-matrix repackaging is now proven collapsed; repeating those routes will
  not produce new witnesses.

## Blocking Gap
- Missing a new constructive mechanism for outside-open injectivity that does
  not depend on `greenRayLogGtAnchorTwo_seed`.

## Keep/Remove Decision
- **Keep** this stuck file as anti-repetition guardrail until a genuinely new
  injectivity source appears.
