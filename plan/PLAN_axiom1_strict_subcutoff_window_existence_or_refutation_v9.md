# PLAN v9: Strict Subcutoff Window Existence Or Refutation

**Status:** `██████████` **100%**
**State:** `DONE (refutation branch completed)`
**Relevance:** ⭐⭐⭐⭐⭐
**Last Updated:** 2026-02-27

## Goal
Either construct a strict-subcutoff nonimplicative window witness, or refute this route cleanly and retire it.

## Completed
- Added strong local-window no-go:
  - `not_nonimplicativeWindowInterfaceTwo_of_one_lt_radius`
- Added strict-subcutoff existence refutation:
  - `not_strictSubcutoffWindowExistenceTwo`
- Added refutation transfers:
  - `not_partialWindowNotCoveringCutoffWithNontransportedTailTwo`
  - `not_constructPartialWindowWitnessDirectlyWithoutTransportTwo`

## Outcome
- This branch is closed on the **refutation** side; strict-subcutoff window
  existence is unavailable in the current model.

## Dead-End / Self-Repetition Check
- Additional attempts to construct strict-subcutoff windows would repeat a
  formally blocked route unless the model assumptions change.
