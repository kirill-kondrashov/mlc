# PLAN 09: Recommended Action Plan

**Status:** `ACTIVE`
**Priority:** ⭐⭐⭐⭐⭐

## Summary of Findings

After analyzing the codebase, we identified the root cause of being stuck:

1. The `bottcher_map` definition is incorrect (preserves `arg(z)` instead
   of using the true Böttcher angle)
2. This makes `ExternalRayMapData (2)` provably FALSE in the current model
3. The entire MLC proof is vacuous (`False.elim` from the axiom's falsity)
4. ALL previous v1-v30 attempts to constructively prove `ExternalRayMapData (2)`
   were doomed because the target is provably false

## Recommended Action Sequence

### Phase 1: Immediate (confirm the diagnosis)

1. **Verify the root cause** by running `#print axioms` and tracing the
   False.elim chain in Lean directly.

2. **Add a diagnostic comment** to `bottcher_map` documenting that it's
   a placeholder definition with incorrect angle behavior.

3. **Add a comment** to `false_of_bottcher_approach_to_one_seq_preimage_data_two`
   explaining that this lemma proves the CRUDE `bottcher_map` is not
   surjective at c=2, and that this is expected given the simplified
   definition.

### Phase 2: Short-term (smallest possible fix)

**Choose ONE of:**

#### Option A: Fix `bottcher_map` at c=2 only (Plan 01)

Scope: Moderate. Define `true_bottcher_map_two` using the sequence limit.
Prove surjectivity. BUT: still need to replace the `False.elim` chain
with real content. This option fixes the definition but doesn't complete
the proof.

#### Option B: Route through a provably-true ExternalRayMapData (Plan 07)

At c=0, `bottcher_map 0 z = z` (identity), so ExternalRayMapData(0) is
trivially true. If we can build a proof chain from ExternalRayMapData(0)
to MLC that has real content (not False.elim), we're done. But this
requires the hardest part: the actual MLC mathematics.

### Phase 3: Medium-term (the real work)

**The actual MLC proof needs mathematical content.** No matter which
plan we follow, we eventually need to prove at least one of:

1. **Yoccoz puzzle shrinking** (`PuzzleBoundaryMotionHyp`) — that
   para-puzzle pieces at finitely renormalizable parameters shrink to
   points. The Yoccoz library may already contain most of this.

2. **IR classification** (`IRClassificationData`) — that infinitely
   renormalizable parameters are either primitive or satellite tower.
   This may be a relatively simple combinatorial dichotomy if the
   right definitions are in place.

3. **Molecule bridge** — that the molecule conjecture implies satellite
   tower local connectivity. This involves Dudko-Lyubich renormalization
   theory.

### Phase 4: Long-term (correct architecture)

Replace the crude `bottcher_map` globally with the true Böttcher coordinate
(Plan 03), and build the MLC proof through the strategy decomposition
(Plan 02) or parameter ray landing (Plan 08).

## What NOT to Do

- ❌ Do NOT try to constructively prove `ExternalRayMapData (2)` — it's
  provably false with the current `bottcher_map` definition.
- ❌ Do NOT try to prove `DirectProperLocalWitnessTwo` — it implies
  surjectivity, which is false.
- ❌ Do NOT try any Green function inversion/monotonicity path — all lead
  to `ExternalRayMapData (2)`, which is false.
- ❌ Do NOT try to prove `BottcherSurjOnExterior (2)` — it's false.
- ❌ Do NOT repeat any v1-v30 approach — they all targeted a provably
  false goal.

## Decision Points

The key decision is: **fix the definition or build real mathematics?**

- If the Yoccoz library is mature enough, **building real mathematics**
  (Phase 3, options 1-2) may be faster than fixing the Böttcher map.
- If the Yoccoz library is NOT mature enough, **fixing the Böttcher map**
  at c=2 (Phase 2, option A) scopes the problem but still requires
  replacing the False.elim chain.

## Honest Assessment

Eliminating the axiom without introducing new ones is **NOT achievable by
small code changes**. It requires either:
- Significant new formalization of the Böttcher coordinate (Plan 01/03), or
- Significant new formalization of the MLC proof strategy (Plan 02/06)

Both are research-level projects. The previous v1-v30 plans were stuck
because they were trying to polish a fundamentally broken approach. The
new plans identify the true blocker and propose paths that address it.
