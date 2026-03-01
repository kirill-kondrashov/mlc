# PLAN 04: Direct Surjectivity Via Degree Theory

**Status:** `░░░░░░░░░░` **0%**
**State:** `PROPOSED`
**Difficulty:** Medium
**Risk:** Medium — mathematically sound, but requires new infrastructure.

## Core Idea

Instead of constructing a full inverse (ExternalRayMapData), prove only
`BottcherSurjOnExterior (2)` directly using **topological degree theory**.
This avoids the need for a correct Böttcher map definition — we prove
surjectivity of ANY reasonable map from the basin to the exterior.

The key insight: for c outside M, the basin of infinity is ℂ\K(c), and
any proper holomorphic map from ℂ\K(c) to ℂ\D̄ of degree 1 is surjective.

## Why This Might Work

The crude `bottcher_map` IS NOT surjective onto {|w| > 1} (as shown in the
root cause analysis). So we can't prove `BottcherSurjOnExterior (2)` for
the crude map.

BUT: we can define a DIFFERENT function that IS surjective and still provides
`BottcherSurjOnExterior (2)`. The idea:

```lean
-- True Böttcher coordinate at c=2 (definition can be noncomputable)
noncomputable def true_phi_two : ℂ → ℂ := ...

-- Prove it's surjective on the exterior
theorem true_phi_two_surj : ∀ w, 1 < ‖w‖ → ∃ z, true_phi_two z = w := ...

-- BUT: BottcherSurjOnExterior uses the crude bottcher_map, not true_phi_two
```

**Problem:** `BottcherSurjOnExterior (2)` is stated in terms of the crude
`bottcher_map`, which is NOT surjective. So degree theory on the true map
doesn't directly help.

## Alternative: Bypass BottcherSurjOnExterior

Instead of proving `BottcherSurjOnExterior (2)`, bypass it entirely.
The proof chain is:

```
BottcherSurjOnExterior (2)
  → BottcherApproachOneSeqFiberData (2)
  → BottcherApproachToOneSeqPreimageData (2)
  → False
  → MainPathData
  → MLC
```

Replace this with a direct route from the true Böttcher map to MLC:

```
True φ_2 is surjective
  → true approach-to-1 preimage data exists
  → ... (need to connect to MLC)
```

But this requires rebuilding the proof chain for the true map, which
essentially reduces to Plan 03.

## Degree Theory Approach (For the True Map)

If we define `true_phi_two` and want to prove surjectivity:

1. Show `true_phi_two` is holomorphic on ℂ\K(2)
2. Show it's proper (preimage of compact is compact) — follows from
   |φ(z)| = exp(G(z)) → ∞ as z → ∞
3. Show it has degree 1 near infinity (φ(z)/z → 1 as z → ∞)
4. By degree theory, a proper holomorphic map of degree 1 is surjective

This is cleaner than constructing the full inverse, but still requires
defining the true Böttcher coordinate.

## Minimal-Work Variant: Surjectivity Without Explicit φ

Prove surjectivity abstractly:
- The Green function G : ℂ\K(2) → (0, ∞) is surjective and proper
- For each Green level {G = t}, the level set is a Jordan curve (for t > 0)
- The Green function + angle coordinate gives a diffeomorphism from ℂ\K(2)
  to (0, ∞) × S¹ ≅ {|w| > 1}

This doesn't use the Böttcher coordinate at all! It uses:
- Surjectivity of the Green function (intermediate value theorem)
- Jordan curve property of Green level sets
- Angle coordinate from the harmonic conjugate

### Implementation

```lean
-- Green function is surjective onto (0, ∞) for c=2
theorem green_function_surj_two :
    ∀ t : ℝ, 0 < t → ∃ z, green_function (2 : ℂ) z = t

-- Level sets are connected (Jordan curves)
theorem green_level_connected_two (t : ℝ) (ht : 0 < t) :
    IsConnected {z : ℂ | green_function (2 : ℂ) z = t}
```

But connecting this to `BottcherSurjOnExterior (2)` still requires the crude
`bottcher_map`, which is the wrong map.

## Conclusion

Degree theory CAN prove surjectivity of the TRUE Böttcher map, but cannot
prove surjectivity of the crude `bottcher_map` (because it's false).
This plan reduces to Plan 01 or Plan 03: we must either fix the map
definition or bypass it entirely.

## Salvageable Subgoal

Even if this plan doesn't directly eliminate the axiom, the degree theory
infrastructure (holomorphic proper maps, topological degree in ℂ) would be
useful for Plan 03 Step 5 (proving surjectivity of the corrected map).
