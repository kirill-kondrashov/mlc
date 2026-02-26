# Plan: Replace `exists_ray_preimage_green_pos_seam` With a Provable Target

---
**Status:** `████████░░` **83%** | **Relevance:** ⭐⭐⭐⭐ | **Effort:** ~50 lines, 1-2 hrs
**Target Axiom:** `greenRayLogGtAnchorTwo_axiom_seed` (partial)
**Last Updated:** 2026-02-26
---

## Goal
- [x] Replace the over-strong global-positive seam with an anchor-threshold seam.
- [x] Keep the external-ray constructive path independent of `external_ray_map_exists`.

## Why This Plan

The current unrestricted seam:
```
∀ c u (‖u‖ = 1) t>0, ∃ ρ>0, G_c((ρ:ℂ) * u) = t
```
is too strong globally. For some parameters/directions, the ray profile can have a positive minimum, so small positive `t` may not be attained.

## Exact Statement Replacement (Draft)

Replace with anchor-threshold target:
```lean
∀ c u (‖u‖ = 1) t,
  t > G_c(((‖c‖+2):ℝ) * u) →
  ∃ ρ, ρ > ‖c‖+2 ∧ G_c((ρ:ℂ) * u) = t
```

This aligns with the already formalized `exists_ray_preimage_green`.

## Progress

- [x] Seam-free conditional replacement implemented
- [x] MainConjecture wrapper added
- [x] Rooted conditional wrappers added
- [ ] Prove the anchor-threshold theorem for c=2

## Remaining Work (~50 lines)

```lean
theorem greenRayLogGtAnchorTwo_constructive : GreenRayLogGtAnchorTwoSeam := by
  intro w hw
  -- Key: G₂(4·(w/‖w‖)) < log‖w‖ for all ‖w‖ > 1
  -- Use bound: G₂(z) ≤ log‖z‖ + C for explicit C
  -- For c=2: C = 4/9
  -- So G₂(4·u) ≤ log 4 + 4/9 ≈ 1.83
  -- For ‖w‖ > 4.5: log‖w‖ > 1.5 > needed
  -- For 1 < ‖w‖ ≤ 4.5: case analysis or tighter bound
```

Then replace:
```lean
theorem greenRayLogGtAnchorTwo_seed : GreenRayLogGtAnchorTwoSeam :=
  greenRayLogGtAnchorTwo_constructive  -- was: greenRayLogGtAnchorTwo_axiom_seed
```
