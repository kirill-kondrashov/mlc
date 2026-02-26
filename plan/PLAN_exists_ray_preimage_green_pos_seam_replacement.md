# Plan: Replace `exists_ray_preimage_green_pos_seam` With a Provable Target

---
**Status:** `█████████░` **90%** | **Relevance:** ⭐⭐⭐⭐⭐ | **Effort Remaining:** ~15-30 lines, 0.5-1.5 hrs
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
- [x] Confirmed downstream unconditional CP5 wrappers now consume the
  branch-combined seam path (no explicit no-landing detour needed on that branch).
- [x] Added constructive large-norm anchor-gap discharge and reduced full seam
  to a bounded annulus obligation:
  `greenRayLogGtAnchorTwo_of_norm_gt_cutoff`,
  `greenRayLogGtAnchorTwoSeam_of_cutoff_band`,
  with cutoff `greenRayLogGtAnchorTwoCutoff`.
- [x] Proved `not_greenRayLogGtAnchorTwoSeam` in `MainConjecture`, showing the
  current global seam is inconsistent at `c = 2`.
- [ ] Replace root wrappers to consume a new anchor-threshold seam target.

## Remaining Work (~15-30 lines)

```lean
def GreenRayLogGtAnchorThresholdTwoSeam : Prop :=
  ∀ w : ℂ, green_function (2 : ℂ) (((‖(2 : ℂ)‖ + 2 : ℝ) * (w / ↑‖w‖)) : ℂ) < Real.log ‖w‖ →
    ∃ ρ : ℝ, ρ > ‖(2 : ℂ)‖ + 2 ∧
      green_function (2 : ℂ) ((ρ : ℂ) * (w / ↑‖w‖)) = Real.log ‖w‖

theorem greenRayLogGtAnchorThresholdTwoSeam_constructive :
    GreenRayLogGtAnchorThresholdTwoSeam := by
  intro w hlog_gt_anchor
  exact exists_ray_preimage_green_pos (2 : ℂ) (w / ↑‖w‖) ?hu (Real.log ‖w‖) hlog_gt_anchor
```

Then replace:
```lean
-- remove
axiom greenRayLogGtAnchorTwo_axiom_seed : GreenRayLogGtAnchorTwoSeam
-- wire all wrappers through GreenRayLogGtAnchorThresholdTwoSeam
```
