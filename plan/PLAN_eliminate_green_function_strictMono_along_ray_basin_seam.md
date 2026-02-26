# Plan: Eliminate `MLC.Quadratic.green_function_strictMono_along_ray_basin_seam`

---
**Status:** `██████░░░░` **58%** | **Relevance:** ⭐⭐⭐⭐⭐ | **Effort Remaining:** ~90-130 lines, 2-4 hrs
**Target Axiom:** `green_function_strictMono_along_ray_basin_seam`
**Last Updated:** 2026-02-26
---

## Goal
Remove `MLC.Quadratic.green_function_strictMono_along_ray_basin_seam` from the axiom footprint of `MLC.mlc_conjecture`.

## Hard Constraints
- [x] Do not reintroduce `MLC.Quadratic.external_ray_map_exists` into the root path.
- [x] Keep `MLC.greenRayLogGtAnchorTwo_axiom_seed` unchanged for this plan.

## Current State (Verified)

```
make check shows:
- MLC.greenRayLogGtAnchorTwo_axiom_seed
- MLC.Quadratic.green_function_strictMono_along_ray_basin_seam
```

## Progress Summary

### Phase 1: Cut Strict-Mono at MainConjecture Root Call Site ✅ 100%
- [x] Replace body of `external_ray_map_exists_two_constructive` to use injectivity-based constructor
- [x] Provide root-safe witness for outside-open injectivity
- [x] Added strict-mono-free assumption-layer theorems
- [x] Isolated the exact remaining root target as `RootSafeOutsideOpenInjWitnessTwo`
- [x] Added centralized root-seed payload layer

### Phase 2: Keep the Frontier Safe While Supplying Injectivity ⏳ 50%
- [x] Route injectivity through degree-one ingress package
- [x] Added strict-mono-free root-candidate wrappers
- [x] Extended selector-layer strict-mono-free coverage
- [ ] **BLOCKED**: All strict-mono-free ingress sources are impossible:
  - `not_outsideOpenAnalyticityHypothesisTwo`
  - `not_greenFunctionDegreeOneIngressTwo`
  - `not_knownInjOnOutsideOpenSourceCandidateTwo`

### Phase 3: Retire Strict-Mono Dependency ❌ 0%
- [ ] Remove remaining call paths to legacy theorem
- [ ] Delete axiom from `Mlc/Quadratic/Complex/Axioms.lean`

### Latest Increment
- [x] Removed explicit no-landing dependency from unconditional CP5 strict-mono
  theorem wrappers by routing through the branch-combined seam.
- [x] Deleted obsolete strict-mono no-landing helper aliases no longer used by
  any root or CP5 wrapper path.
- [x] Added constructive opposite-direction real-ray monotonicity support in
  `GreenFunctionRayInversion` (`green_function_neg_real_eq_two`,
  `green_function_strictMono_along_neg_real_ray_two`).
- [x] Added constructive large-norm anchor-gap discharge and reduced full
  anchor seam to bounded annulus data (`greenRayLogGtAnchorTwoCutoff`,
  `greenRayLogGtAnchorTwo_of_norm_gt_cutoff`,
  `greenRayLogGtAnchorTwoSeam_of_cutoff_band`).
- [x] Added `not_greenRayLogGtAnchorTwoSeam` (in `MainConjecture`) to show the
  old global anchor-gap seam is inconsistent; strict-mono remains the sole
  substantive replacement proof debt on this branch.

## Key Blockers

All strict-mono-free alternatives are **provably impossible**:

```lean
theorem not_outsideOpenAnalyticityHypothesisTwo : ¬ OutsideOpenAnalyticityHypothesis (2 : ℂ)
theorem not_greenFunctionDegreeOneIngressTwo : ¬ GreenFunctionDegreeOneIngressTwo
theorem not_knownInjOnOutsideOpenSourceCandidateTwo : ¬ KnownInjOnOutsideOpenSourceCandidateTwo
```

**Conclusion: Must prove monotonicity directly.**

## Remaining Work (~90-130 lines)

The only path forward is to prove:
```lean
theorem green_function_strictMono_along_ray_basin_two (u : ℂ) (hu : ‖u‖ = 1)
    {ρ₁ ρ₂ : ℝ} (hρ₁ : 0 < ρ₁) (h12 : ρ₁ < ρ₂)
    (hG : 0 < green_function (2 : ℂ) ((ρ₁ : ℂ) * u)) :
    green_function (2 : ℂ) ((ρ₁ : ℂ) * u) < green_function (2 : ℂ) ((ρ₂ : ℂ) * u)
```

See `PLAN_prove_green_function_radial_monotonicity.md` for the proof strategy.
