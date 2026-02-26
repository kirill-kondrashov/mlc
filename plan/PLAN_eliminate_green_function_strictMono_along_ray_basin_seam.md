# Plan: Eliminate `MLC.Quadratic.green_function_strictMono_along_ray_basin_seam`

---
**Status:** `███████░░░` **76%** | **Relevance:** ⭐⭐⭐⭐ | **Effort:** ~200 lines, 4-6 hrs
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

## Key Blockers

All strict-mono-free alternatives are **provably impossible**:

```lean
theorem not_outsideOpenAnalyticityHypothesisTwo : ¬ OutsideOpenAnalyticityHypothesis (2 : ℂ)
theorem not_greenFunctionDegreeOneIngressTwo : ¬ GreenFunctionDegreeOneIngressTwo
theorem not_knownInjOnOutsideOpenSourceCandidateTwo : ¬ KnownInjOnOutsideOpenSourceCandidateTwo
```

**Conclusion: Must prove monotonicity directly.**

## Remaining Work (~200 lines)

The only path forward is to prove:
```lean
theorem green_function_strictMono_along_ray_basin_two (u : ℂ) (hu : ‖u‖ = 1)
    {ρ₁ ρ₂ : ℝ} (hρ₁ : 0 < ρ₁) (h12 : ρ₁ < ρ₂)
    (hG : 0 < green_function (2 : ℂ) ((ρ₁ : ℂ) * u)) :
    green_function (2 : ℂ) ((ρ₁ : ℂ) * u) < green_function (2 : ℂ) ((ρ₂ : ℂ) * u)
```

See `PLAN_prove_green_function_radial_monotonicity.md` for the proof strategy.
