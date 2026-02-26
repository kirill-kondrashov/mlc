# Plan: Prove Green Function Radial Monotonicity at `c = 2`

---
**Status:** `██░░░░░░░░` **18%** | **Relevance:** ⭐⭐⭐⭐⭐ | **Effort Remaining:** ~120-200 lines, 4-8 hrs
**Target Axiom:** `green_function_strictMono_along_ray_basin_seam`
**Last Updated:** 2026-02-26
---

## Goal
Prove a non-axiom theorem replacing `MLC.Quadratic.green_function_strictMono_along_ray_basin_seam` at `c = 2`, eliminating it from `#print axioms MLC.mlc_conjecture`.

## Background

The current axiom asserts:
```lean
axiom green_function_strictMono_along_ray_basin_seam
    (c : ℂ) (u : ℂ) (hu : ‖u‖ = 1)
    {ρ₁ ρ₂ : ℝ} (hρ₁ : 0 < ρ₁) (h12 : ρ₁ < ρ₂)
    (hG : 0 < green_function c ((ρ₁ : ℂ) * u)) :
    green_function c ((ρ₁ : ℂ) * u) < green_function c ((ρ₂ : ℂ) * u)
```

For c=2, the Green function has an explicit Chebyshev-type formula that should make this tractable.

## What's Already Proved (In `GreenFunctionRayInversion.lean`)

- ✅ `green_function_strictMono_along_real_ray_two`: Strict monotonicity for **real ray** (u=1) at c=2
  - Uses orbit comparison for real ρ under f₂(x) = x² + 2
  - `f2_iterate_strictMono`: The real iterate is strictly monotone
- ✅ `green_function_neg_real_eq_two`: evenness on the real axis (`G₂(-ρ)=G₂(ρ)`)
- ✅ `green_function_strictMono_along_neg_real_ray_two`: strict monotonicity on
  the opposite real direction (`u=-1`)

## Current Sprint Delta

- Removed explicit no-landing dependency from unconditional strict-mono CP5
  theorem wrappers in `MainConjecture`; this narrows the remaining proof debt
  to the monotonicity theorem itself and keeps frontier pressure focused.
- Removed obsolete no-landing strict-mono helper aliases so the remaining debt
  is isolated to proving the constructive monotonicity theorem itself.
- Added constructive opposite-direction real-ray monotonicity lemmas to expand
  the non-axiomatic base before attacking general complex directions.
- Added constructive anchor-gap large-norm reduction (`greenRayLogGtAnchorTwo*`
  cutoff/band lemmas), reducing non-monotonicity proof debt to a bounded-annulus
  remainder on the anchor-gap side.
- Added `not_greenRayLogGtAnchorTwoSeam`, formally confirming the anchor-gap
  seam must be replaced (not proved), which sharpens this plan as the primary
  remaining mathematical proof target.

## Remaining Work (~120-200 lines)

### Phase 1: Chebyshev Representation (~50 lines)
```lean
-- Create: Mlc/Quadratic/Complex/Bottcher/ChebyshevStructure.lean

theorem orbit_two_chebyshev (n : ℕ) (z : ℂ) :
    orbit (2 : ℂ) z n = ... -- Chebyshev polynomial formula

theorem green_function_explicit_two (z : ℂ) (hz : ‖z‖ > 2) :
    green_function (2 : ℂ) z = Real.log (‖z + Complex.sqrt (z^2 - 4)‖) - Real.log 2
```

### Phase 2: Harmonic Analysis (~50 lines)
```lean
-- For fixed direction u, ρ ↦ G₂(ρ·u) has no local maxima (harmonic function)
theorem green_function_ray_harmonic (u : ℂ) (hu : ‖u‖ = 1) :
    ∀ ρ > 0, DifferentiableAt ℝ (fun r => green_function (2 : ℂ) (r * u)) ρ
```

### Phase 3: Iteration-Based Monotonicity (~100 lines)
```lean
theorem green_function_strictMono_along_ray_two (u : ℂ) (hu : ‖u‖ = 1)
    {ρ₁ ρ₂ : ℝ} (hρ₁ : ρ₁ > 4) (h12 : ρ₁ < ρ₂) :
    green_function (2 : ℂ) ((ρ₁ : ℂ) * u) < green_function (2 : ℂ) ((ρ₂ : ℂ) * u) := by
  -- Show log‖orbit(ρ₂·u)‖ - log‖orbit(ρ₁·u)‖ → ∞ as iteration deepens
  -- Use functional equation: G(f₂ⁿ(z)) = 2ⁿ · G(z)
```

### Phase 4: Final Integration
```lean
-- Replace axiom call with theorem for c=2 case
lemma green_function_strictMono_along_ray_basin ... := by
  exact green_function_strictMono_along_ray_two u hu ‹_› ‹_›
```

## Recommended Implementation Order

1. **Phase 3 first** (iteration-based) — builds on existing `GreenFunctionRayInversion.lean`
2. **Phase 1** (Chebyshev) if Phase 3 blocked
3. **Phase 4** for final integration

## Success Criteria

```bash
$ make check
All axioms used:
- Quot.sound
- propext  
- Classical.choice
# No green_function_strictMono_along_ray_basin_seam!
```
