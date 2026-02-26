# PLAN: Green function ray inversion at c=2

---
**Status:** `██████░░░░` **66%** | **Relevance:** ⭐⭐⭐⭐⭐ | **Effort:** ~150 lines, 3-4 hrs
**Target Axioms:** Both (indirectly provides theorems to eliminate them)
**Last Updated:** 2026-02-26
---

## Objective
Prove `Quadratic.ExternalRayMapData (2 : ℂ)` constructively by inverting the
Green function `G_2` along radial rays in the outside-open set `{‖z‖ > 4}`.

## Background

The repo's `bottcher_map 2 z = (z / ‖z‖) * exp(G_2(z))` is the "polar Green map":
it preserves the argument of z and scales the modulus by `exp(G_2(z))`. This map is
provably non-analytic (via `not_outsideOpenAnalyticityHypothesisTwo`).

`ExternalRayMapData (2 : ℂ)` asks for a two-sided inverse `f`:
- Right inverse: `bottcher_map 2 (f w) = w` for `‖w‖ > 1`
- Left inverse: `f (bottcher_map 2 z) = z` for `‖z‖ > 4`

## Key Lemmas Status

| Lemma | Statement | Status |
|-------|-----------|--------|
| A | `green_function_pos_on_basin` | ✅ **DONE** |
| B | `green_function_tendsto_atTop` | ✅ **DONE** |
| C (real) | `green_function_strictMono_along_real_ray_two` | ✅ **DONE** |
| C (real, opposite direction) | `green_function_strictMono_along_neg_real_ray_two` | ✅ **DONE** |
| C (complex) | `green_function_strictMono_along_ray_two` | ❌ **AXIOM** (target) |
| D | `exists_ray_preimage_green` | ✅ **DONE** (existence) |
| E | `external_ray_map_two_constructive` | ⏳ **BLOCKED** by C |

## What's Done (~400 lines already in GreenFunctionRayInversion.lean)

### Lemma A: Green function positivity
```lean
lemma green_function_pos_on_outside_open (c : ℂ) (z : ℂ) (hz : ‖z‖ > ‖c‖ + 2) :
    0 < Quadratic.green_function c z
```

### Lemma B: Green function tends to infinity
```lean
lemma green_function_tendsto_atTop (c : ℂ) :
    Tendsto (Quadratic.green_function c) atInfinity atTop
```

### Lemma C (real ray only)
```lean
lemma green_function_strictMono_along_real_ray_two {ρ₁ ρ₂ : ℝ} (h : ρ₁ < ρ₂)
    (hρ₁ : ρ₁ > 4) : green_function (2 : ℂ) ↑ρ₁ < green_function (2 : ℂ) ↑ρ₂
```
Proof uses orbit comparison for real inputs under f₂(x) = x² + 2.

### Lemma D: Ray preimage existence (IVT-based)
```lean
lemma exists_ray_preimage_green (c : ℂ) (u : ℂ) (hu : ‖u‖ = 1) (t : ℝ)
    (ht : t > green_function c ((‖c‖ + 2 : ℝ) * u)) :
    ∃ ρ : ℝ, ρ > ‖c‖ + 2 ∧ green_function c ((ρ : ℂ) * u) = t
```

## Remaining Work (~150 lines)

### Lemma C (complex rays) — Main Technical Gap
```lean
lemma green_function_strictMono_along_ray_two (u : ℂ) (hu : ‖u‖ = 1)
    {t₁ t₂ : ℝ} (ht₁ : t₁ > 4) (ht₂ : t₁ < t₂) :
    green_function (2 : ℂ) (↑t₁ * u) < green_function (2 : ℂ) (↑t₂ * u)
```

## Current Sprint Delta

- Rerouted theorem-level unconditional CP5 wrappers in `MainConjecture` to the
  branch-combined seam path, reducing non-essential no-landing detours while
  keeping the same axiom frontier.
- Removed dead strict-mono no-landing helper wrappers made obsolete by that
  reroute.
- Added constructive real-axis symmetry and opposite-direction monotonicity:
  `green_function_neg_real_eq_two`,
  `green_function_strictMono_along_neg_real_ray_two`.
- Added constructive anchor-gap large-norm reduction on the `c = 2` ingress
  side (in `MainConjecture`):
  `greenRayLogGtAnchorTwoCutoff`,
  `greenRayLogGtAnchorTwo_of_norm_gt_cutoff`,
  `greenRayLogGtAnchorTwoSeam_of_cutoff_band`.

**Approaches:**
1. **Iteration-based**: Show orbit norms separate for complex rays (harder than real case)
2. **Chebyshev formula**: Use explicit G₂(z) = log|z + √(z² - 4)| - log 2
3. **Harmonic analysis**: G is harmonic, so ρ ↦ G(ρ·u) has no local maxima

### Lemma E: External ray map construction
Once C is proved, construct:
```lean
theorem external_ray_map_exists_two_constructive :
    Quadratic.ExternalRayMapData (2 : ℂ)
```

## Related Files
- `Mlc/Quadratic/Complex/Bottcher/GreenFunctionRayInversion.lean` (771 lines)
- `Mlc/Quadratic/Complex/Axioms.lean` (contains the axiom to eliminate)
