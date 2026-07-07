import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Completeness criterion for the corrected `ℂ ∖ {0,1}` cusp metric

`UltrahyperbolicMetric.lean` builds an explicit curvature `≤ -1` conformal density
on `ℂ ∖ {0,1}`, but records a completeness **obstruction**: its singularity
`∼ ‖w‖^{-5/6}` at a puncture has exponent `5/6 < 1`, so the radial distance
element is *finite* at the puncture and the metric is **not complete**. A complete
curvature `≤ -1` metric is exactly what confines distance-decreasing holomorphic
maps and yields strong Montel / the λ-lemma continuity step.

The classical fix is a `log`-corrected *cusp* density behaving like
`1 / (r · log(1/r))` near each puncture (`r = ‖w‖`). This file proves the single
analytic fact that makes the correction work: the radial length integral of that
cusp density **diverges**, i.e. the puncture is at *infinite* distance. Concretely,
`log (log (1/r))` is an antiderivative of `-(r · log(1/r))⁻¹` and tends to `+∞` as
`r → 0⁺`, so `∫₀ (r log(1/r))⁻¹ dr = +∞`.

This is `cusp-divergence`, the first brick of the completeness program that plugs
the obstruction. It is proved sorry-free and axiom-clean.
-/

namespace MLC.Quadratic.Hyperbolic

open Filter Topology Real

/-- The **cusp density** model `1 / (r · log(1/r))`, the radial profile of the
`log`-corrected complete metric near a puncture (`r = ‖w‖ ∈ (0,1)`). -/
noncomputable def cuspDensity (r : ℝ) : ℝ := (r * Real.log (1 / r))⁻¹

/-- `log (log (1/r))` is an antiderivative of `-cuspDensity` on `(0,1)`:
`d/dr log(log(1/r)) = -(r · log(1/r))⁻¹`. Hence the radial length element of the
cusp metric integrates to `log(log(1/r))`. -/
theorem hasDerivAt_logLogInv {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    HasDerivAt (fun r : ℝ => Real.log (Real.log (1 / r)))
      (-(cuspDensity r)) r := by
  have hrne : r ≠ 0 := ne_of_gt hr0
  -- inner map `r ↦ 1/r = r⁻¹`
  have hinv : HasDerivAt (fun r : ℝ => 1 / r) (-(r ^ 2)⁻¹) r := by
    simpa [one_div] using hasDerivAt_inv hrne
  have hinv_pos : (0 : ℝ) < 1 / r := by positivity
  -- `g r = log (1/r)`, `g' = (-(r^2)⁻¹)/(1/r) = -r⁻¹`
  have hg : HasDerivAt (fun r : ℝ => Real.log (1 / r)) (-r⁻¹) r := by
    have := hinv.log (ne_of_gt hinv_pos)
    have hsimp : -(r ^ 2)⁻¹ / (1 / r) = -r⁻¹ := by
      field_simp
    rwa [hsimp] at this
  -- outer `log`; need `log (1/r) ≠ 0`, true since `1/r > 1` for `0 < r < 1`
  have hlog_pos : 0 < Real.log (1 / r) := by
    apply Real.log_pos
    rw [lt_div_iff₀ hr0]; linarith
  have := hg.log (ne_of_gt hlog_pos)
  have hsimp : -r⁻¹ / Real.log (1 / r) = -(cuspDensity r) := by
    rw [cuspDensity]
    field_simp
  rwa [hsimp] at this

/-- **Completeness of the cusp metric (divergence of radial length).** The
antiderivative `log (log (1/r))` of the cusp density tends to `+∞` as `r → 0⁺`.
Equivalently, the radial distance `∫_r^{1/2} cuspDensity` to the puncture is
unbounded, so the `log`-corrected metric is complete at the puncture — exactly the
property the `‖w‖^{-5/6}` density of `UltrahyperbolicMetric.lean` lacks. -/
theorem tendsto_logLogInv_atTop :
    Tendsto (fun r : ℝ => Real.log (Real.log (1 / r))) (𝓝[>] (0 : ℝ)) atTop := by
  have h1 : Tendsto (fun r : ℝ => 1 / r) (𝓝[>] (0 : ℝ)) atTop := by
    simpa [one_div] using tendsto_inv_nhdsGT_zero
  exact Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp h1)

end MLC.Quadratic.Hyperbolic
