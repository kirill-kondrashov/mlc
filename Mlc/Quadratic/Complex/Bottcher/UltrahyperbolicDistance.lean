import Mlc.Quadratic.Complex.Bottcher.UltrahyperbolicPullback

/-!
# Integrated Schwarz–Pick length bound for holomorphic maps into `ℂ \ {0,1}`

The pointwise contraction `pullback_density_contraction_exp` bounds the *infinitesimal* pulled-back
density `σ(f z)·‖f'z‖ ≤ 2/(1-‖z‖²)`.  This file integrates it along a **radial path** to obtain a
finite length bound: the `√(1/1000)·σ`-length of the image of the segment `[0,t₀]` under a
holomorphic immersion `f : 𝔻 → ℂ \ {0,1}` is at most `log((1+‖t₀‖)/(1-‖t₀‖))` — exactly the disk
Poincaré distance from `0` to `t₀`.

This is the *upper* half of the two-trajectory Mañé–Sad–Sullivan comparison: since two nearby
normalized `crossTrack` trajectories share an endpoint whose distance to the puncture `1` blows up,
a *finite* length bound (this file) plus the density blow-up near the puncture will confine the
other endpoint, giving continuity in the space variable.

## Main results

* `integral_poincare_model` — the model integral `∫₀¹ 2a/(1-a²s²) ds = log((1+a)/(1-a))` for
  `0 ≤ a < 1`, the exact Poincaré right-hand side.
* `path_deriv` — the real-parametrized chain rule
  `∂ₛ (f(s·t₀)) = t₀·f'(s·t₀)` for `f` analytic.
* `sigmaLength_radial_le` — the integrated Schwarz–Pick bound
  `∫₀¹ σ(f(s·t₀))·‖∂ₛ f(s·t₀)‖ ds ≤ log((1+‖t₀‖)/(1-‖t₀‖))`.
-/

open Complex Metric intervalIntegral

/-- **Model Poincaré integral.** `∫₀¹ 2a/(1-a²s²) ds = log((1+a)/(1-a))` for `0 ≤ a < 1`; this is
the disk Poincaré distance from `0` to a point of modulus `a`, obtained by integrating the disk
Poincaré density `2/(1-r²)` along the radius. -/
theorem integral_poincare_model {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    (∫ s in (0:ℝ)..1, 2 * a / (1 - a ^ 2 * s ^ 2)) = Real.log ((1 + a) / (1 - a)) := by
  have hden : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → (0:ℝ) < 1 - a ^ 2 * s ^ 2 := by
    intro s hs0 hs1
    have hp : 0 ≤ a * s := mul_nonneg ha0 hs0
    have hpa : a * s ≤ a := by nlinarith [mul_nonneg ha0 (sub_nonneg.2 hs1)]
    have heq : a ^ 2 * s ^ 2 = (a * s) ^ 2 := by ring
    rw [heq]; nlinarith [hp, hpa]
  have hF : ∀ s ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun s => Real.log (1 + a * s) - Real.log (1 - a * s))
        (2 * a / (1 - a ^ 2 * s ^ 2)) s := by
    intro s hs
    rw [Set.uIcc_of_le (by norm_num)] at hs
    obtain ⟨hs0, hs1⟩ := hs
    have has : a * s ≤ a := by nlinarith [mul_nonneg ha0 (sub_nonneg.2 hs1)]
    have hpos1 : (0:ℝ) < 1 + a * s := by nlinarith [mul_nonneg ha0 hs0]
    have hpos2 : (0:ℝ) < 1 - a * s := by nlinarith
    have hi1 : HasDerivAt (fun s => 1 + a * s) a s := by
      simpa using ((hasDerivAt_id s).const_mul a).const_add (1:ℝ)
    have hi2 : HasDerivAt (fun s => 1 - a * s) (-a) s := by
      simpa using ((hasDerivAt_id s).const_mul a).const_sub (1:ℝ)
    have hd := (hi1.log (ne_of_gt hpos1)).sub (hi2.log (ne_of_gt hpos2))
    convert hd using 1
    rw [div_sub_div _ _ (ne_of_gt hpos1) (ne_of_gt hpos2),
      div_eq_div_iff (ne_of_gt (hden s hs0 hs1)) (ne_of_gt (mul_pos hpos1 hpos2))]
    ring
  have hcont : ContinuousOn (fun s => 2 * a / (1 - a ^ 2 * s ^ 2)) (Set.uIcc (0:ℝ) 1) := by
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro s hs
    rw [Set.uIcc_of_le (by norm_num)] at hs
    exact ne_of_gt (hden s hs.1 hs.2)
  rw [integral_eq_sub_of_hasDerivAt hF hcont.intervalIntegrable]
  simp only [mul_zero, mul_one, Real.log_one, add_zero, sub_zero]
  exact (Real.log_div (ne_of_gt (by linarith)) (ne_of_gt (by linarith))).symm

namespace MLC.Quadratic

/-- **Real-parametrized chain rule.** For `f` analytic at `s·t₀`, the derivative of the radial
restriction `r ↦ f(r·t₀)` (a map `ℝ → ℂ`) at `s` is `t₀·f'(s·t₀)`. -/
theorem path_deriv (h : ℂ → ℂ) (t₀ : ℂ) (s : ℝ) (hh : AnalyticAt ℂ h (↑s * t₀)) :
    HasDerivAt (fun r : ℝ => h (↑r * t₀)) (t₀ * deriv h (↑s * t₀)) s := by
  have hφ : HasDerivAt (fun r : ℝ => (↑r * t₀ : ℂ)) t₀ s := by
    simpa using ((Complex.ofRealCLM.hasDerivAt (x := s)).mul_const t₀)
  have hd : HasDerivAt h (deriv h (↑s * t₀)) (↑s * t₀) := hh.differentiableAt.hasDerivAt
  simpa [smul_eq_mul, mul_comm] using hd.scomp s hφ

/-- **Integrated Schwarz–Pick length bound.** For a holomorphic immersion
`f : 𝔻 → ℂ \ {0,1}` (analytic, avoiding `0` and `1`, non-vanishing derivative on the unit disk),
the `√(1/1000)·σ`-length of the image of the radial segment `[0,t₀]` is at most the disk Poincaré
distance `log((1+‖t₀‖)/(1-‖t₀‖))`.  Obtained by integrating the pointwise contraction
`pullback_density_contraction_exp` against the model Poincaré integral. -/
theorem sigmaLength_radial_le {h : ℂ → ℂ} {t₀ : ℂ}
    (hh : ∀ z ∈ ball (0:ℂ) 1, AnalyticAt ℂ h z)
    (h0 : ∀ z ∈ ball (0:ℂ) 1, h z ≠ 0)
    (h1 : ∀ z ∈ ball (0:ℂ) 1, h z ≠ 1)
    (hfd : ∀ z ∈ ball (0:ℂ) 1, deriv h z ≠ 0)
    (ht : ‖t₀‖ < 1) :
    (∫ s in (0:ℝ)..1, ultraDensityScaled (h (↑s * t₀)) * ‖deriv (fun r:ℝ => h (↑r*t₀)) s‖)
      ≤ Real.log ((1 + ‖t₀‖) / (1 - ‖t₀‖)) := by
  set a := ‖t₀‖ with ha
  have ha0 : 0 ≤ a := norm_nonneg _
  have hmem : ∀ s : ℝ, s ∈ Set.Icc (0:ℝ) 1 → (↑s * t₀ : ℂ) ∈ ball (0:ℂ) 1 := by
    intro s hs
    rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]
    calc s * a ≤ 1 * a := by nlinarith [hs.2, ha0]
      _ = a := one_mul a
      _ < 1 := ht
  have hnorm_sq : ∀ s : ℝ, 0 ≤ s → ‖(↑s * t₀ : ℂ)‖ ^ 2 = a ^ 2 * s ^ 2 := by
    intro s hs
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs]; ring
  have hcongr : ∀ s ∈ Set.uIcc (0:ℝ) 1,
      ultraDensityScaled (h (↑s * t₀)) * ‖deriv (fun r:ℝ => h (↑r*t₀)) s‖
        = a * (ultraDensityScaled (h (↑s*t₀)) * ‖deriv h (↑s*t₀)‖) := by
    intro s hs
    rw [Set.uIcc_of_le (by norm_num)] at hs
    have hpd := path_deriv h t₀ s (hh _ (hmem s hs))
    rw [hpd.deriv, norm_mul, ha]; ring
  rw [integral_congr hcongr, ← integral_poincare_model ha0 ht]
  have hden : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → (0:ℝ) < 1 - a ^ 2 * s ^ 2 := by
    intro s hs0 hs1
    have hp : 0 ≤ a * s := mul_nonneg ha0 hs0
    have hpa : a * s ≤ a := by nlinarith [mul_nonneg ha0 (sub_nonneg.2 hs1)]
    have heq : a ^ 2 * s ^ 2 = (a * s) ^ 2 := by ring
    rw [heq]; nlinarith [hp, hpa]
  have hgh : ContinuousOn h (ball (0:ℂ) 1) := fun z hz => (hh z hz).continuousAt.continuousWithinAt
  have hcpath : ContinuousOn (fun s:ℝ => (↑s*t₀:ℂ)) (Set.Icc (0:ℝ) 1) := by fun_prop
  have hmaps : Set.MapsTo (fun s:ℝ => (↑s*t₀:ℂ)) (Set.Icc (0:ℝ) 1) (ball 0 1) :=
    fun s hs => hmem s hs
  have hmapsD : Set.MapsTo (fun s:ℝ => h (↑s*t₀)) (Set.Icc (0:ℝ) 1) ({0,1}ᶜ) := by
    intro s hs
    have hz := hmem s hs
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨h0 _ hz, h1 _ hz⟩
  have hsigD : ContinuousOn ultraDensityScaled ({0,1}ᶜ : Set ℂ) := by
    intro w hw
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hw
    exact ((Real.continuous_exp.continuousAt).comp
      (contDiffAt_ultraLogDensityScaled (n:=2) hw.1 hw.2).continuousAt).continuousWithinAt
  have hderivD : ContinuousOn (fun z => ‖deriv h z‖) (ball (0:ℂ) 1) := fun z hz =>
    (continuous_norm.continuousAt.comp (hh z hz).deriv.continuousAt).continuousWithinAt
  have hcontf : ContinuousOn
      (fun s : ℝ => a * (ultraDensityScaled (h (↑s*t₀)) * ‖deriv h (↑s*t₀)‖)) (Set.Icc (0:ℝ) 1) := by
    apply continuousOn_const.mul
    exact (hsigD.comp (hgh.comp hcpath hmaps) hmapsD).mul (hderivD.comp hcpath hmaps)
  have hcontg : ContinuousOn (fun s : ℝ => 2 * a / (1 - a ^ 2 * s ^ 2)) (Set.Icc (0:ℝ) 1) := by
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro s hs
    exact ne_of_gt (hden s hs.1 hs.2)
  apply integral_mono_on (by norm_num) (hcontf.intervalIntegrable_of_Icc (by norm_num))
    (hcontg.intervalIntegrable_of_Icc (by norm_num))
  intro s hs
  have hz : (↑s*t₀:ℂ) ∈ ball 0 1 := hmem s hs
  have hpc := pullback_density_contraction_exp hh h0 h1 hfd (mem_ball_zero_iff.1 hz)
  rw [hnorm_sq s hs.1] at hpc
  calc a * (ultraDensityScaled (h (↑s*t₀)) * ‖deriv h (↑s*t₀)‖)
      ≤ a * (2 / (1 - a ^ 2 * s ^ 2)) := mul_le_mul_of_nonneg_left hpc ha0
    _ = 2 * a / (1 - a ^ 2 * s ^ 2) := by ring

end MLC.Quadratic
