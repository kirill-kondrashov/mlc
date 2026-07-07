/-
Analytic inverse of the near-infinity Böttcher coordinate.

This file builds the FIRST genuine holomorphic inverse of the sound
Böttcher coordinate `logSeriesBottcherApprox` near infinity, via the reciprocal
coordinate `recipBottcher c w = (φ_c (w⁻¹))⁻¹` (extended by `0` at `0`):

* `recipBottcher_analyticAt_zero` — `recipBottcher c` is holomorphic at `0`
  (Riemann removable singularity: it is bounded and holomorphic on a punctured
  neighborhood of `0`).
* `recipBottcher_deriv_zero` — its derivative at `0` is `1`, obtained *directly*
  from the normalization `φ_c(z)/z → 1` (no series-derivative estimate needed).
* `recipBottcher_exists_analytic_inverse` — hence (Mathlib's analytic inverse
  function theorem) `φ_c` is injective near `∞` and admits an analytic inverse.

This is the analytic base for a genuine non-trivial `HolomorphicMotion` of
exterior boundary points `c ↦ Φ_c⁻¹(ω)` (route-M attack on axiom A).
-/
import Mlc.Quadratic.Complex.Bottcher.BottcherParamHolo
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic

namespace MLC
open Quadratic Complex Topology Set Filter Metric

lemma norm_inv_gt_of_mem_punctured (c : ℂ) {w : ℂ}
    (hw : w ∈ ball (0 : ℂ) (‖c‖ + 2)⁻¹ \ {0}) :
    ‖c‖ + 2 < ‖w⁻¹‖ := by
  have hpos : (0 : ℝ) < ‖c‖ + 2 := by positivity
  have hw0 : w ≠ 0 := by have := hw.2; simpa using this
  have hlt : ‖w‖ < (‖c‖ + 2)⁻¹ := by
    have := hw.1; simpa [mem_ball, dist_eq_norm] using this
  have hwpos : 0 < ‖w‖ := norm_pos_iff.2 hw0
  rw [norm_inv, lt_inv_comm₀ hpos hwpos]; exact hlt

/-- The exterior region `{‖z‖ > ‖c‖+2}` is open. -/
lemma isOpen_exterior (c : ℂ) : IsOpen {z : ℂ | ‖c‖ + 2 < ‖z‖} :=
  isOpen_lt continuous_const continuous_norm

/-- `φ_c` is nonzero on the exterior region. -/
lemma logSeriesBottcherApprox_ne_zero_exterior (c : ℂ) {z : ℂ}
    (hz : ‖c‖ + 2 < ‖z‖) : logSeriesBottcherApprox c z ≠ 0 := by
  have h1 : 1 < ‖logSeriesBottcherApprox c z‖ :=
    one_lt_norm_logSeriesBottcherApprox_of_outside_open c (by linarith)
  intro h; rw [h, norm_zero] at h1; linarith

/-- `w ↦ (φ_c (w⁻¹))⁻¹` is differentiable on the punctured ball. -/
lemma recipBottcher_differentiableOn_punctured (c : ℂ) :
    DifferentiableOn ℂ (fun w => (logSeriesBottcherApprox c w⁻¹)⁻¹)
      (ball (0 : ℂ) (‖c‖ + 2)⁻¹ \ {0}) := by
  intro w hw
  have hw0 : w ≠ 0 := by have := hw.2; simpa using this
  have hgt : ‖c‖ + 2 < ‖w⁻¹‖ := norm_inv_gt_of_mem_punctured c hw
  -- w ↦ w⁻¹ differentiable at w
  have hinv : DifferentiableAt ℂ (fun w : ℂ => w⁻¹) w :=
    (hasDerivAt_inv hw0).differentiableAt
  -- φ_c differentiable at w⁻¹
  have hphi : DifferentiableAt ℂ (logSeriesBottcherApprox c) w⁻¹ := by
    have hdo := logSeriesBottcherApprox_differentiableOn_large_radius c (le_refl (‖c‖ + 2))
    exact (hdo.differentiableAt ((isOpen_exterior c).mem_nhds hgt))
  have hcomp : DifferentiableAt ℂ (fun w => logSeriesBottcherApprox c w⁻¹) w :=
    hphi.comp w hinv
  have hne : logSeriesBottcherApprox c w⁻¹ ≠ 0 :=
    logSeriesBottcherApprox_ne_zero_exterior c hgt
  exact (hcomp.inv hne).differentiableWithinAt



/-- Bridge: `w ↦ w⁻¹` sends the punctured nhds of `0` to `atInfinity`. -/
lemma tendsto_inv_nhdsNE_atInfinity : Tendsto (fun w : ℂ => w⁻¹) (𝓝[≠] 0) atInfinity := by
  rw [atInfinity, tendsto_comap_iff]
  exact tendsto_norm_inv_nhdsNE_zero_atTop

/-- `z / φ_c(z) → 1` at infinity. -/
lemma tendsto_div_logSeriesBottcherApprox_atInfinity (c : ℂ) :
    Tendsto (fun z => (logSeriesBottcherApprox c z / z)⁻¹) atInfinity (𝓝 (1 : ℂ)) := by
  have h := (tendsto_logSeriesBottcherApprox_div_atInfinity c).inv₀ (one_ne_zero)
  simpa using h

/-- The reciprocal Böttcher coordinate tends to `0` at `0`. -/
lemma tendsto_recipBottcher_nhdsNE_zero (c : ℂ) :
    Tendsto (fun w => (logSeriesBottcherApprox c w⁻¹)⁻¹) (𝓝[≠] 0) (𝓝 0) := by
  have hw0 : Tendsto (fun w : ℂ => w) (𝓝[≠] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hratio : Tendsto (fun w : ℂ => (logSeriesBottcherApprox c w⁻¹ / w⁻¹)⁻¹)
      (𝓝[≠] 0) (𝓝 1) :=
    (tendsto_div_logSeriesBottcherApprox_atInfinity c).comp tendsto_inv_nhdsNE_atInfinity
  have hmul := hw0.mul hratio
  rw [mul_one] at hmul
  refine hmul.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with w hw
  have hwne : w ≠ 0 := hw
  rw [inv_div, mul_div_assoc', mul_inv_cancel₀ hwne, one_div]

/-- Boundedness of the reciprocal coordinate on the punctured ball. -/
lemma recipBottcher_bddAbove (c : ℂ) :
    BddAbove ((norm ∘ (fun w => (logSeriesBottcherApprox c w⁻¹)⁻¹)) ''
      (ball (0 : ℂ) (‖c‖ + 2)⁻¹ \ {0})) := by
  refine ⟨1, ?_⟩
  rintro y ⟨w, hw, rfl⟩
  have hgt : ‖c‖ + 2 < ‖w⁻¹‖ := norm_inv_gt_of_mem_punctured c hw
  have h1 : 1 < ‖logSeriesBottcherApprox c w⁻¹‖ :=
    one_lt_norm_logSeriesBottcherApprox_of_outside_open c (by linarith)
  simp only [Function.comp_apply, norm_inv]
  rw [inv_le_one_iff₀]
  right; linarith



/-- The reciprocal Böttcher coordinate, extended by `0` at `0`. -/
noncomputable def recipBottcher (c : ℂ) : ℂ → ℂ :=
  Function.update (fun w => (logSeriesBottcherApprox c w⁻¹)⁻¹) 0 0

lemma recipBottcher_zero (c : ℂ) : recipBottcher c 0 = 0 := Function.update_self _ _ _

lemma recipBottcher_analyticAt_zero (c : ℂ) : AnalyticAt ℂ (recipBottcher c) 0 := by
  set δ : ℝ := (‖c‖ + 2)⁻¹ with hδdef
  have hδ : 0 < δ := by rw [hδdef]; positivity
  have hlim : limUnder (𝓝[≠] (0:ℂ)) (fun w => (logSeriesBottcherApprox c w⁻¹)⁻¹) = 0 :=
    (tendsto_recipBottcher_nhdsNE_zero c).limUnder_eq
  have hdiff := differentiableOn_update_limUnder_of_bddAbove
    (f := fun w => (logSeriesBottcherApprox c w⁻¹)⁻¹) (s := ball (0:ℂ) δ) (c := 0)
    (ball_mem_nhds _ hδ) (recipBottcher_differentiableOn_punctured c)
    (recipBottcher_bddAbove c)
  rw [hlim] at hdiff
  have hana : AnalyticOnNhd ℂ (recipBottcher c) (ball (0:ℂ) δ) :=
    hdiff.analyticOnNhd isOpen_ball
  exact hana 0 (mem_ball_self hδ)

lemma recipBottcher_deriv_zero (c : ℂ) : deriv (recipBottcher c) 0 = 1 := by
  have hda : DifferentiableAt ℂ (recipBottcher c) 0 :=
    (recipBottcher_analyticAt_zero c).differentiableAt
  have hd : HasDerivAt (recipBottcher c) (deriv (recipBottcher c) 0) 0 := hda.hasDerivAt
  have hslope := hasDerivAt_iff_tendsto_slope.1 hd
  have hratio : Tendsto (fun w : ℂ => (logSeriesBottcherApprox c w⁻¹ / w⁻¹)⁻¹)
      (𝓝[≠] 0) (𝓝 1) :=
    (tendsto_div_logSeriesBottcherApprox_atInfinity c).comp tendsto_inv_nhdsNE_atInfinity
  have hslope1 : Tendsto (slope (recipBottcher c) 0) (𝓝[≠] 0) (𝓝 1) := by
    refine hratio.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with w hw
    have hwne : w ≠ 0 := hw
    rw [slope_def_field, recipBottcher, Function.update_of_ne hwne, Function.update_self,
      sub_zero, sub_zero, inv_div]
    ring
  exact tendsto_nhds_unique hslope hslope1



/-- **Analytic local inverse of the near-infinity Böttcher coordinate**
    (in reciprocal coordinates at `0`). The near-infinity Böttcher coordinate
    `φ_c` is injective near `∞` and admits an analytic inverse. -/
theorem recipBottcher_exists_analytic_inverse (c : ℂ) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧ g 0 = 0 ∧
      (∀ᶠ w in 𝓝 (0:ℂ), g (recipBottcher c w) = w) ∧
      (∀ᶠ v in 𝓝 (0:ℂ), recipBottcher c (g v) = v) := by
  have hne : deriv (recipBottcher c) 0 ≠ 0 := by
    rw [recipBottcher_deriv_zero]; exact one_ne_zero
  have hana := recipBottcher_analyticAt_zero c
  refine ⟨hana.hasStrictDerivAt.localInverse _ _ _ hne, ?_, ?_, ?_, ?_⟩
  · have h := hana.analyticAt_localInverse hne
    rwa [recipBottcher_zero] at h
  · have hL := (hana.hasStrictDerivAt.eventually_left_inverse hne).self_of_nhds
    rwa [recipBottcher_zero] at hL
  · exact hana.hasStrictDerivAt.eventually_left_inverse hne
  · have hR := hana.hasStrictDerivAt.eventually_right_inverse hne
    rwa [recipBottcher_zero] at hR

/-- **The `z`-derivative of the near-infinity Böttcher coordinate is nonzero.**
For `‖z‖` large the fiber map `φ_c = logSeriesBottcherApprox c` has
`deriv (φ_c) z ≠ 0`. This is the invertibility ingredient (the `(2,2)` entry of the
block-triangular joint Fréchet derivative) needed to run the `ℂ²` inverse function
theorem. Proof: `recipBottcher c` has derivative `1` at `0`, hence is injective on a
neighborhood of `0`; transporting through the inversions `z ↦ z⁻¹` shows `φ_c` is
injective on the exterior `{R < ‖z‖}`, and an injective holomorphic map has nonzero
derivative (`deriv_ne_zero_of_injOn_nhds`). -/
lemma logSeriesBottcherApprox_deriv_ne_zero_exterior (c : ℂ) :
    ∃ R : ℝ, ‖c‖ + 2 ≤ R ∧
      ∀ z : ℂ, R < ‖z‖ → deriv (logSeriesBottcherApprox c) z ≠ 0 := by
  -- recipBottcher c is injective on a neighborhood of 0 (deriv there is 1 ≠ 0)
  have hstrict : HasStrictDerivAt (recipBottcher c) 1 0 := by
    have := (recipBottcher_analyticAt_zero c).hasStrictDerivAt
    rwa [recipBottcher_deriv_zero c] at this
  obtain ⟨s, hs, hinj⟩ := injOn_nhds_of_hasStrictDerivAt hstrict one_ne_zero
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hs
  -- choose R large: R ≥ ‖c‖+2 and R > 1/δ  (so 1/‖z‖ < δ)
  obtain ⟨R, hR1, hR2⟩ : ∃ R : ℝ, ‖c‖ + 2 ≤ R ∧ 1 / δ < R := by
    refine ⟨max (‖c‖ + 2) (1 / δ + 1), le_max_left _ _, ?_⟩
    exact lt_of_lt_of_le (by linarith) (le_max_right _ _)
  refine ⟨R, hR1, ?_⟩
  have hinvsmall : ∀ z : ℂ, R < ‖z‖ → z⁻¹ ∈ ball (0:ℂ) δ := by
    intro z hz
    have hzne : z ≠ 0 := by
      intro h; rw [h, norm_zero] at hz; nlinarith [norm_nonneg c]
    rw [mem_ball, dist_zero_right, norm_inv]
    have : (1:ℝ) / ‖z‖ < δ := by
      rw [div_lt_iff₀ (by positivity)]
      have : 1 / δ < ‖z‖ := lt_trans hR2 hz
      rw [div_lt_iff₀ hδ] at this; nlinarith [this]
    simpa [one_div] using this
  have hinjphi : Set.InjOn (logSeriesBottcherApprox c) {z : ℂ | R < ‖z‖} := by
    intro z₁ hz₁ z₂ hz₂ hEq
    simp only [Set.mem_setOf_eq] at hz₁ hz₂
    have hz₁ne : z₁ ≠ 0 := by intro h; rw [h, norm_zero] at hz₁; nlinarith [norm_nonneg c]
    have hz₂ne : z₂ ≠ 0 := by intro h; rw [h, norm_zero] at hz₂; nlinarith [norm_nonneg c]
    have hw₁ : z₁⁻¹ ≠ 0 := inv_ne_zero hz₁ne
    have hw₂ : z₂⁻¹ ≠ 0 := inv_ne_zero hz₂ne
    -- recipBottcher c z⁻¹ = (φ_c z)⁻¹
    have hrec : ∀ z : ℂ, z ≠ 0 → recipBottcher c z⁻¹ = (logSeriesBottcherApprox c z)⁻¹ := by
      intro z hzne
      rw [recipBottcher, Function.update_of_ne (inv_ne_zero hzne), inv_inv]
    have heqrec : recipBottcher c z₁⁻¹ = recipBottcher c z₂⁻¹ := by
      rw [hrec z₁ hz₁ne, hrec z₂ hz₂ne, hEq]
    have hmem₁ : z₁⁻¹ ∈ s := hball (hinvsmall z₁ hz₁)
    have hmem₂ : z₂⁻¹ ∈ s := hball (hinvsmall z₂ hz₂)
    have : z₁⁻¹ = z₂⁻¹ := hinj hmem₁ hmem₂ heqrec
    exact inv_injective this
  -- deriv ≠ 0 from injectivity on the open neighborhood
  intro z hz hzero
  have hopen : IsOpen {z : ℂ | R < ‖z‖} := isOpen_lt continuous_const continuous_norm
  have hznhds : {z : ℂ | R < ‖z‖} ∈ 𝓝 z := hopen.mem_nhds hz
  have hana : AnalyticAt ℂ (logSeriesBottcherApprox c) z :=
    (logSeriesBottcherApprox_differentiableOn_large_radius c hR1).analyticAt hznhds
  exact deriv_ne_zero_of_injOn_nhds hana _ hznhds hinjphi hzero

end MLC
