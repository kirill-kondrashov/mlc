import Mlc.Research.NestModulus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# A nest with moduli bounded below: the concentric disks

The moduli of the annuli of a nest of `Mlc/Research/NestModulus.lean` are the extremal widths of
the families `D.loops j` of `C¹` loops around the next piece. This module checks that the
definition is not empty: the nest of the concentric disks `B(0, 2⁻ʲ)` has annuli of modulus at
least `log (3/2) / 2π`, so its moduli add up to infinity (`concentricNest_divergentModuli`) and
the nest realizes every budget.

The circle of radius `s` is the loop `t ↦ s e^{i (2π t - π)}`; its length measure is the
`circleCurve s` of `Mlc/Research/AnnulusModulus.lean`, so the family of the circles of the
annulus lies in the family of its loops, and the extremal length of the circles
(`extLength_circleFamily`) bounds that of the loops from above.
-/

namespace MLC.Research

open MeasureTheory ENNReal Set Real Topology Metric

noncomputable section

/-! ### The circle as a loop -/

/-- The circle of radius `s` around `0`, run once on `(0, 1]` from the angle `-π`. -/
def circleLoop (s : ℝ) (t : ℝ) : ℂ := pol (s, 2 * π * t - π)

lemma circleLoop_eq (s t : ℝ) :
    circleLoop s t = (s : ℂ) * Complex.exp (((2 * π * t - π : ℝ) : ℂ) * Complex.I) := by
  unfold circleLoop pol
  rw [Complex.exp_mul_I]
  push_cast
  ring

lemma hasDerivAt_circleLoop (s t : ℝ) :
    HasDerivAt (circleLoop s)
      ((s : ℂ) * (Complex.exp (((2 * π * t - π : ℝ) : ℂ) * Complex.I) *
        (((2 * π : ℝ) : ℂ) * Complex.I))) t := by
  have h1 : HasDerivAt (fun t : ℝ => 2 * π * t - π) (2 * π) t :=
    (((hasDerivAt_id t).const_mul (2 * π)).sub_const π).congr_deriv (by simp)
  have h2 := ((h1.ofReal_comp.mul_const Complex.I).cexp).const_mul (s : ℂ)
  have h3 : circleLoop s = fun t : ℝ => (s : ℂ) *
      Complex.exp (((2 * π * t - π : ℝ) : ℂ) * Complex.I) := funext (circleLoop_eq s)
  rw [h3]
  exact h2

lemma norm_deriv_circleLoop {s : ℝ} (hs : 0 < s) (t : ℝ) :
    ‖deriv (circleLoop s) t‖ = 2 * π * s := by
  rw [(hasDerivAt_circleLoop s t).deriv, norm_mul, norm_mul, norm_mul, Complex.norm_real,
    Complex.norm_exp_ofReal_mul_I, Complex.norm_real, Complex.norm_I,
    Real.norm_of_nonneg hs.le, Real.norm_of_nonneg (by positivity)]
  ring

lemma isLoop_circleLoop (s : ℝ) : IsLoop (circleLoop s) := by
  refine ⟨?_, fun t => ?_⟩
  · have hl : ContDiff ℝ 1 fun t : ℝ => 2 * π * t - π :=
      (contDiff_const.mul contDiff_id).sub contDiff_const
    have hg : ContDiff ℝ 1 fun t : ℝ => ((2 * π * t - π : ℝ) : ℂ) :=
      Complex.ofRealCLM.contDiff.comp hl
    have h3 : circleLoop s = fun t : ℝ => (s : ℂ) *
        Complex.exp (((2 * π * t - π : ℝ) : ℂ) * Complex.I) := funext (circleLoop_eq s)
    rw [h3]
    exact contDiff_const.mul ((hg.mul contDiff_const).cexp)
  · rw [circleLoop_eq, circleLoop_eq]
    have : ((2 * π * (t + 1) - π : ℝ) : ℂ) * Complex.I =
        ((2 * π * t - π : ℝ) : ℂ) * Complex.I + 2 * π * Complex.I := by
      push_cast
      ring
    rw [this, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

/-- The length measure of the loop `circleLoop s` is the arc length of the circle of radius `s`. -/
lemma loopMeasure_circleLoop {s : ℝ} (hs : 0 < s) :
    loopMeasure (circleLoop s) = circleCurve s := by
  have hd : (fun t => ENNReal.ofReal ‖deriv (circleLoop s) t‖) =
      fun _ => ENNReal.ofReal (2 * π * s) := by
    funext t
    rw [norm_deriv_circleLoop hs t]
  have hmeas : Measurable fun t : ℝ => 2 * π * t - π :=
    (measurable_const.mul measurable_id).sub measurable_const
  have hpre : (fun t : ℝ => 2 * π * t - π) ⁻¹' Ioc (-π) π = Ioc 0 1 := by
    ext t
    simp only [mem_preimage, mem_Ioc]
    constructor <;> intro h <;> constructor <;> nlinarith [Real.pi_pos, h.1, h.2]
  have hvol : volume.map (fun t : ℝ => 2 * π * t - π) =
      ENNReal.ofReal (2 * π)⁻¹ • volume := by
    have h : (fun t : ℝ => 2 * π * t - π) = (fun θ : ℝ => θ - π) ∘ (fun t : ℝ => 2 * π * t) :=
      rfl
    have hm1 : Measurable fun θ : ℝ => θ - π := measurable_id.sub_const π
    have hm2 : Measurable fun t : ℝ => 2 * π * t := measurable_const.mul measurable_id
    rw [h, ← Measure.map_map hm1 hm2, Real.map_volume_mul_left (by positivity),
      Measure.map_smul, map_sub_right_eq_self, abs_of_pos (by positivity)]
  have hmap : (volume.restrict (Ioc (0 : ℝ) 1)).map (fun t : ℝ => 2 * π * t - π) =
      ENNReal.ofReal (2 * π)⁻¹ • volume.restrict (Ioo (-π) π) := by
    rw [← hpre, ← Measure.restrict_map hmeas measurableSet_Ioc, hvol, Measure.restrict_smul,
      Measure.restrict_congr_set Ioo_ae_eq_Ioc.symm]
  unfold loopMeasure circleCurve
  rw [hd, withDensity_const, Measure.map_smul]
  have hcomp : circleLoop s = (fun θ : ℝ => pol (s, θ)) ∘ (fun t : ℝ => 2 * π * t - π) := rfl
  rw [hcomp, ← Measure.map_map (measurable_pol_right s) hmeas, hmap, Measure.map_smul, smul_smul]
  congr 1
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp

/-! ### The rays meet the circle -/

/-- A ray that starts inside the circle of radius `s` around `0` meets the circle. -/
lemma exists_circleLoop_eq {s : ℝ} {z u : ℂ} (hz : ‖z‖ < s) (hu : ‖u‖ = 1) :
    ∃ t : ℝ, ∃ σ : ℝ, 0 < σ ∧ circleLoop s t = z + (σ : ℂ) * u := by
  have hs0 : 0 < s := lt_of_le_of_lt (norm_nonneg z) hz
  set a : ℝ := inner ℝ z u with ha
  have hD : 0 < a ^ 2 + (s ^ 2 - ‖z‖ ^ 2) := by
    nlinarith [sq_nonneg a, norm_nonneg z]
  have hsqrt : Real.sqrt (a ^ 2 + (s ^ 2 - ‖z‖ ^ 2)) ^ 2 = a ^ 2 + (s ^ 2 - ‖z‖ ^ 2) :=
    Real.sq_sqrt hD.le
  have habs : |a| < Real.sqrt (a ^ 2 + (s ^ 2 - ‖z‖ ^ 2)) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_lt_sqrt (sq_nonneg a) (by nlinarith [norm_nonneg z])
  set σ : ℝ := -a + Real.sqrt (a ^ 2 + (s ^ 2 - ‖z‖ ^ 2)) with hσdef
  have hσ : 0 < σ := by linarith [le_abs_self a]
  have hw : ‖z + (σ : ℂ) * u‖ = s := by
    have h2 : ‖z + (σ : ℂ) * u‖ ^ 2 = s ^ 2 := by
      rw [← Complex.real_smul, norm_add_sq_real, real_inner_smul_right, norm_smul, hu,
        Real.norm_of_nonneg hσ.le]
      rw [← ha]
      have : σ ^ 2 = -2 * a * σ + (s ^ 2 - ‖z‖ ^ 2) := by
        have h3 : (σ + a) ^ 2 = a ^ 2 + (s ^ 2 - ‖z‖ ^ 2) := by
          rw [hσdef]
          ring_nf
          rw [hsqrt]
        nlinarith [h3]
      nlinarith [this]
    exact (sq_eq_sq₀ (norm_nonneg _) hs0.le).1 h2
  refine ⟨(Complex.arg (z + (σ : ℂ) * u) + π) / (2 * π), σ, hσ, ?_⟩
  rw [circleLoop_eq]
  have hang : 2 * π * ((Complex.arg (z + (σ : ℂ) * u) + π) / (2 * π)) - π =
      Complex.arg (z + (σ : ℂ) * u) := by
    field_simp
    ring
  rw [hang]
  conv_rhs => rw [← Complex.norm_mul_exp_arg_mul_I (z + (σ : ℂ) * u), hw]

/-! ### The concentric nest -/

/-- The nest of the concentric disks `B(0, 2⁻ʲ)`. -/
def concentricNest : ConnectedNest Set.univ (0 : ℂ) where
  piece j := ball 0 ((1 / 2 : ℝ) ^ j)
  open_piece _ := isOpen_ball
  contains _ := mem_ball_self (by positivity)
  connected _ := by
    rw [inter_univ]
    exact (convex_ball _ _).isConnected ⟨0, mem_ball_self (by positivity)⟩
  compact_closure j := by
    rw [closure_ball _ (by positivity)]
    exact isCompact_closedBall _ _
  nested j := ball_subset_ball (by
    have : 0 < (1 / 2 : ℝ) ^ j := by positivity
    rw [pow_succ]
    linarith)

/-- Each circle of the annulus `2⁻⁽ʲ⁺¹⁾ < |z| < 2⁻ʲ` is a loop of the annulus of the nest that
goes around the next piece. -/
lemma circleCurve_mem_loops {j : ℕ} {s : ℝ}
    (hs : s ∈ Ioo ((1 / 2 : ℝ) ^ (j + 1)) ((1 / 2 : ℝ) ^ j)) :
    circleCurve s ∈ concentricNest.loops j := by
  have hr : 0 < (1 / 2 : ℝ) ^ (j + 1) := by positivity
  have hs0 : 0 < s := hr.trans hs.1
  refine ⟨circleLoop s, isLoop_circleLoop s, fun t => ?_, fun z hz u hu => ?_,
    (loopMeasure_circleLoop hs0).symm⟩
  · have hn : ‖circleLoop s t‖ = s := norm_pol hs0.le _
    refine ⟨?_, ?_⟩
    · show circleLoop s t ∈ ball (0 : ℂ) ((1 / 2 : ℝ) ^ j)
      rw [mem_ball_zero_iff, hn]
      exact hs.2
    · show circleLoop s t ∉ closure (ball (0 : ℂ) ((1 / 2 : ℝ) ^ (j + 1)))
      rw [closure_ball _ hr.ne', mem_closedBall_zero_iff, hn, not_le]
      exact hs.1
  · have hz' : z ∈ closure (ball (0 : ℂ) ((1 / 2 : ℝ) ^ (j + 1))) := hz
    rw [closure_ball _ hr.ne', mem_closedBall_zero_iff] at hz'
    exact exists_circleLoop_eq (lt_of_le_of_lt hz' hs.1) hu

/-- The annuli of the concentric nest have extremal width at least `log (3/2) / 2π`. -/
lemma ofReal_le_extWidth_concentric_loops (j : ℕ) :
    ENNReal.ofReal (Real.log (3 / 2) / (2 * π)) ≤ extWidth volume (concentricNest.loops j) := by
  have hr : 0 < (1 / 2 : ℝ) ^ (j + 1) := by positivity
  have hpow : (1 / 2 : ℝ) ^ j = 2 * (1 / 2 : ℝ) ^ (j + 1) := by
    rw [pow_succ]
    ring
  have hrR : (1 / 2 : ℝ) ^ (j + 1) < 3 / 2 * (1 / 2 : ℝ) ^ (j + 1) := by linarith
  have hsub : circleFamily ((1 / 2 : ℝ) ^ (j + 1)) (3 / 2 * (1 / 2 : ℝ) ^ (j + 1)) ⊆
      concentricNest.loops j := by
    rintro _ ⟨s, hs, rfl⟩
    exact circleCurve_mem_loops ⟨hs.1, by linarith [hs.2]⟩
  have h1 := extLength_mono (m := volume) (Γ := circleFamily ((1 / 2 : ℝ) ^ (j + 1))
    (3 / 2 * (1 / 2 : ℝ) ^ (j + 1))) (Γ' := concentricNest.loops j)
    fun μ hμ => ⟨μ, hsub hμ, le_rfl⟩
  have hlog : 0 < Real.log (3 / 2) := Real.log_pos (by norm_num)
  have hratio : 3 / 2 * (1 / 2 : ℝ) ^ (j + 1) / (1 / 2 : ℝ) ^ (j + 1) = 3 / 2 := by
    field_simp
  unfold extWidth
  calc ENNReal.ofReal (Real.log (3 / 2) / (2 * π))
      = (ENNReal.ofReal (2 * π / Real.log (3 / 2)))⁻¹ := by
        rw [← ENNReal.ofReal_inv_of_pos (by positivity), inv_div]
    _ = (extLength volume (circleFamily ((1 / 2 : ℝ) ^ (j + 1))
          (3 / 2 * (1 / 2 : ℝ) ^ (j + 1))))⁻¹ := by
        rw [extLength_circleFamily hr hrR, hratio]
    _ ≤ (extLength volume (concentricNest.loops j))⁻¹ := ENNReal.inv_le_inv.2 h1

/-- **The moduli of the annuli of the concentric nest add up to infinity.** The definition of the
moduli of a nest is not empty. -/
theorem concentricNest_divergentModuli : concentricNest.DivergentModuli :=
  concentricNest.divergentModuli_of_uniform
    (ENNReal.ofReal_pos.2 (div_pos (Real.log_pos (by norm_num)) (by positivity))).ne'
    ofReal_le_extWidth_concentric_loops

/-- Every budget is realized by the concentric nest around `0`. -/
theorem nonempty_parameterRealization_concentric (b : ReturnBudget) :
    Nonempty (ParameterRealization Set.univ (0 : ℂ) b) :=
  concentricNest.nonempty_parameterRealization concentricNest_divergentModuli b

end

end MLC.Research
