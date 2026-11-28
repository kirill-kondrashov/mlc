import Mlc.Research.NestModulus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Nests with moduli bounded below

The moduli of the annuli of a nest of `Mlc/Research/NestModulus.lean` are the extremal widths of
the families `D.loops j` of `C¹` loops around the next piece. This module shows that nests with
moduli bounded below exist, in two ways.

* The nest of the concentric disks `B(0, 2⁻ʲ)` has annuli of modulus at least `log (3/2) / 2π`,
  so its moduli add up to infinity (`concentricNest_divergentModuli`) and it realizes every
  budget. So the definition of the moduli of a nest is satisfiable.
* **Every shrinking nest has a subnest whose moduli add up to infinity**
  (`ConnectedNest.exists_divergentSubnest`): if the pieces shrink to `c`, each piece contains a
  disk around `c` and a later piece lies in the half of that disk, so the annulus between the two
  contains a round annulus of modulus at least `log (3/2) / 2π`. Together with
  `Mlc/Research/PhaseParameter.lean` this makes the moduli form of Lemma T equivalent to the lemma
  itself.

The circle of radius `s` is the loop `t ↦ s e^{i (2π t - π)}`; its length measure is the
`circleCurve s` of `Mlc/Research/AnnulusModulus.lean`, so the family of the circles of an annulus
lies in the family of its loops, and the extremal length of the circles (`extLength_circleFamily`)
bounds that of the loops from above (`extWidth_loopFamily_ge`).
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

/-! ### The circle is run through every point of itself -/

/-- Every point of the circle of radius `s` around `0` lies on the loop `circleLoop s`. -/
lemma exists_circleLoop_of_norm {s : ℝ} {w : ℂ} (hw : ‖w‖ = s) :
    ∃ t : ℝ, circleLoop s t = w := by
  refine ⟨(Complex.arg w + π) / (2 * π), ?_⟩
  rw [circleLoop_eq]
  have hang : 2 * π * ((Complex.arg w + π) / (2 * π)) - π = Complex.arg w := by
    field_simp
    ring
  rw [hang]
  conv_rhs => rw [← Complex.norm_mul_exp_arg_mul_I w, hw]

/-- The circle of radius `s` around `c` separates the points at distance at most `s` from `c`
from the points at distance at least `s`. -/
lemma separates_circle {c : ℂ} {s : ℝ} {K O : Set ℂ} (hK : ∀ z ∈ K, ‖z - c‖ ≤ s)
    (hO : ∀ w, w ∉ O → s ≤ ‖w - c‖) : Separates (fun t => c + circleLoop s t) K O := by
  intro z hz w hw a b p hab hp hpa hpb
  have hf : ContinuousOn (fun τ => ‖p τ - c‖) (Icc a b) := (hp.sub continuousOn_const).norm
  have h1 : ‖p a - c‖ ≤ s := by rw [hpa]; exact hK z hz
  have h2 : s ≤ ‖p b - c‖ := by rw [hpb]; exact hO w hw
  obtain ⟨τ, hτ, hτs⟩ := intermediate_value_Icc hab hf ⟨h1, h2⟩
  obtain ⟨t, ht⟩ := exists_circleLoop_of_norm (s := s) (w := p τ - c) hτs
  exact ⟨τ, hτ, t, show p τ = c + circleLoop s t by rw [ht]; ring⟩

/-! ### The circles around a point bound the modulus from below -/

/-- Translating a loop translates its length measure. -/
lemma loopMeasure_const_add {γ : ℝ → ℂ} (hγ : IsLoop γ) (c : ℂ) :
    loopMeasure (fun t => c + γ t) = (loopMeasure γ).map (fun z => c + z) := by
  have hd : deriv (fun t => c + γ t) = deriv γ := funext fun t => deriv_const_add c
  unfold loopMeasure
  rw [hd, Measure.map_map (measurable_const_add c) hγ.continuous.measurable]
  rfl

/-- **The circles of an annulus bound its modulus from below.** If the circles `|z - c| = s`,
`r < s ≤ R`, lie in `A`, the set `K` lies in the closed disk of radius `r` around `c` and the
complement of `O` lies outside the open disk of radius `R`, the loops in `A` that separate `K`
from the complement of `O` have extremal width at least `log (R/r) / 2π`. -/
lemma extWidth_loopFamily_ge_radii {A K O : Set ℂ} {c : ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hK : ∀ z ∈ K, ‖z - c‖ ≤ r) (hO : ∀ w, w ∉ O → R ≤ ‖w - c‖)
    (hA : ∀ s ∈ Ioc r R, ∀ t, c + circleLoop s t ∈ A) :
    ENNReal.ofReal (Real.log (R / r) / (2 * π)) ≤ extWidth volume (loopFamily A K O) := by
  set Γ := circleFamily r R with hΓ
  set Γ' : Set (Measure ℂ) := (fun μ : Measure ℂ => μ.map (fun z => c + z)) '' Γ with hΓ'
  have hsub : Γ' ⊆ loopFamily A K O := by
    rintro _ ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    have hs0 : 0 < s := hr.trans hs.1
    have hloop := isLoop_circleLoop s
    refine ⟨fun t => c + circleLoop s t, ⟨contDiff_const.add hloop.1, fun t => ?_⟩, hA s hs,
      separates_circle (fun z hz => (hK z hz).trans hs.1.le)
        (fun w hw => hs.2.trans (hO w hw)), ?_⟩
    · show c + circleLoop s (t + 1) = c + circleLoop s t
      rw [hloop.2 t]
    · rw [loopMeasure_const_add hloop c, loopMeasure_circleLoop hs0]
  have h1 : extWidth volume Γ ≤ extWidth volume Γ' := by
    have h := extWidth_pullback_le (mX := volume) (mY := volume) (ΓX := Γ) (ΓY := Γ')
      (φ := fun z => c + z) (J := fun _ => 1) (d := 1) (measurable_const_add c)
      measurable_const one_ne_zero ENNReal.one_ne_top
      (by
        simp only [one_pow, withDensity_const, one_smul]
        exact (map_add_left_eq_self volume c).le)
      (fun μ hμ => by
        rw [withDensity_const, one_smul]
        exact ⟨μ, hμ, rfl⟩)
    rwa [one_mul] at h
  have h2 : extWidth volume Γ' ≤ extWidth volume (loopFamily A K O) := extWidth_mono hsub
  have hlog : 0 < Real.log (R / r) := Real.log_pos ((one_lt_div hr).2 hrR)
  have h0 : ENNReal.ofReal (Real.log (R / r) / (2 * π)) = extWidth volume Γ := by
    unfold extWidth
    rw [hΓ, extLength_circleFamily hr hrR,
      ← ENNReal.ofReal_inv_of_pos (div_pos (by positivity) hlog), inv_div]
  exact h0.le.trans (h1.trans h2)

/-- The circles of the ratio `3/2` bound the modulus from below by `log (3/2) / 2π`. -/
lemma extWidth_loopFamily_ge {A K O : Set ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hK : ∀ z ∈ K, ‖z - c‖ ≤ r) (hO : ∀ w, w ∉ O → 3 / 2 * r ≤ ‖w - c‖)
    (hA : ∀ s ∈ Ioc r (3 / 2 * r), ∀ t, c + circleLoop s t ∈ A) :
    ENNReal.ofReal (Real.log (3 / 2) / (2 * π)) ≤ extWidth volume (loopFamily A K O) := by
  have h := extWidth_loopFamily_ge_radii (R := 3 / 2 * r) hr (by linarith) hK hO hA
  rwa [show 3 / 2 * r / r = 3 / 2 by field_simp] at h

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

/-- The annuli of the concentric nest have extremal width at least `log (3/2) / 2π`. -/
lemma ofReal_le_extWidth_concentric_loops (j : ℕ) :
    ENNReal.ofReal (Real.log (3 / 2) / (2 * π)) ≤ extWidth volume (concentricNest.loops j) := by
  have hr : 0 < (1 / 2 : ℝ) ^ (j + 1) := by positivity
  have hpow : (1 / 2 : ℝ) ^ j = 2 * (1 / 2 : ℝ) ^ (j + 1) := by
    rw [pow_succ]
    ring
  refine extWidth_loopFamily_ge (c := 0) hr (fun z hz => ?_) (fun w hw => ?_)
    (fun s hs t => ?_)
  · have hz' : z ∈ closure (ball (0 : ℂ) ((1 / 2 : ℝ) ^ (j + 1))) := hz
    rw [closure_ball _ hr.ne', mem_closedBall_zero_iff] at hz'
    simpa using hz'
  · have hw' : w ∉ ball (0 : ℂ) ((1 / 2 : ℝ) ^ j) := hw
    rw [mem_ball_zero_iff, not_lt] at hw'
    rw [sub_zero]
    linarith
  · have hn : ‖circleLoop s t‖ = s := norm_pol (hr.trans hs.1).le _
    refine ⟨?_, ?_⟩
    · show 0 + circleLoop s t ∈ ball (0 : ℂ) ((1 / 2 : ℝ) ^ j)
      rw [zero_add, mem_ball_zero_iff, hn]
      linarith [hs.2]
    · show 0 + circleLoop s t ∉ closure (ball (0 : ℂ) ((1 / 2 : ℝ) ^ (j + 1)))
      rw [zero_add, closure_ball _ hr.ne', mem_closedBall_zero_iff, hn, not_le]
      exact hs.1

/-- **The moduli of the annuli of the concentric nest add up to infinity.** The definition of the
moduli of a nest is satisfiable. -/
theorem concentricNest_divergentModuli : concentricNest.DivergentModuli :=
  concentricNest.divergentModuli_of_uniform
    (ENNReal.ofReal_pos.2 (div_pos (Real.log_pos (by norm_num)) (by positivity))).ne'
    ofReal_le_extWidth_concentric_loops

/-- Every budget is realized by the concentric nest around `0`. -/
theorem nonempty_parameterRealization_concentric (b : ReturnBudget) :
    Nonempty (ParameterRealization Set.univ (0 : ℂ) b) :=
  concentricNest.nonempty_parameterRealization concentricNest_divergentModuli b

/-! ### A subnest with divergent moduli -/

/-- **Every shrinking nest has a subnest whose moduli add up to infinity.** If the pieces shrink
to `c`, each piece `Pₙ` contains a disk `B(c, ρₙ)` and a later piece `P_m` has its closure in
`B(c, ρₙ/2)`; the annulus between them contains the circles `ρₙ/2 < |z - c| ≤ 3ρₙ/4`, which go
around `cl P_m` and have extremal width at least `log (3/2) / 2π`. -/
theorem ConnectedNest.exists_divergentSubnest {S : Set ℂ} {c : ℂ} (D : ConnectedNest S c)
    (hshr : ∀ ε : ℝ, 0 < ε → ∃ n, closure (D.piece n) ⊆ ball c ε) :
    ∃ D' : ConnectedNest S c, D'.DivergentModuli := by
  have hρ : ∀ n, ∃ ρ : ℝ, 0 < ρ ∧ ball c ρ ⊆ D.piece n := fun n => by
    obtain ⟨ρ, hρ, hb⟩ := Metric.isOpen_iff.1 (D.open_piece n) c (D.contains n)
    exact ⟨ρ, hρ, hb⟩
  choose ρ hρpos hρsub using hρ
  have hN : ∀ n, ∃ m, closure (D.piece m) ⊆ ball c (ρ n / 2) := fun n =>
    hshr _ (half_pos (hρpos n))
  choose N hN using hN
  have hnest : ∀ k, D.piece (N^[k + 1] 0) ⊆ D.piece (N^[k] 0) := fun k => by
    rw [Function.iterate_succ_apply']
    exact subset_closure.trans ((hN _).trans
      ((ball_subset_ball (by linarith [hρpos (N^[k] 0)])).trans (hρsub _)))
  let D' : ConnectedNest S c :=
    { piece := fun k => D.piece (N^[k] 0)
      open_piece := fun k => D.open_piece _
      contains := fun k => D.contains _
      connected := fun k => D.connected _
      compact_closure := fun k => D.compact_closure _
      nested := hnest }
  refine ⟨D', D'.divergentModuli_of_uniform (w := ENNReal.ofReal (Real.log (3 / 2) / (2 * π)))
    (ENNReal.ofReal_pos.2 (div_pos (Real.log_pos (by norm_num)) (by positivity))).ne'
    fun k => ?_⟩
  have hr : 0 < ρ (N^[k] 0) / 2 := half_pos (hρpos _)
  refine extWidth_loopFamily_ge (c := c) hr (fun z hz => ?_) (fun w hw => ?_)
    (fun s hs t => ?_)
  · have hz' : z ∈ closure (D.piece (N^[k + 1] 0)) := hz
    rw [Function.iterate_succ_apply'] at hz'
    exact (mem_ball_iff_norm.1 (hN _ hz')).le
  · have hw' : w ∉ ball c (ρ (N^[k] 0)) := fun h => hw (hρsub (N^[k] 0) h)
    rw [mem_ball_iff_norm, not_lt] at hw'
    linarith [hρpos (N^[k] 0)]
  · have hn : ‖circleLoop s t‖ = s := norm_pol (hr.trans hs.1).le _
    refine ⟨?_, ?_⟩
    · refine hρsub (N^[k] 0) ?_
      rw [mem_ball_iff_norm, add_sub_cancel_left, hn]
      linarith [hs.2, hρpos (N^[k] 0)]
    · intro hmem
      have hmem' : c + circleLoop s t ∈ closure (D.piece (N^[k + 1] 0)) := hmem
      rw [Function.iterate_succ_apply'] at hmem'
      have h := mem_ball_iff_norm.1 (hN _ hmem')
      rw [add_sub_cancel_left, hn] at h
      linarith [hs.1]

end

end MLC.Research
