import Mlc.Research.NestModulus
import Yoccoz.Quadratic.Complex.Basic
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.RingTheory.Complex

/-!
# Area multiplicity: the pullback law for the iterates of `f_c`

`Mlc/Research/ExtremalLength.lean` proves the pullback law `W(ΓX) ≤ d W(ΓY)` for a map `φ` that
carries the curves of `ΓX` to curves of `ΓY`, under the hypothesis that the area formula holds with
multiplicity at most `d`: the area `J² mX`, pushed forward by `φ`, is at most `d mY`. This module
proves the hypothesis for the quadratic polynomials.

* `AreaMultiplicity mX mY φ J d` is that hypothesis; it is additive over a measurable partition of
  the domain (`AreaMultiplicity.add_compl`) and multiplicative under composition
  (`AreaMultiplicity.comp`).
* An injective map that is differentiable on a measurable set has area multiplicity `1` there,
  with `J = |φ'|` (`areaMultiplicity_one_of_injOn`): the area formula of Mathlib and the
  determinant `|w|²` of the multiplication by `w`.
* `z ↦ z² + c` is injective on each of the two halves of the plane that the line `z ↦ -z` swaps,
  so `f_c` has area multiplicity `2` (`areaMultiplicity_fc`), and its `p`-th iterate `2ᵖ`
  (`areaMultiplicity_fc_iterate`), with `J = |(f_c^p)'|`.
* **`extWidth_le_pow_two_mul_fc_iterate`**: if `f_c^p` carries the curves of `ΓX` to curves of
  `ΓY`, the extremal width of `ΓX` is at most `2ᵖ` times that of `ΓY`. This is the estimate behind
  the Teichmüller contraction in the survey: `p` iterations of a quadratic map have area
  multiplicity at most `2ᵖ`, so the width of a pulled-back family grows by at most `2ᵖ`.
* `loopMeasure_comp`: the length measure of the image of a `C¹` loop under a holomorphic map is the
  pushforward of the length measure of the loop with the density `|φ'|`, which is the form of the
  hypothesis on the curves.
-/

namespace MLC.Research

open MeasureTheory ENNReal Set

noncomputable section

section General

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

/-- The map `φ` has area multiplicity at most `d` for the stretching `J`: the area `J² mX`, pushed
forward by `φ`, is at most `d` times `mY`. For a holomorphic map `J = |φ'|` and this is the area
formula with the number of preimages at most `d`; it is the hypothesis `harea` of
`extWidth_pullback_le`. -/
def AreaMultiplicity (mX : Measure α) (mY : Measure β) (φ : α → β) (J : α → ℝ≥0∞) (d : ℝ≥0∞) :
    Prop :=
  (mX.withDensity fun x => J x ^ 2).map φ ≤ d • mY

/-- Area multiplicity adds up over a measurable partition of the domain. -/
lemma AreaMultiplicity.add_compl {mX : Measure α} {mY : Measure β} {φ : α → β} {J : α → ℝ≥0∞}
    {d₁ d₂ : ℝ≥0∞} {E : Set α} (hE : MeasurableSet E) (hφ : Measurable φ)
    (h₁ : AreaMultiplicity (mX.restrict E) mY φ J d₁)
    (h₂ : AreaMultiplicity (mX.restrict Eᶜ) mY φ J d₂) :
    AreaMultiplicity mX mY φ J (d₁ + d₂) := by
  unfold AreaMultiplicity at *
  rw [← Measure.restrict_add_restrict_compl (μ := mX) hE, withDensity_add_measure,
    Measure.map_add _ _ hφ, add_smul]
  exact add_le_add h₁ h₂

/-- Area multiplicity multiplies under composition, with the stretching `J₂ ∘ φ₁ · J₁`. -/
lemma AreaMultiplicity.comp {mX : Measure α} {mY : Measure β} {mZ : Measure γ} {φ₁ : α → β}
    {φ₂ : β → γ} {J₁ : α → ℝ≥0∞} {J₂ : β → ℝ≥0∞} {d₁ d₂ : ℝ≥0∞} (hφ₁ : Measurable φ₁)
    (hφ₂ : Measurable φ₂) (hJ₁ : Measurable J₁) (hJ₂ : Measurable J₂)
    (h₁ : AreaMultiplicity mX mY φ₁ J₁ d₁) (h₂ : AreaMultiplicity mY mZ φ₂ J₂ d₂) :
    AreaMultiplicity mX mZ (φ₂ ∘ φ₁) (fun x => J₂ (φ₁ x) * J₁ x) (d₁ * d₂) := by
  refine Measure.le_iff.2 fun B hB => ?_
  have hS : MeasurableSet (φ₂ ⁻¹' B) := hφ₂ hB
  set G : β → ℝ≥0∞ := (φ₂ ⁻¹' B).indicator fun y => J₂ y ^ 2 with hG
  have hGm : Measurable G := (hJ₂.pow_const 2).indicator hS
  have hcomp : MeasurableSet ((φ₂ ∘ φ₁) ⁻¹' B) := (hφ₂.comp hφ₁) hB
  calc ((mX.withDensity fun x => (J₂ (φ₁ x) * J₁ x) ^ 2).map (φ₂ ∘ φ₁)) B
      = ∫⁻ x, G (φ₁ x) * J₁ x ^ 2 ∂mX := by
        rw [Measure.map_apply (hφ₂.comp hφ₁) hB, withDensity_apply _ hcomp,
          ← lintegral_indicator hcomp]
        refine lintegral_congr fun x => ?_
        by_cases hx : φ₂ (φ₁ x) ∈ B
        · simp [hG, Set.indicator, hx, mul_pow]
        · simp [hG, Set.indicator, hx]
    _ = ∫⁻ x, G (φ₁ x) ∂(mX.withDensity fun x => J₁ x ^ 2) := by
        refine Eq.trans ?_
          (lintegral_withDensity_eq_lintegral_mul mX (hJ₁.pow_const 2) (hGm.comp hφ₁)).symm
        exact lintegral_congr fun x => mul_comm _ _
    _ = ∫⁻ y, G y ∂((mX.withDensity fun x => J₁ x ^ 2).map φ₁) := (lintegral_map hGm hφ₁).symm
    _ ≤ ∫⁻ y, G y ∂(d₁ • mY) := lintegral_mono' h₁ le_rfl
    _ = d₁ * ∫⁻ y, G y ∂mY := by rw [lintegral_smul_measure]; rfl
    _ = d₁ * ((mY.withDensity fun y => J₂ y ^ 2).map φ₂) B := by
        congr 1
        rw [Measure.map_apply hφ₂ hB, withDensity_apply _ hS, ← lintegral_indicator hS]
    _ ≤ d₁ * (d₂ • mZ) B := mul_le_mul_right (Measure.le_iff'.1 h₂ B) d₁
    _ = ((d₁ * d₂) • mZ) B := by
        simp [Measure.smul_apply, mul_assoc]

end General

/-! ### The area formula for an injective holomorphic map -/

section Planar

/-- The multiplication by `w`, as a real-linear map of the plane. -/
def mulCLM (w : ℂ) : ℂ →L[ℝ] ℂ :=
  (ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) w).restrictScalars ℝ

/-- The determinant of the multiplication by `w` is `|w|²`. -/
lemma det_mulCLM (w : ℂ) : (mulCLM w).det = ‖w‖ ^ 2 := by
  have h : ((mulCLM w : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ) = LinearMap.mul ℝ ℂ w := by
    ext z
    simp [mulCLM, mul_comm]
  rw [ContinuousLinearMap.det, h]
  have h2 := Algebra.norm_apply ℝ w
  rw [Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq] at h2
  exact h2.symm

/-- An injective map that is differentiable on a measurable set has area multiplicity `1` there,
with the stretching `|φ'|`. -/
lemma areaMultiplicity_one_of_injOn {U : Set ℂ} (hU : MeasurableSet U) {φ φ' : ℂ → ℂ}
    (hφ : Measurable φ) (hd : ∀ z ∈ U, HasDerivWithinAt φ (φ' z) U z) (hinj : InjOn φ U) :
    AreaMultiplicity (volume.restrict U) volume φ (fun z => ENNReal.ofReal ‖φ' z‖) 1 := by
  refine Measure.le_iff.2 fun B hB => ?_
  rw [Measure.map_apply hφ hB, withDensity_apply _ (hφ hB), Measure.restrict_restrict (hφ hB)]
  have hs : MeasurableSet (φ ⁻¹' B ∩ U) := (hφ hB).inter hU
  have h := lintegral_abs_det_fderiv_eq_addHaar_image (volume : Measure ℂ) hs
    (f := φ) (f' := fun z => mulCLM (φ' z))
    (fun z hz => ((hd z hz.2).mono inter_subset_right).hasFDerivWithinAt.restrictScalars ℝ)
    (hinj.mono inter_subset_right)
  have h2 : ∫⁻ z in φ ⁻¹' B ∩ U, ENNReal.ofReal ‖φ' z‖ ^ 2 =
      ∫⁻ z in φ ⁻¹' B ∩ U, ENNReal.ofReal |(mulCLM (φ' z)).det| :=
    lintegral_congr fun z => by
      rw [det_mulCLM, abs_of_nonneg (by positivity), ENNReal.ofReal_pow (norm_nonneg _)]
  rw [h2, h]
  calc volume (φ '' (φ ⁻¹' B ∩ U)) ≤ volume B :=
        measure_mono (by rintro _ ⟨z, hz, rfl⟩; exact hz.1)
    _ = ((1 : ℝ≥0∞) • volume) B := by simp

end Planar

/-! ### The quadratic polynomials have area multiplicity `2` -/

section Quadratic

/-- A fundamental domain of `z ↦ z²`: the open right half plane and the upper half of the
imaginary axis. -/
def sqHalf : Set ℂ := {z | 0 < z.re ∨ (z.re = 0 ∧ 0 ≤ z.im)}

lemma measurableSet_sqHalf : MeasurableSet sqHalf :=
  (measurableSet_lt measurable_const Complex.measurable_re).union
    ((measurableSet_eq_fun Complex.measurable_re measurable_const).inter
      (measurableSet_le measurable_const Complex.measurable_im))

/-- Exactly one of `z` and `-z` lies in `sqHalf`, for `z ≠ 0`. -/
lemma mem_sqHalf_iff_neg_not_mem {z : ℂ} (hz : z ≠ 0) : z ∈ sqHalf ↔ -z ∉ sqHalf := by
  have him : z.re = 0 → z.im ≠ 0 := fun h h' => hz (Complex.ext h h')
  simp only [sqHalf, mem_setOf_eq, Complex.neg_re, Complex.neg_im]
  constructor
  · rintro (h | ⟨h1, h2⟩) (h' | ⟨h1', h2'⟩)
    · linarith
    · linarith
    · linarith
    · exact him h1 (le_antisymm (by linarith) h2)
  · intro h
    by_contra h'
    apply h
    push_neg at h'
    obtain ⟨h1, h2⟩ := h'
    rcases lt_or_eq_of_le h1 with hr | hr
    · exact Or.inl (by linarith)
    · exact Or.inr ⟨by linarith, by have := h2 hr; linarith⟩

/-- `z ↦ z² + c` is injective on every set that contains at most one of `z` and `-z`. -/
lemma injOn_fc_of_neg_not_mem {c : ℂ} {E : Set ℂ} (hE : ∀ z ∈ E, z ≠ 0 → -z ∉ E) :
    InjOn (MLC.Quadratic.fc c) E := by
  intro z hz w hw h
  have h2 : (z - w) * (z + w) = 0 := by
    have : z ^ 2 = w ^ 2 := by simpa [MLC.Quadratic.fc] using h
    linear_combination this
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact sub_eq_zero.1 h3
  · have hzw : w = -z := by linear_combination h3
    by_cases hz0 : z = 0
    · rw [hzw, hz0, neg_zero]
    · exact absurd (hzw ▸ hw) (hE z hz hz0)

/-- **The quadratic polynomial `f_c` has area multiplicity `2`**: `z ↦ z² + c` is injective on the
half plane `sqHalf` and on its complement. -/
lemma areaMultiplicity_fc (c : ℂ) :
    AreaMultiplicity volume volume (MLC.Quadratic.fc c) (fun z => ENNReal.ofReal ‖2 * z‖) 2 := by
  have hφ : Measurable (MLC.Quadratic.fc c) := by
    unfold MLC.Quadratic.fc
    fun_prop
  have hd : ∀ z, HasDerivAt (MLC.Quadratic.fc c) (2 * z) z := fun z =>
    ((hasDerivAt_pow 2 z).add_const c).congr_deriv (by simp)
  have h1 := areaMultiplicity_one_of_injOn measurableSet_sqHalf hφ (φ' := fun z => 2 * z)
    (fun z _ => (hd z).hasDerivWithinAt)
    (injOn_fc_of_neg_not_mem fun z hz hz0 => (mem_sqHalf_iff_neg_not_mem hz0).1 hz)
  have h2 := areaMultiplicity_one_of_injOn measurableSet_sqHalf.compl hφ (φ' := fun z => 2 * z)
    (fun z _ => (hd z).hasDerivWithinAt)
    (injOn_fc_of_neg_not_mem fun z hz hz0 hneg => hz
      ((mem_sqHalf_iff_neg_not_mem hz0).2 (by simpa using hneg)))
  have h := AreaMultiplicity.add_compl measurableSet_sqHalf hφ h1 h2
  rwa [one_add_one_eq_two] at h

end Quadratic

/-! ### The iterates of `f_c` -/

section Iterate

/-- The derivative of `f_c` is `2 z`. -/
lemma hasDerivAt_fc (c z : ℂ) : HasDerivAt (MLC.Quadratic.fc c) (2 * z) z :=
  ((hasDerivAt_pow 2 z).add_const c).congr_deriv (by simp)

lemma differentiable_fc (c : ℂ) : Differentiable ℂ (MLC.Quadratic.fc c) := fun z =>
  (hasDerivAt_fc c z).differentiableAt

/-- **The `p`-th iterate of `f_c` has area multiplicity `2ᵖ`**, with the stretching
`|(f_c^p)'|`. -/
theorem areaMultiplicity_fc_iterate (c : ℂ) (p : ℕ) :
    AreaMultiplicity volume volume ((MLC.Quadratic.fc c)^[p])
      (fun z => ENNReal.ofReal ‖deriv ((MLC.Quadratic.fc c)^[p]) z‖) (2 ^ p) := by
  have hdiff := differentiable_fc c
  have hφ : Measurable (MLC.Quadratic.fc c) := hdiff.continuous.measurable
  induction p with
  | zero =>
    simp [AreaMultiplicity]
  | succ p ih =>
    have hφ₂ : Measurable ((MLC.Quadratic.fc c)^[p]) := hφ.iterate p
    have hJ₁ : Measurable fun z : ℂ => ENNReal.ofReal ‖2 * z‖ := by fun_prop
    have hJ₂ : Measurable fun z => ENNReal.ofReal ‖deriv ((MLC.Quadratic.fc c)^[p]) z‖ :=
      (measurable_deriv _).norm.ennreal_ofReal
    have h := AreaMultiplicity.comp hφ hφ₂ hJ₁ hJ₂ (areaMultiplicity_fc c) ih
    have hfun : (fun z => ENNReal.ofReal ‖deriv ((MLC.Quadratic.fc c)^[p])
        (MLC.Quadratic.fc c z)‖ * ENNReal.ofReal ‖2 * z‖) =
        fun z => ENNReal.ofReal ‖deriv ((MLC.Quadratic.fc c)^[p + 1]) z‖ := by
      funext z
      rw [Function.iterate_succ, ← ENNReal.ofReal_mul (norm_nonneg _), ← norm_mul,
        deriv_comp z ((hdiff.iterate p).differentiableAt) (hdiff z), (hasDerivAt_fc c z).deriv]
    rw [hfun] at h
    rw [pow_succ']
    exact h

/-- **The pullback law for the iterates of `f_c`.** If `f_c^p` carries the curves of `ΓX` to curves
of `ΓY`, a curve `μ` going to `(μ.withDensity |(f_c^p)'|).map f_c^p`, then the extremal width of
`ΓX` is at most `2ᵖ` times that of `ΓY`. This is the estimate behind the Teichmüller
contraction: `p` iterations of a quadratic map have area multiplicity at most `2ᵖ`, so the width of
a pulled-back family grows by at most `2ᵖ`. -/
theorem extWidth_le_pow_two_mul_fc_iterate (c : ℂ) (p : ℕ) {ΓX ΓY : Set (Measure ℂ)}
    (hcurve : ∀ μ ∈ ΓX, (μ.withDensity fun z =>
      ENNReal.ofReal ‖deriv ((MLC.Quadratic.fc c)^[p]) z‖).map ((MLC.Quadratic.fc c)^[p]) ∈ ΓY) :
    extWidth volume ΓX ≤ 2 ^ p * extWidth volume ΓY :=
  extWidth_pullback_le ((differentiable_fc c).continuous.measurable.iterate p)
    (measurable_deriv _).norm.ennreal_ofReal (pow_ne_zero _ two_ne_zero)
    (ENNReal.pow_ne_top ENNReal.ofNat_ne_top) (areaMultiplicity_fc_iterate c p) hcurve

end Iterate

/-! ### Image loops -/

section Loops

/-- The pushforward and the density commute: `(ν.map γ).withDensity J = (ν.withDensity (J ∘ γ)).map γ`. -/
lemma withDensity_map_comp {α : Type*} [MeasurableSpace α] {ν : Measure α} {γ : α → ℂ}
    (hγ : Measurable γ) {J : ℂ → ℝ≥0∞} (hJ : Measurable J) :
    (ν.map γ).withDensity J = (ν.withDensity (J ∘ γ)).map γ := by
  refine Measure.ext fun A hA => ?_
  rw [withDensity_apply _ hA, Measure.map_apply hγ hA, withDensity_apply _ (hγ hA),
    ← lintegral_indicator hA, ← lintegral_indicator (hγ hA), lintegral_map (hJ.indicator hA) hγ]
  refine lintegral_congr fun x => ?_
  by_cases hx : γ x ∈ A <;> simp [Set.indicator, hx]

/-- **The length measure of the image of a `C¹` loop under a holomorphic map `φ`** is the
pushforward by `φ` of the length measure of the loop with the density `|φ'|`. -/
lemma loopMeasure_comp {φ : ℂ → ℂ} (hφ : Differentiable ℂ φ) {γ : ℝ → ℂ} (hγ : IsLoop γ) :
    loopMeasure (φ ∘ γ) =
      ((loopMeasure γ).withDensity fun z => ENNReal.ofReal ‖deriv φ z‖).map φ := by
  have hJ : Measurable fun z => ENNReal.ofReal ‖deriv φ z‖ :=
    (measurable_deriv φ).norm.ennreal_ofReal
  have hd : ∀ t, deriv (φ ∘ γ) t = deriv φ (γ t) * deriv γ t := fun t =>
    deriv_comp t (hφ.differentiableAt) ((hγ.hasDerivAt t).differentiableAt)
  have hγm := hγ.continuous.measurable
  have hf : Measurable fun t => ENNReal.ofReal ‖deriv γ t‖ :=
    hγ.continuous_deriv.norm.measurable.ennreal_ofReal
  have hdens : (fun t => ENNReal.ofReal ‖deriv (φ ∘ γ) t‖) =
      (fun t => ENNReal.ofReal ‖deriv γ t‖) *
        ((fun z => ENNReal.ofReal ‖deriv φ z‖) ∘ γ) := by
    funext t
    simp only [hd, Pi.mul_apply, Function.comp, norm_mul]
    rw [← ENNReal.ofReal_mul (norm_nonneg _), mul_comm]
  unfold loopMeasure
  rw [withDensity_map_comp hγm hJ, ← withDensity_mul _ hf (hJ.comp hγm),
    Measure.map_map hφ.continuous.measurable hγm, hdens]

/-- **The pullback law for loop families under `f_c^p`.** If `f_c^p` maps each loop of `ΓX` to a
loop of `ΓY`, the extremal width of `ΓX` is at most `2ᵖ` times that of `ΓY`. -/
theorem extWidth_le_pow_two_mul_fc_iterate_of_loops (c : ℂ) (p : ℕ) {ΓX ΓY : Set (Measure ℂ)}
    (h : ∀ μ ∈ ΓX, ∃ γ, IsLoop γ ∧ μ = loopMeasure γ ∧
      loopMeasure ((MLC.Quadratic.fc c)^[p] ∘ γ) ∈ ΓY) :
    extWidth volume ΓX ≤ 2 ^ p * extWidth volume ΓY :=
  extWidth_le_pow_two_mul_fc_iterate c p fun μ hμ => by
    obtain ⟨γ, hγ, rfl, hY⟩ := h μ hμ
    rwa [← loopMeasure_comp ((differentiable_fc c).iterate p) hγ]

end Loops

end

end MLC.Research
