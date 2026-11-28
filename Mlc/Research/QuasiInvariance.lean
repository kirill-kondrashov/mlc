import Mlc.Research.AreaMultiplicity
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Quasi-invariance of the extremal width under a change of chart

The moduli of a nest of parameter pieces live in the parameter plane, while the annuli that an a
priori bound controls live in the dynamical plane; the phase–parameter relation (Lyubich,
Kahn–Lyubich; Dudko §3.9, §4.1–§4.3) carries the moduli from one plane to the other through a
correspondence that is conformal or quasi-conformal. This module proves the invariance of the
extremal width of `ExtremalLength.lean` that such a transport needs, for a `C¹` correspondence:

* **Structure `QcEmbedding Ω φ K`**: `φ` is a `C¹` embedding of the open set `Ω` with invertible
  derivative whose dilatation is at most `K`, that is, `‖Dφ‖² ≤ K |det Dφ|` (the ratio of the
  singular values of `Dφ` is at most `K`). An injective holomorphic map with non-vanishing
  derivative is one with `K = 1` (`QcEmbedding.of_holomorphic`).
* **Lemma `QcEmbedding.areaMultiplicity`**: the area formula of Mathlib gives the hypothesis of the
  pullback law with multiplicity `K` and stretching `‖Dφ‖`.
* **Theorem `extWidth_le_of_qcEmbedding`** (quasi-invariance, and conformal invariance for
  `K = 1`): if `φ` carries every curve of `ΓX`, which lies in `Ω`, to a curve that dominates a
  curve of `ΓY`, then `W(ΓX) ≤ K W(ΓY)`.
* **Lemma `Separates.image`**: a map that is continuous and injective on the compact closure of
  `O`, with `φ '' O` open, carries a loop that separates `K` from the complement of `O` to a loop
  that separates `φ '' K` from the complement of `φ '' O` (the first exit time of a path from
  `φ '' O`).
* **Definition `ConnectedNest.map`**, **theorem `ConnectedNest.extWidth_loops_le_map`** and
  **theorem `ConnectedNest.DivergentModuli.map`**: the image of a connected nest under such an
  embedding, in a set `S'` that corresponds to `S` over the first piece, is a connected nest, the
  modulus of each of its annuli is at least `1/K` times the modulus of the annulus of the original
  nest, and a nest with divergent moduli has an image with divergent moduli.

The correspondence is `C¹`: a quasi-conformal homeomorphism is in general only absolutely
continuous on lines, and the analytic definition of quasi-conformality is not formalized here. The
theorem says that a chart of bounded dilatation between a phase nest and a parameter nest
transports divergent moduli, hence (`DivergentModuli.shrinking`,
`ConnectedNest.nonempty_parameterRealization`) the shrinking of the parameter nest and the
separation estimate of every budget. It constructs neither such a chart nor such a phase nest:
the phase–parameter relation stays open.
-/

namespace MLC.Research

open MeasureTheory ENNReal Set Topology

noncomputable section

/-! ### Embeddings with bounded dilatation -/

/-- `φ` is a `C¹` embedding of the open set `Ω` with dilatation at most `K`. -/
structure QcEmbedding (Ω : Set ℂ) (φ : ℂ → ℂ) (K : ℝ) : Prop where
  isOpen : IsOpen Ω
  contDiffOn : ContDiffOn ℝ 1 φ Ω
  injOn : InjOn φ Ω
  det_ne : ∀ z ∈ Ω, (fderiv ℝ φ z).det ≠ 0
  dilatation : ∀ z ∈ Ω, ‖fderiv ℝ φ z‖ ^ 2 ≤ K * |(fderiv ℝ φ z).det|

namespace QcEmbedding

variable {Ω : Set ℂ} {φ : ℂ → ℂ} {K : ℝ} (h : QcEmbedding Ω φ K)
include h

lemma differentiableAt {z : ℂ} (hz : z ∈ Ω) : DifferentiableAt ℝ φ z :=
  (h.contDiffOn.differentiableOn one_ne_zero).differentiableAt (h.isOpen.mem_nhds hz)

lemma hasStrictFDerivAt {z : ℂ} (hz : z ∈ Ω) : HasStrictFDerivAt φ (fderiv ℝ φ z) z :=
  ((h.contDiffOn.contDiffAt (h.isOpen.mem_nhds hz)).hasStrictFDerivAt one_ne_zero)

/-- A `C¹` embedding with invertible derivative is open. -/
lemma image_mem_nhds {z : ℂ} (hz : z ∈ Ω) {s : Set ℂ} (hs : s ∈ 𝓝 z) : φ '' s ∈ 𝓝 (φ z) := by
  let e : ℂ ≃L[ℝ] ℂ :=
    ((fderiv ℝ φ z : ℂ →ₗ[ℝ] ℂ).equivOfDetNeZero (h.det_ne z hz)).toContinuousLinearEquiv
  have he : (e : ℂ →L[ℝ] ℂ) = fderiv ℝ φ z := rfl
  have hs' : HasStrictFDerivAt φ (e : ℂ →L[ℝ] ℂ) z := by
    rw [he]
    exact h.hasStrictFDerivAt hz
  rw [← hs'.map_nhds_eq_of_equiv]
  exact Filter.image_mem_map hs

lemma isOpen_image {U : Set ℂ} (hU : IsOpen U) (hUΩ : U ⊆ Ω) : IsOpen (φ '' U) := by
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨z, hz, rfl⟩
  exact h.image_mem_nhds (hUΩ hz) (hU.mem_nhds hz)

/-- **A `C¹` embedding with dilatation at most `K` has area multiplicity `K`** for the stretching
`‖Dφ‖`: the area formula of Mathlib with `‖Dφ‖² ≤ K |det Dφ|`. -/
lemma areaMultiplicity (hK : 0 ≤ K) (hφ : Measurable φ) :
    AreaMultiplicity (volume.restrict Ω) volume φ (fun z => ENNReal.ofReal ‖fderiv ℝ φ z‖)
      (ENNReal.ofReal K) := by
  refine Measure.le_iff.2 fun B hB => ?_
  rw [Measure.map_apply hφ hB, withDensity_apply _ (hφ hB), Measure.restrict_restrict (hφ hB)]
  have hs : MeasurableSet (φ ⁻¹' B ∩ Ω) := (hφ hB).inter h.isOpen.measurableSet
  have hArea := lintegral_abs_det_fderiv_eq_addHaar_image (volume : Measure ℂ) hs
    (f := φ) (f' := fun z => fderiv ℝ φ z)
    (fun z hz => (h.differentiableAt hz.2).hasFDerivAt.hasFDerivWithinAt)
    (h.injOn.mono inter_subset_right)
  calc ∫⁻ z in φ ⁻¹' B ∩ Ω, ENNReal.ofReal ‖fderiv ℝ φ z‖ ^ 2
      ≤ ∫⁻ z in φ ⁻¹' B ∩ Ω, ENNReal.ofReal K * ENNReal.ofReal |(fderiv ℝ φ z).det| := by
        refine setLIntegral_mono' hs fun z hz => ?_
        rw [← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_mul hK]
        exact ENNReal.ofReal_le_ofReal (h.dilatation z hz.2)
    _ = ENNReal.ofReal K * volume (φ '' (φ ⁻¹' B ∩ Ω)) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        exact congrArg _ hArea
    _ ≤ ENNReal.ofReal K * volume B := by
        gcongr
        exact image_subset_iff.2 inter_subset_left
    _ = ((ENNReal.ofReal K) • (volume : Measure ℂ)) B := by simp

end QcEmbedding

/-- The norm of the multiplication by `w` is `|w|`. -/
lemma norm_mulCLM (w : ℂ) : ‖mulCLM w‖ = ‖w‖ := by
  unfold mulCLM
  rw [ContinuousLinearMap.norm_restrictScalars, ContinuousLinearMap.norm_smulRight_apply,
    norm_one, one_mul]

/-- The real derivative of a holomorphic map is the multiplication by its complex derivative. -/
lemma fderiv_eq_mulCLM {φ : ℂ → ℂ} {z : ℂ} (hd : DifferentiableAt ℂ φ z) :
    fderiv ℝ φ z = mulCLM (deriv φ z) :=
  (hd.hasDerivAt.hasFDerivAt.restrictScalars ℝ).fderiv

/-- **A conformal embedding has dilatation `1`**: an injective holomorphic map with nonvanishing
derivative on an open set. -/
lemma QcEmbedding.of_holomorphic {Ω : Set ℂ} {φ : ℂ → ℂ} (hΩ : IsOpen Ω)
    (hd : DifferentiableOn ℂ φ Ω) (hinj : InjOn φ Ω) (hne : ∀ z ∈ Ω, deriv φ z ≠ 0) :
    QcEmbedding Ω φ 1 where
  isOpen := hΩ
  contDiffOn := (hd.contDiffOn hΩ).restrict_scalars ℝ
  injOn := hinj
  det_ne z hz := by
    rw [fderiv_eq_mulCLM (hd.differentiableAt (hΩ.mem_nhds hz)), det_mulCLM]
    exact pow_ne_zero 2 (norm_ne_zero_iff.2 (hne z hz))
  dilatation z hz := by
    rw [fderiv_eq_mulCLM (hd.differentiableAt (hΩ.mem_nhds hz)), det_mulCLM, norm_mulCLM, one_mul,
      abs_of_nonneg (sq_nonneg _)]

/-! ### Loops under a `C¹` map -/

lemma IsLoop.comp_contDiffOn {γ : ℝ → ℂ} (hγ : IsLoop γ) {Ω : Set ℂ} {φ : ℂ → ℂ}
    (hφ : ContDiffOn ℝ 1 φ Ω) (hγΩ : ∀ t, γ t ∈ Ω) : IsLoop (φ ∘ γ) :=
  ⟨contDiffOn_univ.1 (hφ.comp hγ.1.contDiffOn (fun t _ => hγΩ t)), hγ.2.comp φ⟩

/-- The length measure of the image of a `C¹` loop under a `C¹` map is at most the pushforward of
the length measure of the loop with the density `‖Dφ‖`. -/
lemma loopMeasure_comp_le {Ω : Set ℂ} (hΩ : IsOpen Ω) {φ : ℂ → ℂ} (hφ : ContDiffOn ℝ 1 φ Ω)
    (hφm : Measurable φ) {γ : ℝ → ℂ} (hγ : IsLoop γ) (hγΩ : ∀ t, γ t ∈ Ω) :
    loopMeasure (φ ∘ γ) ≤
      ((loopMeasure γ).withDensity fun z => ENNReal.ofReal ‖fderiv ℝ φ z‖).map φ := by
  have hJ : Measurable fun z => ENNReal.ofReal ‖fderiv ℝ φ z‖ :=
    (measurable_fderiv ℝ φ).norm.ennreal_ofReal
  have hγm := hγ.continuous.measurable
  have hf : Measurable fun t => ENNReal.ofReal ‖deriv γ t‖ :=
    hγ.continuous_deriv.norm.measurable.ennreal_ofReal
  have hd : ∀ t, deriv (φ ∘ γ) t = fderiv ℝ φ (γ t) (deriv γ t) := fun t =>
    (((hφ.differentiableOn one_ne_zero).differentiableAt (hΩ.mem_nhds (hγΩ t))).hasFDerivAt.comp_hasDerivAt
      t (hγ.hasDerivAt t)).deriv
  have hdens : ∀ t, ENNReal.ofReal ‖deriv (φ ∘ γ) t‖ ≤
      ENNReal.ofReal ‖deriv γ t‖ * ((fun z => ENNReal.ofReal ‖fderiv ℝ φ z‖) ∘ γ) t := by
    intro t
    simp only [Function.comp_apply]
    rw [← ENNReal.ofReal_mul (norm_nonneg _), hd t, mul_comm]
    exact ENNReal.ofReal_le_ofReal ((fderiv ℝ φ (γ t)).le_opNorm _)
  unfold loopMeasure
  rw [withDensity_map_comp hγm hJ, ← withDensity_mul _ hf (hJ.comp hγm),
    Measure.map_map hφm hγm]
  refine Measure.le_iff.2 fun s hs => ?_
  rw [Measure.map_apply (hφm.comp hγm) hs, Measure.map_apply (hφm.comp hγm) hs]
  exact Measure.le_iff'.1 (withDensity_mono (Filter.Eventually.of_forall hdens)) _

/-! ### The pullback law with domination and a restricted area -/

/-- Restricting the area to a region that carries all the curves does not decrease the extremal
width, hence it does not matter. -/
lemma extLength_restrict_le {α : Type*} [MeasurableSpace α] {m : Measure α} {Ω : Set α}
    (hΩ : MeasurableSet Ω) {Γ : Set (Measure α)} (hΓ : ∀ μ ∈ Γ, μ Ωᶜ = 0) :
    extLength (m.restrict Ω) Γ ≤ extLength m Γ := by
  refine extLength_le fun ρ hρ hA => ?_
  have hρ' : Measurable (Ω.indicator ρ) := hρ.indicator hΩ
  have harea : rhoArea (m.restrict Ω) ρ = rhoArea m (Ω.indicator ρ) := by
    unfold rhoArea
    rw [← lintegral_indicator hΩ]
    refine lintegral_congr fun x => ?_
    by_cases hx : x ∈ Ω <;> simp [hx]
  have hlen : minLength ρ Γ = minLength (Ω.indicator ρ) Γ := by
    unfold minLength
    refine iInf_congr fun μ => iInf_congr fun hμ => ?_
    unfold rhoLength
    exact (lintegral_indicator_of_compl_null (hΓ μ hμ) ρ).symm
  rw [harea] at hA ⊢
  rw [hlen]
  exact ratio_le_extLength hρ' hA

/-- **The pullback law for a `C¹` embedding with dilatation at most `K`** (quasi-invariance of the
extremal width): if `φ` carries every curve of `ΓX`, which lies in `Ω`, to a curve that
dominates a curve of `ΓY`, then `W(ΓX) ≤ K W(ΓY)`. For `K = 1` and a holomorphic `φ` this is the
conformal invariance of the extremal width. -/
theorem extWidth_le_of_qcEmbedding {Ω : Set ℂ} {φ : ℂ → ℂ} {K : ℝ} (h : QcEmbedding Ω φ K)
    (hK : 0 < K) (hφm : Measurable φ) {ΓX ΓY : Set (Measure ℂ)} (hX : ∀ μ ∈ ΓX, μ Ωᶜ = 0)
    (hcurve : ∀ μ ∈ ΓX, ∃ ν ∈ ΓY,
      ν ≤ (μ.withDensity fun z => ENNReal.ofReal ‖fderiv ℝ φ z‖).map φ) :
    extWidth volume ΓX ≤ ENNReal.ofReal K * extWidth volume ΓY := by
  set ΓY' : Set (Measure ℂ) := {ν' | ∃ ν ∈ ΓY, ν ≤ ν'} with hΓY'
  have hJ : Measurable fun z => ENNReal.ofReal ‖fderiv ℝ φ z‖ :=
    (measurable_fderiv ℝ φ).norm.ennreal_ofReal
  have h1 : extWidth volume ΓX ≤ extWidth (volume.restrict Ω) ΓX :=
    ENNReal.inv_le_inv.2 (extLength_restrict_le h.isOpen.measurableSet hX)
  have h2 : extWidth (volume.restrict Ω) ΓX ≤
      ENNReal.ofReal K * extWidth volume ΓY' :=
    extWidth_pullback_le hφm hJ (ENNReal.ofReal_pos.2 hK).ne' ENNReal.ofReal_ne_top
      (h.areaMultiplicity hK.le hφm)
      (fun μ hμ => by
        obtain ⟨ν, hν, hle⟩ := hcurve μ hμ
        exact ⟨ν, hν, hle⟩)
  have h3 : extWidth volume ΓY' ≤ extWidth volume ΓY :=
    ENNReal.inv_le_inv.2 (extLength_mono fun μ hμ => hμ)
  exact h1.trans (h2.trans (by gcongr))

/-! ### Separation under an embedding -/

/-- A loop in `O` that separates `K` from the complement of `O` forces `K ⊆ O`. -/
lemma Separates.subset {γ : ℝ → ℂ} {K O : Set ℂ} (hsep : Separates γ K O)
    (hγO : ∀ s, γ s ∈ O) : K ⊆ O := by
  intro z hz
  by_contra hzO
  obtain ⟨t, -, s, hs⟩ := hsep z hz z hzO 0 0 (fun _ => z) le_rfl continuousOn_const rfl rfl
  exact hzO (by rw [show z = γ s from hs]; exact hγO s)

/-- **A homeomorphism onto an open image carries separating loops to separating loops.** Let `φ`
be continuous and injective on the compact set `cl O`, with `φ '' O` open. If a loop in `O`
separates `K` from the complement of `O`, then `φ ∘ γ` separates `φ '' K` from the complement of
`φ '' O`: a path from `φ '' K` to the complement of `φ '' O` stays in `φ '' O` up to its first exit
time, where it is the image of a path in `cl O` that ends outside `O`. -/
lemma Separates.image {γ : ℝ → ℂ} {K O : Set ℂ} {φ : ℂ → ℂ} (hsep : Separates γ K O)
    (hγO : ∀ s, γ s ∈ O) (hcont : ContinuousOn φ (closure O)) (hinj : InjOn φ (closure O))
    (hcpt : IsCompact (closure O)) (hopen : IsOpen (φ '' O)) :
    Separates (φ ∘ γ) (φ '' K) (φ '' O) := by
  intro z hz w hw a b p hab hp hpa hpb
  obtain ⟨z₀, hz₀, rfl⟩ := hz
  have hKO : K ⊆ O := hsep.subset hγO
  set T := closure O with hT
  set F : Set ℝ := Icc a b ∩ p ⁻¹' (φ '' O)ᶜ with hF
  have hFclosed : IsClosed F := hp.preimage_isClosed_of_isClosed isClosed_Icc hopen.isClosed_compl
  have hbF : b ∈ F := ⟨⟨hab, le_rfl⟩, by simpa [hpb] using hw⟩
  have hFbdd : BddBelow F := ⟨a, fun τ hτ => hτ.1.1⟩
  set τ := sInf F with hτdef
  have hτF : τ ∈ F := hFclosed.csInf_mem ⟨b, hbF⟩ hFbdd
  have haτ : a ≤ τ := hτF.1.1
  have hτb : τ ≤ b := hτF.1.2
  have haF : a ∉ F := fun haF => haF.2 ⟨z₀, hKO hz₀, hpa.symm⟩
  have haτ' : a < τ := lt_of_le_of_ne haτ fun h => haF (h ▸ hτF)
  have hbefore : ∀ σ ∈ Ico a τ, p σ ∈ φ '' O := by
    intro σ hσ
    by_contra hnot
    exact absurd (csInf_le hFbdd (⟨⟨hσ.1, hσ.2.le.trans hτb⟩, hnot⟩ : σ ∈ F)) (not_le.2 hσ.2)
  have hclosed : IsClosed (φ '' T) := (hcpt.image_of_continuousOn hcont).isClosed
  have hpτ : p τ ∈ φ '' T := by
    have hcw : ContinuousWithinAt p (Ico a τ) τ :=
      (hp.continuousWithinAt ⟨haτ, hτb⟩).mono (Ico_subset_Icc_self.trans (Icc_subset_Icc_right hτb))
    have hcl : τ ∈ closure (Ico a τ) := by
      rw [closure_Ico haτ'.ne]
      exact ⟨haτ, le_rfl⟩
    have h2 : p '' Ico a τ ⊆ φ '' T := by
      rintro _ ⟨σ, hσ, rfl⟩
      obtain ⟨y, hy, hy'⟩ := hbefore σ hσ
      exact ⟨y, subset_closure hy, hy'⟩
    exact hclosed.closure_subset_iff.2 h2 (hcw.mem_closure_image hcl)
  have hmem : ∀ σ : Icc a τ, p σ ∈ φ '' T := by
    rintro ⟨σ, hσ⟩
    rcases hσ.2.eq_or_lt with h | h
    · simpa [h] using hpτ
    · obtain ⟨y, hy, hy'⟩ := hbefore σ ⟨hσ.1, h⟩
      exact ⟨y, subset_closure hy, hy'⟩
  obtain ⟨y, hyT, hy⟩ := hpτ
  have hyO : y ∉ O := fun hyO => hτF.2 ⟨y, hyO, hy⟩
  let g : T → ℂ := fun x => φ x
  have hgcont : Continuous g := hcont.restrict
  have hginj : Function.Injective g := fun x x' hxx => Subtype.ext (hinj x.2 x'.2 hxx)
  haveI : CompactSpace T := isCompact_iff_compactSpace.1 hcpt
  have hgemb : Topology.IsClosedEmbedding g := hgcont.isClosedEmbedding hginj
  let q' : Icc a τ → T := fun σ => ⟨Function.invFunOn φ T (p σ), Function.invFunOn_mem (hmem σ)⟩
  have hq'cont : Continuous q' := by
    rw [hgemb.isInducing.continuous_iff]
    have : g ∘ q' = fun σ : Icc a τ => p σ := by
      funext σ
      exact Function.invFunOn_eq (hmem σ)
    rw [this]
    exact (hp.mono (Icc_subset_Icc_right hτb)).restrict
  let q : ℝ → ℂ := fun σ => if hσ : σ ∈ Icc a τ then ((q' ⟨σ, hσ⟩ : T) : ℂ) else z₀
  have hqcont : ContinuousOn q (Icc a τ) := by
    rw [continuousOn_iff_continuous_restrict]
    have : (Icc a τ).restrict q = fun σ : Icc a τ => ((q' σ : T) : ℂ) := by
      funext σ
      show q σ = ((q' σ : T) : ℂ)
      simp only [q, dif_pos σ.2]
    rw [this]
    exact continuous_subtype_val.comp hq'cont
  have hqa : q a = z₀ := by
    have ha : a ∈ Icc a τ := ⟨le_rfl, haτ⟩
    simp only [q, dif_pos ha, q']
    rw [hpa]
    exact hinj.leftInvOn_invFunOn (subset_closure (hKO hz₀))
  have hqτ : q τ = y := by
    have hτ : τ ∈ Icc a τ := ⟨haτ, le_rfl⟩
    simp only [q, dif_pos hτ, q']
    rw [← hy]
    exact hinj.leftInvOn_invFunOn hyT
  obtain ⟨σ, hσ, s, hs⟩ := hsep z₀ hz₀ y hyO a τ q haτ hqcont hqa hqτ
  have hσq : q σ = Function.invFunOn φ T (p σ) := by simp only [q, dif_pos hσ, q']
  have hpσ : φ (q σ) = p σ := by
    rw [hσq]
    exact Function.invFunOn_eq (hmem ⟨σ, hσ⟩)
  exact ⟨σ, ⟨hσ.1, hσ.2.trans hτb⟩, s, by rw [Function.comp_apply, ← hs, hpσ]⟩

/-! ### The image of a nest -/

namespace ConnectedNest

variable {S S' : Set ℂ} {c : ℂ} (D : ConnectedNest S c) {Ω : Set ℂ} {φ : ℂ → ℂ} {K : ℝ}

lemma piece_subset (hΩ : closure (D.piece 0) ⊆ Ω) (n : ℕ) : D.piece n ⊆ Ω :=
  (D.antitone_piece (Nat.zero_le n)).trans (subset_closure.trans hΩ)

lemma closure_piece_subset (hΩ : closure (D.piece 0) ⊆ Ω) (n : ℕ) : closure (D.piece n) ⊆ Ω :=
  (closure_mono (D.antitone_piece (Nat.zero_le n))).trans hΩ

lemma closure_image_piece_subset (h : QcEmbedding Ω φ K) (hΩ : closure (D.piece 0) ⊆ Ω) (n : ℕ) :
    closure (φ '' D.piece n) ⊆ φ '' closure (D.piece n) :=
  closure_minimal (image_mono subset_closure)
    ((D.compact_closure n).image_of_continuousOn
      (h.contDiffOn.continuousOn.mono (D.closure_piece_subset hΩ n))).isClosed

/-- The image of a nest under a `C¹` embedding of a neighbourhood of the closure of its first
piece, in a set `S'` that corresponds to `S` over the image of the first piece. -/
def map (h : QcEmbedding Ω φ K) (hΩ : closure (D.piece 0) ⊆ Ω)
    (hS : φ '' D.piece 0 ∩ S' = φ '' (D.piece 0 ∩ S)) : ConnectedNest S' (φ c) where
  piece n := φ '' D.piece n
  open_piece n := h.isOpen_image (D.open_piece n) (D.piece_subset hΩ n)
  contains n := ⟨c, D.contains n, rfl⟩
  connected n := by
    have hn0 : D.piece n ⊆ D.piece 0 := D.antitone_piece (Nat.zero_le n)
    have himg : φ '' D.piece n ∩ S' = φ '' (D.piece n ∩ S) := by
      calc φ '' D.piece n ∩ S' = φ '' D.piece n ∩ (φ '' D.piece 0 ∩ S') := by
            rw [← inter_assoc, inter_eq_left.2 (image_mono hn0)]
        _ = φ '' D.piece n ∩ φ '' (D.piece 0 ∩ S) := by rw [hS]
        _ = φ '' (D.piece n ∩ (D.piece 0 ∩ S)) :=
            (h.injOn.image_inter (D.piece_subset hΩ n)
              (inter_subset_left.trans (D.piece_subset hΩ 0))).symm
        _ = φ '' (D.piece n ∩ S) := by rw [← inter_assoc, inter_eq_left.2 hn0]
    rw [himg]
    exact (D.connected n).image φ
      (h.contDiffOn.continuousOn.mono (inter_subset_left.trans (D.piece_subset hΩ n)))
  compact_closure n :=
    ((D.compact_closure n).image_of_continuousOn
      (h.contDiffOn.continuousOn.mono (D.closure_piece_subset hΩ n))).of_isClosed_subset
      isClosed_closure (D.closure_image_piece_subset h hΩ n)
  nested n := image_mono (D.nested n)

lemma map_annulus_subset (h : QcEmbedding Ω φ K) (hΩ : closure (D.piece 0) ⊆ Ω)
    (hS : φ '' D.piece 0 ∩ S' = φ '' (D.piece 0 ∩ S)) (j : ℕ) :
    φ '' D.annulus j ⊆ (D.map h hΩ hS).annulus j := by
  rintro _ ⟨y, ⟨hy1, hy2⟩, rfl⟩
  refine ⟨⟨y, hy1, rfl⟩, fun hmem => ?_⟩
  obtain ⟨y', hy', hyy'⟩ := D.closure_image_piece_subset h hΩ (j + 1) hmem
  exact hy2 (h.injOn (D.closure_piece_subset hΩ (j + 1) hy') (D.piece_subset hΩ j hy1) hyy' ▸ hy')

/-- A loop of the `j`-th annulus is carried by the embedding to a loop of the `j`-th annulus of the
image nest. -/
lemma map_mem_loops (h : QcEmbedding Ω φ K) (hΩ : closure (D.piece 0) ⊆ Ω)
    (hS : φ '' D.piece 0 ∩ S' = φ '' (D.piece 0 ∩ S)) {j : ℕ}
    {γ : ℝ → ℂ} (hγ : IsLoop γ) (hA : ∀ t, γ t ∈ D.annulus j)
    (hsep : Separates γ (closure (D.piece (j + 1))) (D.piece j)) :
    loopMeasure (φ ∘ γ) ∈ (D.map h hΩ hS).loops j := by
  have hγO : ∀ t, γ t ∈ D.piece j := fun t => (hA t).1
  refine ⟨φ ∘ γ, hγ.comp_contDiffOn h.contDiffOn
      (fun t => D.piece_subset hΩ j (hγO t)),
    fun t => D.map_annulus_subset h hΩ hS j ⟨γ t, hA t, rfl⟩, ?_, rfl⟩
  have himg := hsep.image (φ := φ) hγO
    (h.contDiffOn.continuousOn.mono (D.closure_piece_subset hΩ j)) (h.injOn.mono
      (D.closure_piece_subset hΩ j)) (D.compact_closure j)
    (h.isOpen_image (D.open_piece j) (D.piece_subset hΩ j))
  exact himg.mono (D.closure_image_piece_subset h hΩ (j + 1)) subset_rfl

/-- **Quasi-invariance of the moduli of a nest.** The modulus of the `j`-th annulus of a nest is
at most `K` times the modulus of the `j`-th annulus of its image under a `C¹` embedding with
dilatation at most `K`. -/
theorem extWidth_loops_le_map (h : QcEmbedding Ω φ K) (hK : 0 < K) (hφm : Measurable φ)
    (hΩ : closure (D.piece 0) ⊆ Ω) (hS : φ '' D.piece 0 ∩ S' = φ '' (D.piece 0 ∩ S)) (j : ℕ) :
    extWidth volume (D.loops j) ≤
      ENNReal.ofReal K * extWidth volume ((D.map h hΩ hS).loops j) := by
  refine extWidth_le_of_qcEmbedding h hK hφm (fun μ hμ => ?_) (fun μ hμ => ?_)
  · refine measure_mono_null (compl_subset_compl.2 ?_) (D.loops_compl_null hμ)
    exact fun x hx => D.piece_subset hΩ j hx.1
  · obtain ⟨γ, hγ, hA, hsep, rfl⟩ := hμ
    exact ⟨loopMeasure (φ ∘ γ), D.map_mem_loops h hΩ hS hγ hA hsep,
      loopMeasure_comp_le h.isOpen h.contDiffOn hφm hγ
        (fun t => D.piece_subset hΩ j (hA t).1)⟩

/-- **Divergent moduli are preserved by `C¹` embeddings of bounded dilatation.** -/
theorem DivergentModuli.map (hD : D.DivergentModuli) (h : QcEmbedding Ω φ K) (hK : 0 < K)
    (hφm : Measurable φ) (hΩ : closure (D.piece 0) ⊆ Ω)
    (hS : φ '' D.piece 0 ∩ S' = φ '' (D.piece 0 ∩ S)) : (D.map h hΩ hS).DivergentModuli := by
  intro C hC
  obtain ⟨n, hn⟩ := hD (ENNReal.ofReal K * C) (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hC)
  refine ⟨n, ?_⟩
  have hsum : ∑ j ∈ Finset.range n, extWidth volume (D.loops j) ≤
      ENNReal.ofReal K * ∑ j ∈ Finset.range n, extWidth volume ((D.map h hΩ hS).loops j) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => D.extWidth_loops_le_map h hK hφm hΩ hS j
  exact (ENNReal.mul_lt_mul_iff_right (ENNReal.ofReal_pos.2 hK).ne' ENNReal.ofReal_ne_top).1
    (hn.trans_le hsum)

end ConnectedNest

end

end MLC.Research
