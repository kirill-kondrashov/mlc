import Mlc.Quadratic.Complex.Bottcher.BottcherJointDeriv
import Mlc.Quadratic.Complex.Bottcher.BottcherInverse

/-!
# Parametrized holomorphic Böttcher inverse (ℂ² inverse function theorem)

Assembling the joint-differentiability keystone (`BottcherJointDeriv.lean`) and the
`z`-derivative nonvanishing (`BottcherInverse.lean`), this file runs the inverse
function theorem in `ℂ²` on the joint Böttcher map `F(c,z) = (c, φ_c(z))`.

Because `F` is `C¹` over `ℂ` and its Fréchet derivative at a deep-exterior base
point is a `ContinuousLinearEquiv` (block-triangular with invertible `(2,2)`-entry
`∂_z φ ≠ 0`), Mathlib's `ContDiffAt.to_localInverse` yields a `C¹` local inverse
`ψ = F⁻¹`. Its second component `c ↦ (ψ(c,w)).2 = φ_c⁻¹(w)` is therefore
`ℂ`-differentiable in the parameter `c` — the **c-holomorphy of the parametrized
Böttcher inverse**, which was the target of this whole development.
-/

namespace MLC
open Quadratic Complex Metric Filter Topology Set

theorem exists_param_holo_bottcher_inverse (c₀ : ℂ) :
    ∃ (z₀ w₀ : ℂ) (ψ : ℂ × ℂ → ℂ × ℂ),
      w₀ = logSeriesBottcherApprox c₀ z₀ ∧
      ContDiffAt ℂ 1 ψ (c₀, w₀) ∧
      ψ (c₀, w₀) = (c₀, z₀) ∧
      (∀ᶠ p in 𝓝 (c₀, z₀),
        ψ (p.1, logSeriesBottcherApprox p.1 p.2) = p) ∧
      DifferentiableAt ℂ (fun c => (ψ (c, w₀)).2) c₀ ∧
      DifferentiableAt ℂ (fun w => (ψ (c₀, w)).2) w₀ := by
  obtain ⟨R, hRge, hRderiv⟩ := logSeriesBottcherApprox_deriv_ne_zero_exterior c₀
  set M : ℝ := max R (‖c₀‖ + 5) + 1 with hM
  have hMpos : 0 < M := by
    have : (0:ℝ) ≤ max R (‖c₀‖ + 5) := le_trans (by positivity) (le_max_right _ _)
    linarith
  set z₀ : ℂ := (M : ℂ) with hz₀def
  have hnz₀ : ‖z₀‖ = M := by rw [hz₀def, Complex.norm_real, Real.norm_of_nonneg hMpos.le]
  have hz₀big : ‖c₀‖ + 3 * 1 + 2 < ‖z₀‖ := by
    rw [hnz₀, hM]; have := le_max_right R (‖c₀‖ + 5); linarith
  have hz₀R : R < ‖z₀‖ := by rw [hnz₀, hM]; have := le_max_left R (‖c₀‖ + 5); linarith
  set F : ℂ × ℂ → ℂ × ℂ := fun p => (p.1, logSeriesBottcherApprox p.1 p.2) with hFdef
  have hx₀mem : (c₀, z₀) ∈ ball c₀ 1 ×ˢ ball z₀ 1 := by
    rw [Set.mem_prod, mem_ball, mem_ball, dist_self, dist_self]; exact ⟨one_pos, one_pos⟩
  have hphi : ContDiffAt ℂ 1 (fun p : ℂ × ℂ => logSeriesBottcherApprox p.1 p.2) (c₀, z₀) :=
    logSeriesBottcherApprox_contDiffAt_one_joint (a := 1) one_pos hz₀big hx₀mem
  have hFcd : ContDiffAt ℂ 1 F (c₀, z₀) := contDiffAt_fst.prodMk hphi
  set D₂ : (ℂ × ℂ) →L[ℂ] ℂ :=
    fderiv ℂ (fun p : ℂ × ℂ => logSeriesBottcherApprox p.1 p.2) (c₀, z₀) with hD₂
  have hφfd : HasFDerivAt (fun p : ℂ × ℂ => logSeriesBottcherApprox p.1 p.2) D₂ (c₀, z₀) :=
    (hphi.differentiableAt one_ne_zero).hasFDerivAt
  set Lclm : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) := (ContinuousLinearMap.fst ℂ ℂ ℂ).prod D₂ with hLclm
  have hFL : HasFDerivAt F Lclm (c₀, z₀) := hasFDerivAt_fst.prodMk hφfd
  set b : ℂ := deriv (fun z => logSeriesBottcherApprox c₀ z) z₀ with hb
  have hbne : b ≠ 0 := hRderiv z₀ hz₀R
  have hslice : HasFDerivAt (fun z : ℂ => logSeriesBottcherApprox c₀ z)
      (D₂.comp (ContinuousLinearMap.inr ℂ ℂ ℂ)) z₀ :=
    hφfd.comp z₀ (hasFDerivAt_prodMk_right c₀ z₀)
  have hD01 : D₂ (0, 1) = b := by
    have hd := hslice.hasDerivAt
    rw [hb, hd.deriv]
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
  have hval : ∀ u v : ℂ, Lclm (u, v) = (u, D₂ (u, v)) := by
    intro u v; rw [hLclm]; rfl
  have hker : (↑Lclm : (ℂ × ℂ) →ₗ[ℂ] (ℂ × ℂ)).ker = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    rintro ⟨u, v⟩ h
    have h0 : ((u : ℂ), D₂ (u, v)) = (0 : ℂ × ℂ) := by
      have hh : Lclm (u, v) = (0 : ℂ × ℂ) := h
      rw [hval] at hh; exact hh
    have hu : u = 0 := (Prod.ext_iff.1 h0).1
    have hv0 : D₂ (0, v) = 0 := by
      have := (Prod.ext_iff.1 h0).2; rwa [hu] at this
    have hsm : D₂ (0, v) = v * b := by
      have hpair : ((0 : ℂ), v) = v • ((0 : ℂ), (1 : ℂ)) := by
        simp [Prod.smul_mk, smul_eq_mul]
      rw [hpair, map_smul, hD01, smul_eq_mul]
    rw [hsm] at hv0
    have hv : v = 0 := by
      rcases mul_eq_zero.1 hv0 with h1 | h2
      · exact h1
      · exact absurd h2 hbne
    rw [hu, hv]; rfl
  have hrange : (↑Lclm : (ℂ × ℂ) →ₗ[ℂ] (ℂ × ℂ)).range = ⊤ := by
    rw [LinearMap.range_eq_top]
    exact LinearMap.injective_iff_surjective.1 (LinearMap.ker_eq_bot.1 hker)
  set e : (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ) := ContinuousLinearEquiv.ofBijective Lclm hker hrange with he
  have hFLe : HasFDerivAt F (↑e : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) (c₀, z₀) := by
    rw [he, ContinuousLinearEquiv.coe_ofBijective]; exact hFL
  have hn : (1 : WithTop ℕ∞) ≠ 0 := one_ne_zero
  have hFx₀ : F (c₀, z₀) = (c₀, logSeriesBottcherApprox c₀ z₀) := rfl
  refine ⟨z₀, logSeriesBottcherApprox c₀ z₀, hFcd.localInverse hFLe hn, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · have h := hFcd.to_localInverse hFLe hn; rwa [hFx₀] at h
  · have h := hFcd.localInverse_apply_image hFLe hn; rwa [hFx₀] at h
  · have hstr := hFcd.hasStrictFDerivAt' hFLe hn
    filter_upwards [hstr.eventually_left_inverse] with p hp
    exact hp
  · have hψcd : ContDiffAt ℂ 1 (hFcd.localInverse hFLe hn) (c₀, logSeriesBottcherApprox c₀ z₀) := by
      have h := hFcd.to_localInverse hFLe hn; rwa [hFx₀] at h
    have hψdiff := hψcd.differentiableAt one_ne_zero
    have hcurve : DifferentiableAt ℂ (fun c : ℂ => (c, logSeriesBottcherApprox c₀ z₀)) c₀ :=
      differentiableAt_id.prodMk (differentiableAt_const _)
    exact (hψdiff.comp c₀ hcurve).snd
  · have hψcd : ContDiffAt ℂ 1 (hFcd.localInverse hFLe hn) (c₀, logSeriesBottcherApprox c₀ z₀) := by
      have h := hFcd.to_localInverse hFLe hn; rwa [hFx₀] at h
    have hψdiff := hψcd.differentiableAt one_ne_zero
    have hcurve : DifferentiableAt ℂ (fun w : ℂ => (c₀, w)) (logSeriesBottcherApprox c₀ z₀) :=
      (differentiableAt_const _).prodMk differentiableAt_id
    exact (hψdiff.comp _ hcurve).snd

end MLC
