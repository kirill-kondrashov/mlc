import Mlc.Quadratic.Complex.Bottcher.UltrahyperbolicPullback

/-!
# Little Picard core via Ahlfors rescaling

This file extracts the first genuine payoff of the curvature `≤ -1`
(ultrahyperbolic) metric on `ℂ ∖ {0,1}` built in `UltrahyperbolicMetric.lean` /
`UltrahyperbolicPullback.lean`: an **Ahlfors rescaling** argument that needs only
the Schwarz–Pick contraction (`pullback_density_contraction_exp`) and **not** the
completeness of the metric.

The pullback contraction says a holomorphic immersion `g : 𝔻 → ℂ ∖ {0,1}`
satisfies `σ(g 0)·‖g'(0)‖ ≤ 2` (Poincaré density of `𝔻` at the centre). Applying
this to the rescalings `g_R(ζ) = f(R·ζ)` of an *entire* immersion `f` omitting
`{0,1}` gives `σ(f 0)·‖f'(0)‖·R ≤ 2` for **all** `R > 0`; letting `R → ∞` forces
`f'(0) = 0`, contradicting the immersion hypothesis. Hence:

* `false_of_entire_immersion_omitting_two` — no entire immersion omits `{0,1}`;
* `exists_deriv_eq_zero_of_entire_omitting_two` — every entire function omitting
  `{0,1}` has a critical point.

This is the `picard-core` brick toward strong Montel (a family omitting two values
is normal) and, ultimately, the λ-lemma continuity step. The *full* little Picard
(such an `f` is constant) additionally requires handling isolated critical points,
where the pulled-back log-density has poles; that is the follow-up `picard-full`
brick.

All results are sorry-free and use only the Lean-core axioms.
-/

namespace MLC.Quadratic

open Complex Metric Set

/-- **No entire immersion omits two values (Ahlfors rescaling).** If `f : ℂ → ℂ`
is entire, omits `0` and `1`, and has nowhere-vanishing derivative, we reach a
contradiction: the Schwarz–Pick contraction of the curvature `≤ -1` metric applied
to the rescalings `ζ ↦ f (R·ζ)` gives `σ(f 0)·‖f'(0)‖·R ≤ 2` for all `R > 0`. -/
theorem false_of_entire_immersion_omitting_two
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (h0 : ∀ z, f z ≠ 0) (h1 : ∀ z, f z ≠ 1)
    (hfd : ∀ z, deriv f z ≠ 0) : False := by
  -- `A = σ(f 0)·‖f'(0)‖ > 0`.
  set A : ℝ := ultraDensityScaled (f 0) * ‖deriv f 0‖ with hA
  have hApos : 0 < A :=
    mul_pos (ultraDensityScaled_pos _) (norm_pos_iff.2 (hfd 0))
  -- For every `R > 0`, the rescaled contraction gives `R·A ≤ 2`.
  have key : ∀ R : ℝ, 0 < R → R * A ≤ 2 := by
    intro R hR
    have hRne : (R : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hR
    set g : ℂ → ℂ := fun ζ => f ((R : ℂ) * ζ) with hg
    -- derivative of the rescaling: `g'(ζ) = f'(R·ζ)·R`.
    have hderiv : ∀ ζ : ℂ, deriv g ζ = deriv f ((R : ℂ) * ζ) * (R : ℂ) := by
      intro ζ
      have hin : HasDerivAt (fun ζ : ℂ => (R : ℂ) * ζ) (R : ℂ) ζ := by
        simpa using (hasDerivAt_id ζ).const_mul (R : ℂ)
      have hout : HasDerivAt f (deriv f ((R : ℂ) * ζ)) ((R : ℂ) * ζ) :=
        (hf ((R : ℂ) * ζ)).hasDerivAt
      simpa [hg] using (hout.comp ζ hin).deriv
    -- `g` is analytic, omits `{0,1}`, is an immersion on the unit disc.
    have hg_an : ∀ ζ ∈ ball (0 : ℂ) 1, AnalyticAt ℂ g ζ := by
      intro ζ _
      have hfan : AnalyticAt ℂ f ((R : ℂ) * ζ) :=
        hf.differentiableOn.analyticAt (IsOpen.mem_nhds isOpen_univ (mem_univ _))
      have hlin : AnalyticAt ℂ (fun ζ : ℂ => (R : ℂ) * ζ) ζ :=
        (analyticAt_const).mul analyticAt_id
      exact hfan.comp hlin
    have hg0 : ∀ ζ ∈ ball (0 : ℂ) 1, g ζ ≠ 0 := fun ζ _ => h0 _
    have hg1 : ∀ ζ ∈ ball (0 : ℂ) 1, g ζ ≠ 1 := fun ζ _ => h1 _
    have hgd : ∀ ζ ∈ ball (0 : ℂ) 1, deriv g ζ ≠ 0 := by
      intro ζ _
      rw [hderiv ζ]
      exact mul_ne_zero (hfd _) hRne
    -- Apply the contraction at `ζ = 0`.
    have hz : ‖(0 : ℂ)‖ < 1 := by simp
    have hc := pullback_density_contraction_exp hg_an hg0 hg1 hgd hz
    rw [hderiv 0] at hc
    -- Simplify: `g 0 = f 0`, `‖f'(0)·R‖ = ‖f'(0)‖·R`, RHS `= 2`.
    have hgz0 : g (0 : ℂ) = f 0 := by simp [hg]
    have hnormR : ‖deriv f ((R : ℂ) * 0) * (R : ℂ)‖ = ‖deriv f 0‖ * R := by
      simp [Complex.norm_real, abs_of_pos hR]
    rw [hgz0, hnormR] at hc
    have : ultraDensityScaled (f 0) * (‖deriv f 0‖ * R) ≤ 2 := by
      simpa using hc
    calc R * A = ultraDensityScaled (f 0) * (‖deriv f 0‖ * R) := by rw [hA]; ring
      _ ≤ 2 := this
  -- Take `R = 3/A` to contradict `R·A ≤ 2`.
  have hbad := key (3 / A) (by positivity)
  rw [div_mul_cancel₀ 3 (ne_of_gt hApos)] at hbad
  linarith

/-- **Every entire function omitting two values has a critical point.** Immediate
from `false_of_entire_immersion_omitting_two`: if the derivative never vanished,
`f` would be an entire immersion omitting `{0,1}`, which is impossible. -/
theorem exists_deriv_eq_zero_of_entire_omitting_two
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (h0 : ∀ z, f z ≠ 0) (h1 : ∀ z, f z ≠ 1) :
    ∃ z, deriv f z = 0 := by
  by_contra hcon
  push_neg at hcon
  exact false_of_entire_immersion_omitting_two f hf h0 h1 hcon

end MLC.Quadratic
