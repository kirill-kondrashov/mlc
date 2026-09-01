import Mlc.Quadratic.Complex.Bottcher.ConformalLaplacian
import Mlc.Quadratic.Complex.Bottcher.UltrahyperbolicMetric
import Mlc.Quadratic.Complex.Bottcher.AhlforsSchwarz
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions

/-!
# Holomorphic pullback of the ultrahyperbolic metric (Schwarz–Pick)

This file completes the analytic heart of **step 4** of the Schottky route toward discharging
axiom A: pulling back the rescaled ultrahyperbolic metric `√(1/1000)·σ|dz|` of curvature `≤ -1`
on `ℂ \ {0,1}` (from `UltrahyperbolicMetric.lean`) via a holomorphic map `f : 𝔻 → ℂ \ {0,1}`,
and applying Ahlfors' generalized Schwarz lemma (`ahlfors_schwarz`) to obtain the Schwarz–Pick
density contraction.

## Main results

* `exp_two_pullback_le_laplacian` — the pulled-back log-density
  `u = log(√(1/1000)·σ) ∘ f + log‖f'‖` again satisfies the curvature-`≤ -1` inequality
  `exp(2u) ≤ Δu`, wherever `f` is holomorphic, `f z ∉ {0,1}`, and `f' z ≠ 0`.  The proof combines
  the conformal Laplacian chain rule (`laplacian_comp_analytic`), the harmonicity of `log‖f'‖`
  (Mathlib's `AnalyticAt.harmonicAt_log_norm`), and the source curvature bound
  (`exp_two_ultraLogDensityScaled_le_laplacian`).

* `pullback_density_contraction` — feeding the above into `ahlfors_schwarz`, on the unit disk
  `𝔻` a holomorphic `f : 𝔻 → ℂ \ {0,1}` with non-vanishing derivative satisfies
  `log(√(1/1000)·σ(f z)) + log‖f' z‖ ≤ log 2 − log(1 − ‖z‖²)`, i.e. the density form of the
  Schwarz–Pick lemma: the pulled-back metric is dominated by the Poincaré metric of `𝔻`.

The `f' z ≠ 0` hypothesis (holomorphic *immersion*) is genuine: at critical points the
`log‖f'‖` term degenerates.  Handling critical points of the eventual `crossTrack` maps is left
to the wiring step that consumes this contraction.
-/

namespace MLC.Quadratic

open Complex Metric
open scoped Laplacian

open InnerProductSpace in
/-- **Curvature `≤ -1` is preserved under holomorphic pullback.** With
`u = log(√(1/1000)·σ) ∘ f + log‖f'‖` (the pulled-back log-density), wherever `f` is holomorphic
at `z`, `f z ∉ {0, 1}`, and `f' z ≠ 0`, one has `exp(2·u z) ≤ Δu z`. -/
theorem exp_two_pullback_le_laplacian {f : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (h0 : f z ≠ 0) (h1 : f z ≠ 1) (hfd : deriv f z ≠ 0) :
    Real.exp (2 * (ultraLogDensityScaled (f z) + Real.log ‖deriv f z‖))
      ≤ Δ (fun w => ultraLogDensityScaled (f w) + Real.log ‖deriv f w‖) z := by
  have hfR : ContDiffAt ℝ 2 f z := (hf.contDiffAt).restrict_scalars ℝ
  have hg2 : ContDiffAt ℝ 2 (fun w => ultraLogDensityScaled (f w)) z :=
    (contDiffAt_ultraLogDensityScaled h0 h1).comp z hfR
  have harm : HarmonicAt (fun w => Real.log ‖deriv f w‖) z :=
    (hf.deriv).harmonicAt_log_norm hfd
  have hlogC2 : ContDiffAt ℝ 2 (fun w => Real.log ‖deriv f w‖) z := harm.1
  have hharm0 : Δ (fun w => Real.log ‖deriv f w‖) z = 0 := by
    have := harm.2.eq_of_nhds; simpa using this
  have hlap : Δ (fun w => ultraLogDensityScaled (f w) + Real.log ‖deriv f w‖) z
      = ‖deriv f z‖ ^ 2 * Δ ultraLogDensityScaled (f z) := by
    rw [show (fun w => ultraLogDensityScaled (f w) + Real.log ‖deriv f w‖)
          = (fun w => ultraLogDensityScaled (f w)) + (fun w => Real.log ‖deriv f w‖) from rfl,
      ContDiffAt.laplacian_add hg2 hlogC2, hharm0, add_zero,
      laplacian_comp_analytic hf (contDiffAt_ultraLogDensityScaled h0 h1)]
  have hnorm_pos : 0 < ‖deriv f z‖ := norm_pos_iff.2 hfd
  have hexp2 : Real.exp (2 * Real.log ‖deriv f z‖) = ‖deriv f z‖ ^ 2 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.exp_nat_mul, Real.exp_log hnorm_pos]
  have hu : Real.exp (2 * (ultraLogDensityScaled (f z) + Real.log ‖deriv f z‖))
      = Real.exp (2 * ultraLogDensityScaled (f z)) * ‖deriv f z‖ ^ 2 := by
    rw [mul_add, Real.exp_add, hexp2]
  rw [hlap, hu, mul_comm (‖deriv f z‖ ^ 2) (Δ ultraLogDensityScaled (f z))]
  exact mul_le_mul_of_nonneg_right (exp_two_ultraLogDensityScaled_le_laplacian h0 h1)
    (sq_nonneg _)

open InnerProductSpace in
/-- **Schwarz–Pick density contraction.** A holomorphic immersion `f : 𝔻 → ℂ \ {0,1}` (i.e.
`f` analytic, `f z ∉ {0,1}`, and `f' z ≠ 0` on the open unit disk) pulls the rescaled
ultrahyperbolic metric back to a metric dominated by the disk Poincaré metric:
`log(√(1/1000)·σ(f z)) + log‖f' z‖ ≤ log 2 − log(1 − ‖z‖²)` for all `‖z‖ < 1`. -/
theorem pullback_density_contraction {f : ℂ → ℂ}
    (hf : ∀ z ∈ ball (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h0 : ∀ z ∈ ball (0 : ℂ) 1, f z ≠ 0)
    (h1 : ∀ z ∈ ball (0 : ℂ) 1, f z ≠ 1)
    (hfd : ∀ z ∈ ball (0 : ℂ) 1, deriv f z ≠ 0)
    {z : ℂ} (hz : ‖z‖ < 1) :
    ultraLogDensityScaled (f z) + Real.log ‖deriv f z‖
      ≤ Real.log 2 - Real.log (1 - ‖z‖ ^ 2) := by
  refine ahlfors_schwarz
    (u := fun w => ultraLogDensityScaled (f w) + Real.log ‖deriv f w‖) ?_ ?_ hz
  · intro w hw
    have hfR : ContDiffAt ℝ 2 f w := ((hf w hw).contDiffAt).restrict_scalars ℝ
    exact ((contDiffAt_ultraLogDensityScaled (h0 w hw) (h1 w hw)).comp w hfR).add
      ((hf w hw).deriv.harmonicAt_log_norm (hfd w hw)).1
  · intro w hw
    exact exp_two_pullback_le_laplacian (hf w hw) (h0 w hw) (h1 w hw) (hfd w hw)

/-- The rescaled ultrahyperbolic density `√(1/1000)·σ = exp(ultraLogDensityScaled)` on
`ℂ \ {0,1}`. -/
noncomputable def ultraDensityScaled (w : ℂ) : ℝ := Real.exp (ultraLogDensityScaled w)

theorem ultraDensityScaled_pos (w : ℂ) : 0 < ultraDensityScaled w := Real.exp_pos _

/-- **Schwarz–Pick density contraction, metric form.** Exponentiating
`pullback_density_contraction`: a holomorphic immersion `f : 𝔻 → ℂ \ {0,1}` contracts the
rescaled ultrahyperbolic metric into the disk Poincaré metric,
`(√(1/1000)·σ)(f z) · ‖f' z‖ ≤ 2 / (1 − ‖z‖²)`, for all `‖z‖ < 1`.  The right-hand side is the
disk Poincaré density.  This is the pointwise (infinitesimal) contraction that the
Mañé–Sad–Sullivan continuity argument integrates along paths. -/
theorem pullback_density_contraction_exp {f : ℂ → ℂ}
    (hf : ∀ z ∈ ball (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h0 : ∀ z ∈ ball (0 : ℂ) 1, f z ≠ 0)
    (h1 : ∀ z ∈ ball (0 : ℂ) 1, f z ≠ 1)
    (hfd : ∀ z ∈ ball (0 : ℂ) 1, deriv f z ≠ 0)
    {z : ℂ} (hz : ‖z‖ < 1) :
    ultraDensityScaled (f z) * ‖deriv f z‖ ≤ 2 / (1 - ‖z‖ ^ 2) := by
  have hz2 : ‖z‖ ^ 2 < 1 := by nlinarith [norm_nonneg z]
  have hpos : (0 : ℝ) < 1 - ‖z‖ ^ 2 := by linarith
  have hfdz : deriv f z ≠ 0 := hfd z (by simpa [mem_ball_zero_iff] using hz)
  have hnpos : 0 < ‖deriv f z‖ := norm_pos_iff.2 hfdz
  have hmono := Real.exp_le_exp.2 (pullback_density_contraction hf h0 h1 hfd hz)
  rw [Real.exp_add, Real.exp_log hnpos, Real.exp_sub, Real.exp_log (by norm_num),
    Real.exp_log hpos] at hmono
  exact hmono

/-- **Uniform derivative bound from the Schwarz–Pick contraction.** If a holomorphic immersion
`f : 𝔻 → ℂ \ {0,1}` has image on which the rescaled density stays above `m > 0`, then its
derivative is controlled by the disk Poincaré density: `‖f' z‖ ≤ 2 / ((1 − ‖z‖²)·m)`.  This is
the local-Lipschitz estimate underlying equicontinuity of holomorphic motions: when the
normalized `crossTrack` trajectories stay in a fixed compact subset of `ℂ \ {0,1}`, their time
derivatives are uniformly bounded. -/
theorem deriv_norm_bound_of_density_lower {f : ℂ → ℂ} {m : ℝ}
    (hf : ∀ z ∈ ball (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h0 : ∀ z ∈ ball (0 : ℂ) 1, f z ≠ 0)
    (h1 : ∀ z ∈ ball (0 : ℂ) 1, f z ≠ 1)
    (hfd : ∀ z ∈ ball (0 : ℂ) 1, deriv f z ≠ 0)
    (hm0 : 0 < m) (hm : ∀ z ∈ ball (0 : ℂ) 1, m ≤ ultraDensityScaled (f z))
    {z : ℂ} (hz : ‖z‖ < 1) :
    ‖deriv f z‖ ≤ 2 / ((1 - ‖z‖ ^ 2) * m) := by
  have hzmem : z ∈ ball (0 : ℂ) 1 := by simpa [mem_ball_zero_iff] using hz
  have hz2 : ‖z‖ ^ 2 < 1 := by nlinarith [norm_nonneg z]
  have hpos : (0 : ℝ) < 1 - ‖z‖ ^ 2 := by linarith
  have hcontr := pullback_density_contraction_exp hf h0 h1 hfd hz
  have hmz : m ≤ ultraDensityScaled (f z) := hm z hzmem
  have hstep : m * ‖deriv f z‖ ≤ 2 / (1 - ‖z‖ ^ 2) :=
    le_trans (by nlinarith [norm_nonneg (deriv f z), hmz]) hcontr
  rw [div_mul_eq_div_div, le_div_iff₀ hm0, mul_comm]
  exact hstep

/-- **A positive density lower bound on any compact subset of `ℂ \ {0,1}`.** Since the rescaled
ultrahyperbolic density `ultraDensityScaled = exp ∘ ultraLogDensityScaled` is continuous and
strictly positive away from the punctures, it attains a positive minimum on every compact
`K ⊂ ℂ \ {0,1}`.  This supplies the density lower bound `m` demanded by
`deriv_norm_bound_of_density_lower` and `norm_deriv_crossTrack_le`: a holomorphic-motion trajectory
confined to a fixed compact `K` has uniformly bounded time derivative. -/
theorem exists_pos_lower_bound_ultraDensityScaled {K : Set ℂ}
    (hK : IsCompact K) (hKne : K.Nonempty)
    (hK0 : (0 : ℂ) ∉ K) (hK1 : (1 : ℂ) ∉ K) :
    ∃ m : ℝ, 0 < m ∧ ∀ w ∈ K, m ≤ ultraDensityScaled w := by
  have hcont : ContinuousOn ultraDensityScaled K := by
    intro w hw
    have h0 : w ≠ 0 := fun h => hK0 (h ▸ hw)
    have h1 : w ≠ 1 := fun h => hK1 (h ▸ hw)
    exact ((Real.continuous_exp.continuousAt).comp
      (contDiffAt_ultraLogDensityScaled (n := 2) h0 h1).continuousAt).continuousWithinAt
  obtain ⟨w₀, hw₀K, hmin⟩ := hK.exists_isMinOn hKne hcont
  exact ⟨ultraDensityScaled w₀, ultraDensityScaled_pos w₀, fun w hw => hmin hw⟩

end MLC.Quadratic
