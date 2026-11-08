import Mlc.Research.Programme
import Mlc.Quadratic.RealSlice

/-! Numerical nonvacuity is distinct from a new Mandelbrot parameter. -/

namespace MLC.Research

open Filter Topology

noncomputable section

/-- An exact numerical model with unbounded loss and moduli tending to zero. -/
def harmonicBudget : ReturnBudget where
  degree n := n + 1
  distortion _ := 1
  collar _ := 1
  attenuation _ := 0
  injection n := 1 / (n + 1)
  modulus n := 1 / n
  degree_pos n := by positivity
  distortion_ge_one _ := le_rfl
  collar_pos _ := zero_lt_one
  attenuation_nonneg _ := le_rfl
  initial_nonneg := by norm_num
  injection_ge _ := le_rfl
  step n := by simp

theorem harmonicBudget_controlled : harmonicBudget.LinearLossControl := by
  refine ⟨1, zero_lt_one, 1, zero_lt_one, ?_, ?_⟩
  · intro n; exact le_rfl
  · intro n; simp [ReturnBudget.loss, harmonicBudget]

theorem harmonicBudget_unbounded : UnboundedBudget harmonicBudget.cost :=
  harmonicBudget.unbounded_of_linearLossControl harmonicBudget_controlled

theorem harmonicBudget_modulus_tendsto_zero :
    Tendsto harmonicBudget.modulus atTop (𝓝 0) :=
  tendsto_one_div_atTop_nhds_zero_nat

/-- No eventual positive lower bound is required by the numerical criterion. -/
theorem harmonicBudget_no_eventual_positive_bound :
    ¬ ∃ δ > (0 : ℝ), ∀ᶠ n in atTop, δ ≤ harmonicBudget.modulus n := by
  rintro ⟨δ, hδ, hbound⟩
  have hle : δ ≤ (0 : ℝ) :=
    ge_of_tendsto harmonicBudget_modulus_tendsto_zero hbound
  exact (not_le_of_gt hδ) hle

/-- An empty admissibility predicate makes realization vacuous. -/
def emptyCandidate : CandidateSystem := ⟨fun _ _ => False⟩

theorem emptyCandidate_realization : emptyCandidate.Realization := by
  intro c hc b hfalse
  exact hfalse.elim

theorem emptyCandidate_not_eligible (c : ℂ) : ¬ emptyCandidate.Eligible c := by
  rintro ⟨b, hfalse, hb⟩
  exact hfalse

theorem neg_two_not_interior_mandelbrot :
    (-2 : ℂ) ∉ interior MLC.Quadratic.MandelbrotSet := by
  intro hi
  obtain ⟨ε, hε, hεM⟩ := Metric.mem_nhds_iff.mp
    (mem_interior_iff_mem_nhds.mp hi)
  have hz : (((-2 - ε / 2 : ℝ) : ℂ)) ∈ Metric.ball (-2 : ℂ) ε := by
    rw [show (-2 : ℂ) = ((-2 : ℝ) : ℂ) by norm_num,
      Metric.mem_ball, Complex.isometry_ofReal.dist_eq, Real.dist_eq]
    have heq : (-2 - ε / 2) - (-2) = -(ε / 2) := by ring
    rw [heq, abs_neg, abs_of_pos (half_pos hε)]
    exact half_lt_self hε
  have hreal := (MLC.Quadratic.RealSlice.ofReal_mem_mandelbrotSet_iff
    (-2 - ε / 2)).mp (hεM hz)
  linarith [hreal.1]

/-- A concrete counterexample to inferring global coverage from realization. -/
theorem emptyCandidate_not_coverage : ¬ emptyCandidate.Coverage := by
  intro h
  have hc : (-2 : ℂ) ∈ MLC.Quadratic.MandelbrotSet := by
    have := (MLC.Quadratic.RealSlice.ofReal_mem_mandelbrotSet_iff (-2)).mpr
      (by constructor <;> norm_num)
    exact_mod_cast this
  rcases h (-2) hc with hi | he
  · exact neg_two_not_interior_mandelbrot hi
  · exact emptyCandidate_not_eligible (-2) he

end
end MLC.Research
