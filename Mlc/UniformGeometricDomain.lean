import Mlc.CategoricalMandelbrot
import Mathlib.Analysis.Convex.Topology

namespace MLC.UniformGeometry

open Set Metric

/-- The fixed source square for rational piecewise-affine approximations. -/
def parameterSquare : Set ℂ :=
  {z | (-2 : ℝ) ≤ z.re ∧ z.re ≤ 2 ∧ -2 ≤ z.im ∧ z.im ≤ 2}

theorem isClosed_parameterSquare : IsClosed parameterSquare :=
  (isClosed_le continuous_const Complex.continuous_re).inter
    ((isClosed_le Complex.continuous_re continuous_const).inter
      ((isClosed_le continuous_const Complex.continuous_im).inter
        (isClosed_le Complex.continuous_im continuous_const)))

theorem norm_le_four_of_mem_parameterSquare {z : ℂ}
    (hz : z ∈ parameterSquare) : ‖z‖ ≤ (4 : ℝ) := by
  have hre : |z.re| ≤ (2 : ℝ) := abs_le.mpr ⟨hz.1, hz.2.1⟩
  have him : |z.im| ≤ (2 : ℝ) := abs_le.mpr ⟨hz.2.2.1, hz.2.2.2⟩
  exact (Complex.norm_le_abs_re_add_abs_im z).trans (by linarith)

theorem isCompact_parameterSquare : IsCompact parameterSquare := by
  apply (isCompact_closedBall (0 : ℂ) 4).of_isClosed_subset isClosed_parameterSquare
  intro z hz
  simpa only [mem_closedBall, dist_zero_right] using
    norm_le_four_of_mem_parameterSquare hz

theorem convex_parameterSquare : Convex ℝ parameterSquare := by
  intro x hx y hy a b ha hb hab
  simp only [parameterSquare, mem_setOf_eq, Complex.add_re, Complex.smul_re,
    Complex.add_im, Complex.smul_im, smul_eq_mul]
  refine ⟨?_, ?_, ?_, ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_left hx.1 ha,
      mul_le_mul_of_nonneg_left hy.1 hb]
  · nlinarith [mul_le_mul_of_nonneg_left hx.2.1 ha,
      mul_le_mul_of_nonneg_left hy.2.1 hb]
  · nlinarith [mul_le_mul_of_nonneg_left hx.2.2.1 ha,
      mul_le_mul_of_nonneg_left hy.2.2.1 hb]
  · nlinarith [mul_le_mul_of_nonneg_left hx.2.2.2 ha,
      mul_le_mul_of_nonneg_left hy.2.2.2 hb]

theorem outerOrbitSet_subset_parameterSquare (n : ℕ) :
    MLC.Categorical.Mandelbrot.outerOrbitSet n ⊆ parameterSquare := by
  intro z hz
  have hre := abs_le.mp ((Complex.abs_re_le_norm z).trans hz.1)
  have him := abs_le.mp ((Complex.abs_im_le_norm z).trans hz.1)
  exact ⟨hre.1, hre.2, him.1, him.2⟩

theorem mandelbrot_subset_parameterSquare :
    MLC.Quadratic.MandelbrotSet ⊆ parameterSquare :=
  (MLC.Categorical.Mandelbrot.set_subset_outerOrbitSet 0).trans
    (outerOrbitSet_subset_parameterSquare 0)

theorem norm_le_three_of_mem_parameterSquare {z : ℂ}
    (hz : z ∈ parameterSquare) : ‖z‖ ≤ (3 : ℝ) := by
  have hre : z.re ^ 2 ≤ (2 : ℝ) ^ 2 :=
    sq_le_sq.mpr (by simpa using (abs_le.mpr ⟨hz.1, hz.2.1⟩))
  have him : z.im ^ 2 ≤ (2 : ℝ) ^ 2 :=
    sq_le_sq.mpr (by simpa using (abs_le.mpr ⟨hz.2.2.1, hz.2.2.2⟩))
  have hsq : ‖z‖ ^ 2 ≤ (8 : ℝ) := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    nlinarith
  nlinarith [norm_nonneg z]

/-- The identity map satisfies the initial stage's outer-proximity bound. -/
theorem parameterSquare_near_outer_zero {z : ℂ} (hz : z ∈ parameterSquare) :
    ∃ w ∈ MLC.Categorical.Mandelbrot.outerOrbitSet 0, dist z w ≤ (1 : ℝ) := by
  let w : ℂ := (2 / 3 : ℝ) • z
  have hnorm := norm_le_three_of_mem_parameterSquare hz
  refine ⟨w, ⟨?_, ?_⟩, ?_⟩
  · calc
      ‖w‖ = (2 / 3 : ℝ) * ‖z‖ := by
        change ‖(2 / 3 : ℝ) • z‖ = (2 / 3 : ℝ) * ‖z‖
        rw [norm_smul]
        norm_num
      _ ≤ 2 := by linarith
  · intro k hk
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
    subst k
    change ‖(0 : ℂ)‖ ≤ (2 : ℝ)
    norm_num
  · calc
      dist z w = ‖(1 - 2 / 3 : ℝ) • z‖ := by
        simp only [dist_eq_norm, sub_smul, one_smul, w]
      _ = (1 / 3 : ℝ) * ‖z‖ := by
        rw [norm_smul]
        norm_num
      _ ≤ 1 := by linarith

end MLC.UniformGeometry
