import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Topology

namespace MLC.UniformGeometry

open scoped BigOperators

/-- Vertex displacement bounds pass to affine interpolation on a simplex. -/
theorem dist_affine_combinations_le {ι : Type*} [Fintype ι]
    (weights : ι → ℝ) (hweights : ∀ i, 0 ≤ weights i)
    (hsum : ∑ i, weights i = 1) (x y : ι → ℂ) (b : ℝ)
    (hvertices : ∀ i, dist (x i) (y i) ≤ b) :
    dist (∑ i, weights i • x i) (∑ i, weights i • y i) ≤ b := by
  calc
    dist (∑ i, weights i • x i) (∑ i, weights i • y i) =
        ‖∑ i, weights i • (x i - y i)‖ := by
      simp only [dist_eq_norm, smul_sub, Finset.sum_sub_distrib]
    _ ≤ ∑ i, ‖weights i • (x i - y i)‖ := norm_sum_le _ _
    _ = ∑ i, weights i * dist (x i) (y i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hweights i), dist_eq_norm]
    _ ≤ ∑ i, weights i * b := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (hvertices i) (hweights i)
    _ = b := by rw [← Finset.sum_mul, hsum, one_mul]

end MLC.UniformGeometry
