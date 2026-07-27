import Mlc.ParameterEscapeExhaustion
import Mathlib.Analysis.Complex.Polynomial.GaussLucas
import Mathlib.Analysis.Calculus.Deriv.Polynomial

open Set
open scoped Classical

namespace MLC.Quadratic
open Polynomial

/-- The parameter polynomial whose value at `c` is the critical orbit iterate
`orbit c 0 (n + 1)` for the quadratic family `z ↦ z^2 + c`. -/
noncomputable def ParameterOrbitPolynomial : ℕ → ℂ[X]
  | 0 => Polynomial.X
  | n + 1 => (ParameterOrbitPolynomial n) ^ 2 + Polynomial.X

lemma parameterOrbitPolynomial_natDegree :
    ∀ n : ℕ, (ParameterOrbitPolynomial n).natDegree = 2 ^ n
  | 0 => by simp [ParameterOrbitPolynomial]
  | n + 1 => by
      rw [ParameterOrbitPolynomial, natDegree_add_eq_left_of_natDegree_lt]
      · rw [Polynomial.natDegree_pow, parameterOrbitPolynomial_natDegree]
        ring
      · rw [natDegree_X, Polynomial.natDegree_pow, parameterOrbitPolynomial_natDegree]
        have hpowpos : 0 < 2 ^ n := pow_pos (by norm_num) n
        linarith

lemma parameterOrbitPolynomial_nonzero (n : ℕ) : ParameterOrbitPolynomial n ≠ 0 := by
  intro hz
  have hnat := congrArg Polynomial.natDegree hz
  simp [parameterOrbitPolynomial_natDegree] at hnat

lemma parameterOrbitPolynomial_eval (n : ℕ) (c : ℂ) :
    (ParameterOrbitPolynomial n).eval c = orbit c 0 (n + 1) := by
  induction n with
  | zero => simp [ParameterOrbitPolynomial, orbit, fc]
  | succ n ih =>
      simp [ParameterOrbitPolynomial, ih, orbit_succ, fc, pow_two]

lemma parameterOrbitPolynomial_rootSet_subset_mandelbrotSet (n : ℕ) :
    (ParameterOrbitPolynomial n).rootSet ℂ ⊆ MandelbrotSet := by
  intro c hc
  rw [Polynomial.mem_rootSet] at hc
  exact mandelbrot_of_orbit_zero c n (by simpa [parameterOrbitPolynomial_eval] using hc.2)

lemma parameterOrbitPolynomial_rootSet_subset_closedBall_two (n : ℕ) :
    (ParameterOrbitPolynomial n).rootSet ℂ ⊆ Metric.closedBall (0 : ℂ) 2 := by
  exact (parameterOrbitPolynomial_rootSet_subset_mandelbrotSet n).trans
    mandelbrotSet_subset_closedBall_two

theorem parameterOrbitPolynomial_derivative_root_norm_le_two
    (n : ℕ) {c : ℂ}
    (h : (ParameterOrbitPolynomial n).derivative.eval c = 0) :
    ‖c‖ ≤ 2 := by
  have hp : ParameterOrbitPolynomial n ≠ 0 := parameterOrbitPolynomial_nonzero n
  have hdeg : 0 < (ParameterOrbitPolynomial n).degree := by
    rw [degree_eq_natDegree hp, parameterOrbitPolynomial_natDegree]
    exact Nat.cast_pos.mpr (pow_pos (by norm_num) _)
  have hderiv_ne : (ParameterOrbitPolynomial n).derivative ≠ 0 := by
    intro hzero
    have hnat : (ParameterOrbitPolynomial n).natDegree = 0 :=
      natDegree_eq_zero_of_derivative_eq_zero hzero
    rw [parameterOrbitPolynomial_natDegree] at hnat
    exact pow_ne_zero _ (by norm_num) hnat
  have hcroot : c ∈ (ParameterOrbitPolynomial n).derivative.rootSet ℂ := by
    rw [Polynomial.mem_rootSet]
    constructor
    · exact hderiv_ne
    · simpa using h
  have hsubset := Polynomial.rootSet_derivative_subset_convexHull_rootSet
    (P := ParameterOrbitPolynomial n) hdeg
  have hconv : convexHull ℝ ((ParameterOrbitPolynomial n).rootSet ℂ) ⊆
      Metric.closedBall (0 : ℂ) 2 := by
    exact convexHull_min (parameterOrbitPolynomial_rootSet_subset_closedBall_two n)
      (convex_closedBall (0 : ℂ) 2)
  have hball : c ∈ Metric.closedBall (0 : ℂ) 2 := hconv (hsubset hcroot)
  simpa [Metric.mem_closedBall, dist_eq_norm] using hball

end MLC.Quadratic
