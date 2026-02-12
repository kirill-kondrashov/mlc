import Mlc.Quadratic.Complex.InverseBranch
import Mlc.Quadratic.Complex.Bottcher.BottcherAxioms
import Mlc.Quadratic.Complex.Bottcher.BottcherOnMDefs
import Mlc.Quadratic.Complex.Bottcher.BottcherCpowSlit

namespace MLC
namespace Quadratic

open Topology Set

/-- The exterior of the unit disk. -/
def exterior : Set ℂ := {w | 1 < ‖w‖}

/-!
Square-root branches on the exterior. These are *hypotheses* used to
explain what additional structure would be required to build inverse
branches for `quadratic_map` on the basin.
-/

structure SquareRootBranch (S : Set ℂ) where
  (toFun : ℂ → ℂ)
  (mapsTo : MapsTo toFun S S)
  (sq : ∀ z ∈ S, (toFun z) ^ 2 = z)

/-- A right-inverse branch of squaring on `S`. -/
def SquareRootRightInverseOn (S : Set ℂ) (sqrt : ℂ → ℂ) : Prop :=
  ∀ w ∈ S, sqrt (w ^ 2) = w

def exteriorRight : Set ℂ := {w | 1 < ‖w‖ ∧ 0 < w.re}
def slitPlaneRight : Set ℂ := {w | w ∈ Complex.slitPlane ∧ 0 < w.re}
def slitPlaneRotRight (θ : ℝ) : Set ℂ :=
  {w | w * Complex.exp (-Complex.I * θ / 2) ∈ slitPlaneRight}

lemma sqrt_right_inverse_on_exteriorRight :
    SquareRootRightInverseOn exteriorRight (fun z => z ^ ((1 : ℂ) / 2)) := by
  intro w hw
  have hre : 0 < w.re := hw.2
  have harg : |Complex.arg w| < Real.pi / 2 :=
    MLC.abs_arg_lt_pi_div_two_of_re_pos hre
  have h1 : -Real.pi < (Complex.log w * (2 : ℂ)).im := by
    have hlog : (Complex.log w * (2 : ℂ)).im = 2 * Complex.arg w := by
      simp [Complex.mul_im, Complex.log_im, mul_comm, mul_assoc]
    have hlt : -Real.pi < 2 * Complex.arg w := by
      have h' := (abs_lt.1 harg)
      linarith
    simpa [hlog] using hlt
  have h2 : (Complex.log w * (2 : ℂ)).im ≤ Real.pi := by
    have hlog : (Complex.log w * (2 : ℂ)).im = 2 * Complex.arg w := by
      simp [Complex.mul_im, Complex.log_im, mul_comm, mul_assoc]
    have hle : 2 * Complex.arg w ≤ Real.pi := by
      have h' := (abs_lt.1 harg)
      linarith
    exact (by simpa [hlog] using hle)
  have hmul := Complex.cpow_mul (x := w) (y := (2 : ℂ)) (z := ((1 : ℂ) / 2)) h1 h2
  calc
    (w ^ 2) ^ ((1 : ℂ) / 2) = w ^ ((2 : ℂ) * ((1 : ℂ) / 2)) := by
      simpa [mul_comm] using hmul.symm
    _ = w ^ (1 : ℂ) := by ring_nf
    _ = w := by simp

lemma sqrt_right_inverse_on_slitPlaneRight :
    SquareRootRightInverseOn slitPlaneRight (fun z => z ^ ((1 : ℂ) / 2)) := by
  intro w hw
  have hre : 0 < w.re := hw.2
  have harg : |Complex.arg w| < Real.pi / 2 :=
    MLC.abs_arg_lt_pi_div_two_of_re_pos hre
  have h1 : -Real.pi < (Complex.log w * (2 : ℂ)).im := by
    have hlog : (Complex.log w * (2 : ℂ)).im = 2 * Complex.arg w := by
      simp [Complex.mul_im, Complex.log_im, mul_comm, mul_assoc]
    have hlt : -Real.pi < 2 * Complex.arg w := by
      have h' := (abs_lt.1 harg)
      linarith
    simpa [hlog] using hlt
  have h2 : (Complex.log w * (2 : ℂ)).im ≤ Real.pi := by
    have hlog : (Complex.log w * (2 : ℂ)).im = 2 * Complex.arg w := by
      simp [Complex.mul_im, Complex.log_im, mul_comm, mul_assoc]
    have hle : 2 * Complex.arg w ≤ Real.pi := by
      have h' := (abs_lt.1 harg)
      linarith
    exact (by simpa [hlog] using hle)
  have hmul := Complex.cpow_mul (x := w) (y := (2 : ℂ)) (z := ((1 : ℂ) / 2)) h1 h2
  calc
    (w ^ 2) ^ ((1 : ℂ) / 2) = w ^ ((2 : ℂ) * ((1 : ℂ) / 2)) := by
      simpa [mul_comm] using hmul.symm
    _ = w ^ (1 : ℂ) := by ring_nf
    _ = w := by simp

lemma sqrt_right_inverse_on_slitPlaneRotRight (θ : ℝ) :
    SquareRootRightInverseOn (slitPlaneRotRight θ)
      (fun z =>
        (z * Complex.exp (-Complex.I * θ)) ^ ((1 : ℂ) / 2) *
          Complex.exp (Complex.I * θ / 2)) := by
  intro w hw
  have hw' : w * Complex.exp (-Complex.I * θ / 2) ∈ slitPlaneRight := hw
  have hexp : (Complex.exp (-Complex.I * θ / 2)) ^ 2 =
      Complex.exp (-Complex.I * θ) := by
    have h := (Complex.exp_nat_mul (-Complex.I * θ / 2) 2).symm
    -- `exp (2 * x) = exp x ^ 2`
    -- rewrite `(-I*θ/2) * 2` as `-I*θ`
    simpa [mul_comm, mul_left_comm, mul_assoc, two_mul, mul_add, add_mul, mul_div_assoc] using h
  have hsq :
      w ^ 2 * Complex.exp (-Complex.I * θ) =
        (w * Complex.exp (-Complex.I * θ / 2)) ^ 2 := by
    calc
      w ^ 2 * Complex.exp (-Complex.I * θ)
          = w ^ 2 * (Complex.exp (-Complex.I * θ / 2)) ^ 2 := by
              rw [hexp]
      _ = (w * Complex.exp (-Complex.I * θ / 2)) ^ 2 := by
            simp [pow_two, mul_assoc, mul_comm, mul_left_comm]
  have hright :=
    sqrt_right_inverse_on_slitPlaneRight (w := w * Complex.exp (-Complex.I * θ / 2)) hw'
  have hright' :
      ((w * Complex.exp (-Complex.I * θ / 2)) ^ 2) ^ ((2 : ℂ)⁻¹) =
        w * Complex.exp (-Complex.I * θ / 2) := by
    simpa [div_eq_mul_inv] using hright
  calc
    (w ^ 2 * Complex.exp (-Complex.I * θ)) ^ ((1 : ℂ) / 2) *
        Complex.exp (Complex.I * θ / 2)
        = (w ^ 2 * Complex.exp (-Complex.I * θ)) ^ ((2 : ℂ)⁻¹) *
            Complex.exp (Complex.I * θ / 2) := by
              simp [div_eq_mul_inv]
    _ = ((w * Complex.exp (-Complex.I * θ / 2)) ^ 2) ^ ((2 : ℂ)⁻¹) *
          Complex.exp (Complex.I * θ / 2) := by
            rw [hsq]
    _ = w * Complex.exp (-Complex.I * θ / 2) * Complex.exp (Complex.I * θ / 2) := by
          have h := congrArg (fun t => t * Complex.exp (Complex.I * θ / 2)) hright'
          simpa using h
    _ = w := by
      have hmul :
          Complex.exp (-Complex.I * θ / 2) * Complex.exp (Complex.I * θ / 2) = 1 := by
        rw [← Complex.exp_add]
        ring_nf
        simp
      calc
        w * Complex.exp (-Complex.I * θ / 2) * Complex.exp (Complex.I * θ / 2)
            = w * (Complex.exp (-Complex.I * θ / 2) * Complex.exp (Complex.I * θ / 2)) := by
                ring
        _ = w * 1 := by rw [hmul]
        _ = w := by simp

lemma no_square_root_right_inverse_on_exterior :
    ¬ ∃ sqrt : ℂ → ℂ, SquareRootRightInverseOn exterior sqrt := by
  intro h
  rcases h with ⟨sqrt, hsqrt⟩
  have hpos : (2 : ℂ) ∈ exterior := by
    show (1 : ℝ) < ‖(2 : ℂ)‖
    simpa using (by norm_num : (1 : ℝ) < (2 : ℝ))
  have hneg : (-2 : ℂ) ∈ exterior := by
    show (1 : ℝ) < ‖(-2 : ℂ)‖
    simpa using (by norm_num : (1 : ℝ) < (2 : ℝ))
  have h1 : sqrt ((2 : ℂ) ^ 2) = (2 : ℂ) := hsqrt (2 : ℂ) hpos
  have h2 : sqrt ((-2 : ℂ) ^ 2) = (-2 : ℂ) := hsqrt (-2 : ℂ) hneg
  have hsq : ((2 : ℂ) ^ 2) = ((-2 : ℂ) ^ 2) := by
    simp
  have hsq' : ((-2 : ℂ) ^ 2) = ((2 : ℂ) ^ 2) := by
    simpa using hsq.symm
  have h2' : sqrt ((2 : ℂ) ^ 2) = (-2 : ℂ) := by
    simpa [hsq'] using h2
  have hcontra : (2 : ℂ) = (-2 : ℂ) := by
    exact h1.symm.trans h2'
  have : (2 : ℂ) ≠ (-2 : ℂ) := by norm_num
  exact this hcontra

/-!
Inverse-branch roadmap for the quadratic map on the basin of infinity.

This file is deliberately hypothesis-driven: it introduces the exact
properties needed to remove `quadratic_map_iter_eq_imp_eq` without adding
axioms. The proofs here are simple implications from those hypotheses.
-/

/-- Hypothesis: `quadratic_map` admits a left inverse on the basin. -/
def QuadraticMapLeftInverseOnBasin (c : ℂ) : Prop :=
  HasLeftInverseOn (quadratic_map c) Set.univ (basin_of_infinity c)

/-- Hypothesis: all iterates of `quadratic_map` admit left inverses on the basin. -/
def QuadraticMapIterLeftInverseOnBasin (c : ℂ) : Prop :=
  ∀ n : ℕ, HasLeftInverseOn ((quadratic_map c)^[n]) Set.univ (basin_of_infinity c)

/-- A left inverse for an iterate yields injectivity on the basin. -/
lemma quadratic_map_iter_inj_on_basin_of_left_inverse
    (c : ℂ) (n : ℕ)
    (h_left : HasLeftInverseOn ((quadratic_map c)^[n]) Set.univ (basin_of_infinity c)) :
    Set.InjOn ((quadratic_map c)^[n]) (basin_of_infinity c) := by
  simpa using (injOn_of_hasLeftInverseOn h_left)

/-- If every iterate is injective on the basin, equal iterates imply equality. -/
lemma quadratic_map_iter_eq_imp_eq_of_all_iter_inj
    (c : ℂ)
    (h_inj : ∀ n, Set.InjOn ((quadratic_map c)^[n]) (basin_of_infinity c)) :
    ∀ z w, z ∈ basin_of_infinity c → w ∈ basin_of_infinity c →
      (∃ n, (quadratic_map c)^[n] z = (quadratic_map c)^[n] w) → z = w := by
  intro z w hz hw hiter
  rcases hiter with ⟨n, h⟩
  exact h_inj n hz hw h

/-- Package the desired replacement for `quadratic_map_iter_eq_imp_eq`. -/
lemma quadratic_map_iter_eq_imp_eq_of_iter_left_inverse
    (c : ℂ)
    (h_left : QuadraticMapIterLeftInverseOnBasin c) :
    ∀ z w, z ∈ basin_of_infinity c → w ∈ basin_of_infinity c →
      (∃ n, (quadratic_map c)^[n] z = (quadratic_map c)^[n] w) → z = w := by
  intro z w hz hw hiter
  have h_inj : ∀ n, Set.InjOn ((quadratic_map c)^[n]) (basin_of_infinity c) := by
    intro n
    exact quadratic_map_iter_inj_on_basin_of_left_inverse c n (h_left n)
  exact quadratic_map_iter_eq_imp_eq_of_all_iter_inj c h_inj z w hz hw hiter

/-!
If one had a *right-inverse* square root branch on the exterior and a
left inverse for `bottcher_map` on the basin, one could build a left
inverse for `quadratic_map` on the basin. This is recorded as a
hypothesis-driven lemma to make the remaining gap explicit.
-/

lemma quadratic_map_left_inverse_on_basin_of_sqrt_branch
    (c : ℂ)
    (sqrt : ℂ → ℂ)
    (h_sqrt : SquareRootRightInverseOn exterior sqrt)
    (h_conj : ∀ z, z ∈ basin_of_infinity c →
      bottcher_map c (quadratic_map c z) = (bottcher_map c z) ^ 2)
    (h_left_bottcher : ∀ z, z ∈ basin_of_infinity c →
      external_ray_map c (bottcher_map c z) = z)
    (h_norm : ∀ z, z ∈ basin_of_infinity c → 1 < ‖bottcher_map c z‖)
    (h_maps : MapsTo (fun z => external_ray_map c (sqrt (bottcher_map c z)))
      (basin_of_infinity c) (basin_of_infinity c)) :
    HasLeftInverseOn (quadratic_map c) (basin_of_infinity c) (basin_of_infinity c) := by
  refine ⟨fun z => external_ray_map c (sqrt (bottcher_map c z)), ?_, ?_⟩
  · intro z hz
    have hz' : 1 < ‖bottcher_map c z‖ := h_norm z hz
    have hz_ext : bottcher_map c z ∈ exterior := hz'
    have hsq : sqrt ((bottcher_map c z) ^ 2) = bottcher_map c z :=
      h_sqrt (bottcher_map c z) hz_ext
    have hconj := h_conj z hz
    calc
      external_ray_map c (sqrt (bottcher_map c (quadratic_map c z)))
          = external_ray_map c (sqrt ((bottcher_map c z) ^ 2)) := by
              simp [hconj]
      _ = external_ray_map c (bottcher_map c z) := by simp [hsq]
      _ = z := h_left_bottcher z hz
  · intro y hy
    exact h_maps hy

lemma quadratic_map_left_inverse_on_basin_of_sqrt_branch_slitPlaneRight
    (c : ℂ)
    (sqrt : ℂ → ℂ)
    (h_sqrt : SquareRootRightInverseOn slitPlaneRight sqrt)
    (h_conj : ∀ z, z ∈ basin_of_infinity c →
      bottcher_map c (quadratic_map c z) = (bottcher_map c z) ^ 2)
    (h_left_bottcher : ∀ z, z ∈ basin_of_infinity c →
      external_ray_map c (bottcher_map c z) = z)
    (h_mem : ∀ z, z ∈ basin_of_infinity c → bottcher_map c z ∈ slitPlaneRight)
    (h_maps : MapsTo (fun z => external_ray_map c (sqrt (bottcher_map c z)))
      (basin_of_infinity c) (basin_of_infinity c)) :
    HasLeftInverseOn (quadratic_map c) (basin_of_infinity c) (basin_of_infinity c) := by
  refine ⟨fun z => external_ray_map c (sqrt (bottcher_map c z)), ?_, ?_⟩
  · intro z hz
    have hz_mem : bottcher_map c z ∈ slitPlaneRight := h_mem z hz
    have hsq : sqrt ((bottcher_map c z) ^ 2) = bottcher_map c z :=
      h_sqrt (bottcher_map c z) hz_mem
    have hconj := h_conj z hz
    calc
      external_ray_map c (sqrt (bottcher_map c (quadratic_map c z)))
          = external_ray_map c (sqrt ((bottcher_map c z) ^ 2)) := by
              simp [hconj]
      _ = external_ray_map c (bottcher_map c z) := by simp [hsq]
      _ = z := h_left_bottcher z hz
  · intro y hy
    exact h_maps hy

lemma quadratic_map_left_inverse_on_basin_of_sqrt_branch_slitPlaneRotRight
    (c : ℂ) (θ : ℝ)
    (sqrt : ℂ → ℂ)
    (h_sqrt : SquareRootRightInverseOn (slitPlaneRotRight θ) sqrt)
    (h_conj : ∀ z, z ∈ basin_of_infinity c →
      bottcher_map c (quadratic_map c z) = (bottcher_map c z) ^ 2)
    (h_left_bottcher : ∀ z, z ∈ basin_of_infinity c →
      external_ray_map c (bottcher_map c z) = z)
    (h_mem : ∀ z, z ∈ basin_of_infinity c → bottcher_map c z ∈ slitPlaneRotRight θ)
    (h_maps : MapsTo (fun z => external_ray_map c (sqrt (bottcher_map c z)))
      (basin_of_infinity c) (basin_of_infinity c)) :
    HasLeftInverseOn (quadratic_map c) (basin_of_infinity c) (basin_of_infinity c) := by
  refine ⟨fun z => external_ray_map c (sqrt (bottcher_map c z)), ?_, ?_⟩
  · intro z hz
    have hz_mem : bottcher_map c z ∈ slitPlaneRotRight θ := h_mem z hz
    have hsq : sqrt ((bottcher_map c z) ^ 2) = bottcher_map c z :=
      h_sqrt (bottcher_map c z) hz_mem
    have hconj := h_conj z hz
    calc
      external_ray_map c (sqrt (bottcher_map c (quadratic_map c z)))
          = external_ray_map c (sqrt ((bottcher_map c z) ^ 2)) := by
              simp [hconj]
      _ = external_ray_map c (bottcher_map c z) := by simp [hsq]
      _ = z := h_left_bottcher z hz
  · intro y hy
    exact h_maps hy

end Quadratic
end MLC
