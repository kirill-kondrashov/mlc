import Mlc.Quadratic.Complex.InverseBranch
import Mlc.Quadratic.Complex.Bottcher.BottcherAxioms
import Mlc.Quadratic.Complex.Bottcher.BottcherOnMDefs

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

end Quadratic
end MLC
