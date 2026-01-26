import Mlc.Quadratic.Complex.PuzzleBoundaryMotion
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord

namespace MLC

open Quadratic Complex Topology Set Filter Metric

namespace Quadratic

/-- The Böttcher map `φ_c` conjugates `f_c(z) = z^2 + c` to `z^2` near infinity. -/
noncomputable def bottcher_map (c : ℂ) (z : ℂ) : ℂ :=
  -- Ideally: lim_{n \to \infty} (f_c^n(z))^(1/2^n)
  -- For now, we postulate its existence and properties.
  sorry

/-- The domain where the Böttcher map is defined (basin of infinity). -/
def basin_of_infinity (c : ℂ) : Set ℂ :=
  {z | ¬ MLC.Quadratic.boundedOrbit c z}

theorem basin_eq_compl_K (c : ℂ) : basin_of_infinity c = (MLC.Quadratic.K c)ᶜ := by
  ext z
  simp [basin_of_infinity, MLC.Quadratic.K, MLC.Quadratic.boundedOrbit]

/-- The Böttcher map is a conformal isomorphism from the basin to the exterior of the disk. -/
axiom bottcher_map_image (c : ℂ) :
    bottcher_map c '' basin_of_infinity c = {w | 1 < ‖w‖}

/-- The Böttcher map satisfies |φ_c(z)| = exp(G_c(z)). -/
axiom norm_bottcher_eq_exp_green (c : ℂ) (z : ℂ) :
    ‖bottcher_map c z‖ = Real.exp (MLC.Quadratic.green_function c z)

/-- The Böttcher map is continuous on the basin. -/
axiom bottcher_continuous_on (c : ℂ) :
    ContinuousOn (bottcher_map c) (basin_of_infinity c)

/-- The inverse of the Böttcher map exists (ray map). -/
noncomputable def external_ray_map (c : ℂ) (w : ℂ) : ℂ :=
  if 1 < ‖w‖ then
    -- inverse of bottcher_map
    sorry
  else 0

/-- The ray map is the inverse of the Böttcher map. -/
axiom bottcher_right_inv (c : ℂ) (w : ℂ) (hw : 1 < ‖w‖) :
    bottcher_map c (external_ray_map c w) = w

axiom bottcher_left_inv (c : ℂ) (z : ℂ) (hz : z ∈ basin_of_infinity c) :
    external_ray_map c (bottcher_map c z) = z

/-- The ray map is continuous on the exterior of the disk. -/
axiom ray_map_continuous_on (c : ℂ) :
    ContinuousOn (external_ray_map c) {w | 1 < ‖w‖}

end Quadratic

open Quadratic

/--
Every point in the Green sublevel set `S` is path-connected to `K_c` within `S`.
-/
lemma green_sublevel_joined_to_Kc (c : ℂ) (n : ℕ) :
    let S := MLC.Quadratic.GreenSublevel c n
    let K := MLC.Quadratic.K c
    ∀ z ∈ S, ∃ w ∈ K, JoinedIn S z w := by
  intro S K z hz
  have hK_sub_S : K ⊆ S := by
    intro w hw
    simp only [S, MLC.Quadratic.GreenSublevel, mem_setOf_eq]
    have hGw : MLC.Quadratic.green_function c w = 0 :=
      (MLC.Quadratic.green_function_eq_zero_iff_mem_K c w).2 hw
    rw [hGw]
    positivity

  by_cases h_in_K : z ∈ K
  · use z
    exact ⟨h_in_K, JoinedIn.refl (hK_sub_S h_in_K)⟩

  -- If z ∉ K, we use Böttcher coordinates.
  have h_basin : z ∈ basin_of_infinity c := by
    rw [basin_eq_compl_K]
    exact h_in_K

  -- Let w = φ_c(z). Then |w| = exp(G_c(z)).
  let w := bottcher_map c z
  have hw_norm : ‖w‖ = Real.exp (green_function c z) := norm_bottcher_eq_exp_green c z
  
  -- Since z ∈ S, G_c(z) < (1/2)^n. So 1 < |w| < exp((1/2)^n).
  have h_norm_lt : ‖w‖ < Real.exp ((1 / 2) ^ n) := by
    rw [hw_norm]
    apply Real.exp_lt_exp.mpr
    simp only [S, MLC.Quadratic.GreenSublevel, mem_setOf_eq] at hz
    exact hz
  
  have h_norm_gt : 1 < ‖w‖ := by
    rw [hw_norm]
    apply Real.one_lt_exp_iff.mpr
    rw [← green_function_eq_zero_iff_mem_K c z] at h_in_K
    exact lt_of_le_of_ne (green_function_nonneg c z) (Ne.symm h_in_K)

  -- Define a path in the w-plane: radial segment from w towards the circle.
  sorry

end MLC