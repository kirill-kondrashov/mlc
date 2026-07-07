import Mlc.Quadratic.Complex.Bottcher.BottcherAxioms
import Mathlib.Topology.Connected.PathConnected

namespace MLC

open Quadratic Complex Topology Set Filter Metric

namespace Quadratic
end Quadratic

open Quadratic

/-- K is contained in the Green sublevel set. -/
lemma K_subset_green_sublevel (c : ℂ) (n : ℕ) : 
    MLC.Quadratic.K c ⊆ MLC.Quadratic.GreenSublevel c n := by
  intro w hw
  simp only [MLC.Quadratic.GreenSublevel, mem_setOf_eq]
  have hGw : MLC.Quadratic.green_function c w = 0 :=
    (MLC.Quadratic.green_function_eq_zero_iff_mem_K c w).2 hw
  rw [hGw]
  positivity

/-- If z is not in K, it is in the basin of infinity. -/
lemma z_in_basin_of_not_mem_K (c : ℂ) (z : ℂ) (h : z ∉ MLC.Quadratic.K c) :
    z ∈ Quadratic.basin_of_infinity c := by
  rw [Quadratic.basin_eq_compl_K]
  exact h

/-- Bounds on the Böttcher coordinate norm for points in the sublevel set but not in K. -/
lemma bottcher_norm_of_mem_sublevel (c : ℂ) (n : ℕ) (z : ℂ) 
    (hz : z ∈ MLC.Quadratic.GreenSublevel c n) (hK : z ∉ MLC.Quadratic.K c) :
    let w := proxy_bottcher_map c z
    1 < ‖w‖ ∧ ‖w‖ < Real.exp ((1 / 2) ^ n) := by
  intro w
  have hw_norm : ‖w‖ = Real.exp (green_function c z) := norm_bottcher_eq_exp_green c z
  constructor
  · rw [hw_norm]
    apply Real.one_lt_exp_iff.mpr
    rw [← green_function_eq_zero_iff_mem_K c z] at hK
    exact lt_of_le_of_ne (green_function_nonneg c z) (Ne.symm hK)
  · rw [hw_norm]
    apply Real.exp_lt_exp.mpr
    simp only [MLC.Quadratic.GreenSublevel, mem_setOf_eq] at hz
    exact hz

/-- The radial path γ(t) stays in the exterior of the unit disk (norm ≥ 1). -/
lemma radial_path_norm_ge_one (w : ℂ) (hw : 1 < ‖w‖) :
    ∀ (t : unitInterval), 1 ≤ ‖w * (1 - t + t / ↑‖w‖)‖ := by
  intro t
  let r_t : ℝ := (t : ℝ)
  have ht0 : 0 ≤ r_t := t.2.1
  have ht1 : r_t ≤ 1 := t.2.2
  have hw0 : 0 < ‖w‖ := lt_trans zero_lt_one hw
  have h_pos : 0 ≤ 1 - r_t + r_t / ‖w‖ := by
    apply add_nonneg (sub_nonneg.mpr ht1) (div_nonneg ht0 hw0.le)
  rw [norm_mul]
  have h_norm_real : ‖(1 : ℂ) - ↑r_t + ↑r_t / ↑‖w‖‖ = 1 - r_t + r_t / ‖w‖ := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_div, ← Complex.ofReal_add]
    rw [Complex.norm_real, Real.norm_of_nonneg h_pos]
  rw [h_norm_real]
  have h_linear : ‖w‖ * (1 - r_t + r_t / ‖w‖) = ‖w‖ * (1 - r_t) + r_t := by
    field_simp [hw0.ne.symm]
  rw [h_linear]
  calc (1 : ℝ) = 1 * (1 - r_t) + r_t := by ring
    _ ≤ ‖w‖ * (1 - r_t) + r_t := by
      rw [add_le_add_iff_right]
      apply mul_le_mul_of_nonneg_right (le_of_lt hw) (sub_nonneg.mpr ht1)

/-- The radial path γ(t) has norm decreasing from |w| to 1. -/
lemma radial_path_norm_le_w (w : ℂ) (hw : 1 < ‖w‖) :
    ∀ (t : unitInterval), ‖w * (1 - t + t / ↑‖w‖)‖ ≤ ‖w‖ := by
  intro t
  let r_t : ℝ := (t : ℝ)
  have ht0 : 0 ≤ r_t := t.2.1
  have ht1 : r_t ≤ 1 := t.2.2
  have hw0 : 0 < ‖w‖ := lt_trans zero_lt_one hw
  have h_pos : 0 ≤ 1 - r_t + r_t / ‖w‖ := by
    apply add_nonneg (sub_nonneg.mpr ht1) (div_nonneg ht0 hw0.le)
  rw [norm_mul]
  have h_norm_real : ‖(1 : ℂ) - ↑r_t + ↑r_t / ↑‖w‖‖ = 1 - r_t + r_t / ‖w‖ := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_div, ← Complex.ofReal_add]
    rw [Complex.norm_real, Real.norm_of_nonneg h_pos]
  rw [h_norm_real]
  have h_linear : ‖w‖ * (1 - r_t + r_t / ‖w‖) = ‖w‖ * (1 - r_t) + r_t := by
    field_simp [hw0.ne.symm]
  rw [h_linear]
  calc ‖w‖ * (1 - r_t) + r_t = ‖w‖ - r_t * (‖w‖ - 1) := by ring
    _ ≤ ‖w‖ := by
      rw [sub_le_self_iff]
      apply mul_nonneg ht0 (sub_nonneg.mpr (le_of_lt hw))

/-- Auxiliary lemma to construct the path. -/
lemma construct_bottcher_path (c : ℂ) (hc : c ∈ MandelbrotSet) (z : ℂ) (w : ℂ)
    (h_norm_gt : 1 < ‖w‖) (hw_ne_zero : w ≠ 0)
    (h_start : extended_ray_map_free c w = z)
    (h_basin : z ∈ Quadratic.basin_of_infinity c) :
    ∃ p : Path z (extended_ray_map_free c (w / ↑‖w‖)), p 1 ∈ MLC.Quadratic.K c ∧
    ∀ t, p t = extended_ray_map_free c (w * (1 - t + t / ↑‖w‖)) := by
  let γ : Path w (w / ↑‖w‖) := {
    toFun := fun t => w * (1 - t + t / ↑‖w‖)
    continuous_toFun := by continuity
    source' := by simp
    target' := by simp; field_simp [hw_ne_zero]
  }
  
  have h_norm_γ := radial_path_norm_ge_one w h_norm_gt
  have h_gamma_cont : Continuous (extended_ray_map_free c ∘ γ) :=
    ContinuousOn.comp_continuous (extended_ray_map_free_continuous c hc) γ.continuous h_norm_γ

  let p_path : Path (extended_ray_map_free c w) (extended_ray_map_free c (w / ↑‖w‖)) := {
    toFun := extended_ray_map_free c ∘ γ
    continuous_toFun := h_gamma_cont
    source' := by dsimp; rw [γ.source]
    target' := by dsimp; rw [γ.target]
  }
  
  -- Use h_start to redefine source
  let p' : Path z (extended_ray_map_free c (w / ↑‖w‖)) := {
    toFun := p_path.toFun
    continuous_toFun := p_path.continuous_toFun
    source' := by rw [p_path.source', h_start]
    target' := p_path.target'
  }

  have hp'_eq : ∀ t, p' t = p_path t := by intro t; rfl

  have hp1_K : p' 1 ∈ MLC.Quadratic.K c := by
    rw [hp'_eq]
    dsimp [p_path]
    rw [γ.target]
    apply extended_ray_map_free_lands
    simp [hw_ne_zero]

  refine ⟨p', hp1_K, hp'_eq⟩

/--
Every point in the Green sublevel set `S` is path-connected to `K_c` within `S`.
-/
lemma green_sublevel_joined_to_Kc (c : ℂ) (hc : c ∈ MandelbrotSet) (n : ℕ)
    (h_inj_basin : Set.InjOn (proxy_bottcher_map c) (basin_of_infinity c)) :
    let S := MLC.Quadratic.GreenSublevel c n
    let K := MLC.Quadratic.K c
    ∀ z ∈ S, ∃ w ∈ K, JoinedIn S z w := by
  intro S K z hz
  by_cases h_in_K : z ∈ K
  · use z
    exact ⟨h_in_K, JoinedIn.refl (K_subset_green_sublevel c n h_in_K)⟩

  have h_basin := z_in_basin_of_not_mem_K c z h_in_K
  let w := proxy_bottcher_map c z
  obtain ⟨h_norm_gt, h_norm_lt⟩ := bottcher_norm_of_mem_sublevel c n z hz h_in_K
  
  have hw_ne_zero : w ≠ 0 := ne_zero_of_norm_ne_zero (ne_of_gt (lt_trans zero_lt_one h_norm_gt))
  
  have h_start : extended_ray_map_free c w = z := by
    rw [extended_ray_map_free_eq c w h_norm_gt]
    have hright :
        proxy_bottcher_map c (external_ray_map_free c w) = w :=
      external_ray_map_free_right_inverse c hc w h_norm_gt
    have hphi_ext :
        1 < ‖proxy_bottcher_map c (external_ray_map_free c w)‖ := by
      simpa [hright] using h_norm_gt
    have hnorm_ext :
        ‖proxy_bottcher_map c (external_ray_map_free c w)‖ =
          Real.exp (green_function c (external_ray_map_free c w)) :=
      norm_bottcher_eq_exp_green c (external_ray_map_free c w)
    have hpos_ext : 0 < green_function c (external_ray_map_free c w) := by
      have hgt_ext : 1 < Real.exp (green_function c (external_ray_map_free c w)) := by
        simpa [hnorm_ext] using hphi_ext
      exact (Real.one_lt_exp_iff).1 hgt_ext
    have hnotK_ext : external_ray_map_free c w ∉ MLC.Quadratic.K c :=
      (green_function_pos_iff_not_mem_K c (external_ray_map_free c w)).1 hpos_ext
    have h_basin_ext : external_ray_map_free c w ∈ basin_of_infinity c :=
      z_in_basin_of_not_mem_K c (external_ray_map_free c w) hnotK_ext
    have h_eq_phi :
        proxy_bottcher_map c (external_ray_map_free c w) = proxy_bottcher_map c z := by
      simpa [w] using hright
    exact h_inj_basin h_basin_ext h_basin h_eq_phi

  obtain ⟨p', hp1_K, hp'_eq⟩ := construct_bottcher_path c hc z w h_norm_gt hw_ne_zero h_start h_basin
  
  -- Cast p' to connect z to p' 1 explicitly
  let p'' : Path z (p' 1) := p'.cast rfl p'.target

  use p' 1
  refine ⟨hp1_K, ⟨p'', ?_⟩⟩
  
  intro t
  -- p'' t = p' t
  have hp''_eq : p'' t = p' t := by rw [Path.cast_coe]
  rw [hp''_eq]
  rw [hp'_eq]
  let u := w * (1 - t + t / ↑‖w‖)
  have h_u_norm_ge_1 := radial_path_norm_ge_one w h_norm_gt t
  have h_u_norm_le_w := radial_path_norm_le_w w h_norm_gt t
  
  by_cases hu_1 : ‖u‖ = 1
  · have : extended_ray_map_free c u ∈ K := by
      apply extended_ray_map_free_lands c u hu_1
    apply K_subset_green_sublevel c n this
  · have hu_gt_1 : 1 < ‖u‖ := lt_of_le_of_ne h_u_norm_ge_1 (Ne.symm hu_1)
    have hp'_val : extended_ray_map_free c u = external_ray_map_free c u := by
      rw [extended_ray_map_free_eq c u hu_gt_1]
    
    simp only [S, MLC.Quadratic.GreenSublevel, mem_setOf_eq]
    rw [hp'_val]
    have h_phi : ‖proxy_bottcher_map c (external_ray_map_free c u)‖ = ‖u‖ := by
      rw [external_ray_map_free_right_inverse c hc u hu_gt_1]
    rw [norm_bottcher_eq_exp_green c (external_ray_map_free c u)] at h_phi
    
    have h_G : green_function c (external_ray_map_free c u) = Real.log ‖u‖ := by
      rw [← h_phi, Real.log_exp]
    
    rw [h_G]
    rw [Real.log_lt_iff_lt_exp (lt_trans zero_lt_one hu_gt_1)]
    calc ‖u‖ ≤ ‖w‖ := h_u_norm_le_w
      _ < Real.exp ((1 / 2) ^ n) := h_norm_lt
