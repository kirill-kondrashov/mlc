import Mlc.Quadratic.Complex.PuzzleBoundaryMotion
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.PolarCoord

namespace MLC

open Quadratic Complex Topology Set Filter Metric

namespace Quadratic

/-- The Böttcher map `φ_c` conjugates `f_c(z) = z^2 + c` to `z^2` near infinity. -/
noncomputable def bottcher_map (c : ℂ) (z : ℂ) : ℂ :=
  let w := lim (map (fun n => ((fun w => w^2 + c)^[n] z) ^ ((1 : ℂ) / (2 : ℂ) ^ n)) atTop)
  let u := if w = 0 then 1 else w / ↑‖w‖
  u * ↑(Real.exp (MLC.Quadratic.green_function c z))

/-- The domain where the Böttcher map is defined (basin of infinity). -/
def basin_of_infinity (c : ℂ) : Set ℂ :=
  {z | ¬ MLC.Quadratic.boundedOrbit c z}

theorem basin_eq_compl_K (c : ℂ) : basin_of_infinity c = (MLC.Quadratic.K c)ᶜ := by
  ext z
  simp [basin_of_infinity, MLC.Quadratic.K, MLC.Quadratic.boundedOrbit]


/-- The Böttcher map satisfies |φ_c(z)| = exp(G_c(z)). -/
theorem norm_bottcher_eq_exp_green (c : ℂ) (z : ℂ) :
    ‖bottcher_map c z‖ = Real.exp (MLC.Quadratic.green_function c z) := by
  dsimp [bottcher_map]
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _)]
  let w := lim (map (fun n => ((fun w => w^2 + c)^[n] z) ^ ((1 : ℂ) / (2 : ℂ) ^ n)) atTop)
  let u := if w = 0 then 1 else w / ↑‖w‖
  have : ‖u‖ = 1 := by
    dsimp [u]
    split_ifs with h
    · simp
    · rw [norm_div, Complex.norm_real, norm_norm]
      exact div_self (norm_ne_zero_iff.mpr h)
  rw [this, one_mul]

/-- The inverse of the Böttcher map exists (ray map). -/
noncomputable def external_ray_map (c : ℂ) (w : ℂ) : ℂ :=
  if 1 < ‖w‖ then Function.invFun (bottcher_map c) w else 0

/-- The ray map is the inverse of the Böttcher map. -/
axiom bottcher_right_inv (c : ℂ) (w : ℂ) (hw : 1 < ‖w‖) :
    bottcher_map c (external_ray_map c w) = w

axiom bottcher_left_inv (c : ℂ) (z : ℂ) (hz : z ∈ basin_of_infinity c) :
    external_ray_map c (bottcher_map c z) = z

/-- The ray map is continuous on the exterior of the disk. -/
axiom ray_map_continuous_on (c : ℂ) :
    ContinuousOn (external_ray_map c) {w | 1 < ‖w‖}

/-- The Böttcher map is continuous on the basin.
    This follows from Böttcher's theorem regarding the locally uniform convergence
    of the sequence `(f_c^n(z))^(1/2^n)` in the basin of infinity.
    Here we prove it using the Invariance of Domain on the inverse map. -/
axiom invariance_of_domain_complex {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ}
    (hf : ContinuousOn f U) (hinj : Set.InjOn f U) : IsOpenMap (U.restrict f)

theorem bottcher_continuous_on (c : ℂ) :
    ContinuousOn (bottcher_map c) (basin_of_infinity c) := by
  -- Prove basin is open
  have h_G_cont : Continuous (MLC.Quadratic.green_function c) := MLC.Quadratic.continuous_green_function c
  have h_basin_open : IsOpen (basin_of_infinity c) := by
    rw [basin_eq_compl_K]
    have h_K_closed : IsClosed (MLC.Quadratic.K c) := by
      have : MLC.Quadratic.K c = MLC.Quadratic.green_function c ⁻¹' {0} := by
        ext z
        rw [mem_preimage, mem_singleton_iff, MLC.Quadratic.green_function_eq_zero_iff_mem_K]
      rw [this]
      exact isClosed_singleton.preimage h_G_cont
    exact h_K_closed.isOpen_compl

  -- Prove exterior is open
  have h_ext_open : IsOpen {w : ℂ | 1 < ‖w‖} :=
    isOpen_Ioi.preimage continuous_norm

  -- Prove injectivity of ray map
  have h_inj : Set.InjOn (external_ray_map c) {w | 1 < ‖w‖} := by
    intro x hx y hy h_eq
    rw [← bottcher_right_inv c x hx, ← bottcher_right_inv c y hy, h_eq]

  -- Apply Invariance of Domain
  have h_open_map : IsOpenMap ({w | 1 < ‖w‖}.restrict (external_ray_map c)) :=
    invariance_of_domain_complex h_ext_open (ray_map_continuous_on c) h_inj

  -- ContinuousOn via open map property of inverse
  rw [continuousOn_iff_continuous_restrict]
  rw [continuous_def]
  intro U hU
  
  let V := U ∩ {w | 1 < ‖w‖}
  have hV_open : IsOpen V := IsOpen.inter hU h_ext_open
  
  let V' : Set {w | 1 < ‖w‖} := Subtype.val ⁻¹' V
  have hV'_open : IsOpen V' := isOpen_induced hV_open
  
  have h_image_open : IsOpen (external_ray_map c '' V) := by
    have h_eq : external_ray_map c '' V = ({w | 1 < ‖w‖}.restrict (external_ray_map c)) '' V' := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        refine ⟨⟨x, hx.2⟩, ?_, rfl⟩
        simp only [V', mem_preimage, hx]
      · rintro ⟨⟨x, hx_ext⟩, hx_V', rfl⟩
        simp only [V', mem_preimage] at hx_V'
        use x
        exact ⟨hx_V', rfl⟩
    rw [h_eq]
    exact h_open_map V' hV'_open
  
  have h_eq_image : { z ∈ basin_of_infinity c | bottcher_map c z ∈ V } = external_ray_map c '' V := by
    ext z
    constructor
    · intro hz
      use bottcher_map c z
      constructor
      · exact hz.2
      · exact bottcher_left_inv c z hz.1
    · rintro ⟨w, hw, rfl⟩
      have hw_gt : 1 < ‖w‖ := hw.2
      constructor
      · rw [basin_eq_compl_K]
        intro hK
        have hG : MLC.Quadratic.green_function c (external_ray_map c w) = 0 :=
          (MLC.Quadratic.green_function_eq_zero_iff_mem_K c _).mpr hK
        have h_norm : ‖bottcher_map c (external_ray_map c w)‖ = 1 := by
          rw [norm_bottcher_eq_exp_green, hG, Real.exp_zero]
        rw [bottcher_right_inv c w hw_gt] at h_norm
        linarith
      · rw [bottcher_right_inv c w hw_gt]
        exact hw
    
  rw [isOpen_induced_iff]
  use external_ray_map c '' V
  constructor
  · exact h_image_open
  · ext ⟨z, hz_basin⟩
    simp only [mem_preimage, restrict_apply]
    show z ∈ external_ray_map c '' V ↔ bottcher_map c z ∈ U
    constructor
    · intro h_in_RHS
      have h_in_LHS : z ∈ { w ∈ basin_of_infinity c | bottcher_map c w ∈ V } := by
        rw [h_eq_image]
        exact h_in_RHS
      exact h_in_LHS.2.1
      
    · intro h_in_U
      have h_ext : 1 < ‖bottcher_map c z‖ := by
        rw [norm_bottcher_eq_exp_green]
        apply Real.one_lt_exp_iff.mpr
        have hK : z ∉ MLC.Quadratic.K c := by
          rw [basin_eq_compl_K] at hz_basin
          exact hz_basin
        rw [← MLC.Quadratic.green_function_eq_zero_iff_mem_K] at hK
        exact lt_of_le_of_ne (MLC.Quadratic.green_function_nonneg c z) (Ne.symm hK)
      
      have h_in_LHS : z ∈ { w ∈ basin_of_infinity c | bottcher_map c w ∈ V } := 
        ⟨hz_basin, ⟨h_in_U, h_ext⟩⟩
      
      have h_in_RHS : z ∈ external_ray_map c '' V := by
        rw [← h_eq_image]
        exact h_in_LHS
        
      exact h_in_RHS

/-- The Böttcher map is a conformal isomorphism from the basin to the exterior of the disk. -/
theorem bottcher_map_image (c : ℂ) :
    bottcher_map c '' basin_of_infinity c = {w | 1 < ‖w‖} := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [mem_setOf_eq, norm_bottcher_eq_exp_green]
    apply Real.one_lt_exp_iff.mpr
    rw [basin_eq_compl_K] at hz
    have hG := (MLC.Quadratic.green_function_eq_zero_iff_mem_K c z).not.mpr hz
    exact lt_of_le_of_ne (MLC.Quadratic.green_function_nonneg c z) (Ne.symm hG)
  · intro hw
    rw [mem_setOf_eq] at hw
    use external_ray_map c w
    constructor
    · rw [basin_eq_compl_K]
      intro hK
      have hG : MLC.Quadratic.green_function c (external_ray_map c w) = 0 :=
        (MLC.Quadratic.green_function_eq_zero_iff_mem_K c _).mpr hK
      have h_norm : ‖bottcher_map c (external_ray_map c w)‖ = 1 := by
        rw [norm_bottcher_eq_exp_green, hG, Real.exp_zero]
      rw [bottcher_right_inv c w hw] at h_norm
      linarith
    · exact bottcher_right_inv c w hw

/-- Extension of the ray map to the closed exterior of the disk. -/
noncomputable def extended_ray_map (c : ℂ) (w : ℂ) : ℂ :=
  if 1 ≤ ‖w‖ then lim (map (external_ray_map c) (nhdsWithin w {z | 1 < ‖z‖})) else 0

/-- The extended ray map agrees with the external ray map on the open exterior. -/
axiom extended_ray_map_eq (c : ℂ) (w : ℂ) (hw : 1 < ‖w‖) :
    extended_ray_map c w = external_ray_map c w

/-- The extended ray map is continuous on the closed exterior {w | 1 ≤ |w|}. -/
axiom extended_ray_map_continuous (c : ℂ) :
    ContinuousOn (extended_ray_map c) {w | 1 ≤ ‖w‖}

/-- The extended ray map maps the unit circle to the Julia set (subset of K). -/
axiom extended_ray_map_lands (c : ℂ) (w : ℂ) (hw : ‖w‖ = 1) :
    extended_ray_map c w ∈ MLC.Quadratic.K c

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
    z ∈ basin_of_infinity c := by
  rw [basin_eq_compl_K]
  exact h

/-- Bounds on the Böttcher coordinate norm for points in the sublevel set but not in K. -/
lemma bottcher_norm_of_mem_sublevel (c : ℂ) (n : ℕ) (z : ℂ) 
    (hz : z ∈ MLC.Quadratic.GreenSublevel c n) (hK : z ∉ MLC.Quadratic.K c) :
    let w := bottcher_map c z
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
lemma construct_bottcher_path (c : ℂ) (z : ℂ) (w : ℂ) 
    (h_norm_gt : 1 < ‖w‖) (hw_ne_zero : w ≠ 0)
    (h_start : extended_ray_map c w = z) 
    (h_basin : z ∈ basin_of_infinity c) :
    ∃ p : Path z (extended_ray_map c (w / ↑‖w‖)), p 1 ∈ MLC.Quadratic.K c ∧ 
    ∀ t, p t = extended_ray_map c (w * (1 - t + t / ↑‖w‖)) := by
  let γ : Path w (w / ↑‖w‖) := {
    toFun := fun t => w * (1 - t + t / ↑‖w‖)
    continuous_toFun := by continuity
    source' := by simp
    target' := by simp; field_simp [hw_ne_zero]
  }
  
  have h_norm_γ := radial_path_norm_ge_one w h_norm_gt
  have h_gamma_cont : Continuous (extended_ray_map c ∘ γ) :=
    ContinuousOn.comp_continuous (extended_ray_map_continuous c) γ.continuous h_norm_γ

  let p_path : Path (extended_ray_map c w) (extended_ray_map c (w / ↑‖w‖)) := {
    toFun := extended_ray_map c ∘ γ
    continuous_toFun := h_gamma_cont
    source' := by dsimp; rw [γ.source]
    target' := by dsimp; rw [γ.target]
  }
  
  -- Use h_start to redefine source
  let p' : Path z (extended_ray_map c (w / ↑‖w‖)) := {
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
    apply extended_ray_map_lands
    simp [hw_ne_zero]

  refine ⟨p', hp1_K, hp'_eq⟩

/--
Every point in the Green sublevel set `S` is path-connected to `K_c` within `S`.
-/
lemma green_sublevel_joined_to_Kc (c : ℂ) (n : ℕ) :
    let S := MLC.Quadratic.GreenSublevel c n
    let K := MLC.Quadratic.K c
    ∀ z ∈ S, ∃ w ∈ K, JoinedIn S z w := by
  intro S K z hz
  by_cases h_in_K : z ∈ K
  · use z
    exact ⟨h_in_K, JoinedIn.refl (K_subset_green_sublevel c n h_in_K)⟩

  have h_basin := z_in_basin_of_not_mem_K c z h_in_K
  let w := bottcher_map c z
  obtain ⟨h_norm_gt, h_norm_lt⟩ := bottcher_norm_of_mem_sublevel c n z hz h_in_K
  
  have hw_ne_zero : w ≠ 0 := ne_zero_of_norm_ne_zero (ne_of_gt (lt_trans zero_lt_one h_norm_gt))
  
  have h_start : extended_ray_map c w = z := by
    rw [extended_ray_map_eq c w h_norm_gt]
    apply bottcher_left_inv c z h_basin

  obtain ⟨p', hp1_K, hp'_eq⟩ := construct_bottcher_path c z w h_norm_gt hw_ne_zero h_start h_basin
  
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
  · have : extended_ray_map c u ∈ K := by
      apply extended_ray_map_lands c u hu_1
    apply K_subset_green_sublevel c n this
  · have hu_gt_1 : 1 < ‖u‖ := lt_of_le_of_ne h_u_norm_ge_1 (Ne.symm hu_1)
    have hp'_val : extended_ray_map c u = external_ray_map c u := by
      rw [extended_ray_map_eq c u hu_gt_1]
    
    simp only [S, MLC.Quadratic.GreenSublevel, mem_setOf_eq]
    rw [hp'_val]
    have h_phi : ‖bottcher_map c (external_ray_map c u)‖ = ‖u‖ := by
      rw [bottcher_right_inv c u hu_gt_1]
    rw [norm_bottcher_eq_exp_green c (external_ray_map c u)] at h_phi
    
    have h_G : green_function c (external_ray_map c u) = Real.log ‖u‖ := by
      rw [← h_phi, Real.log_exp]
    
    rw [h_G]
    rw [Real.log_lt_iff_lt_exp (lt_trans zero_lt_one hu_gt_1)]
    calc ‖u‖ ≤ ‖w‖ := h_u_norm_le_w
      _ < Real.exp ((1 / 2) ^ n) := h_norm_lt