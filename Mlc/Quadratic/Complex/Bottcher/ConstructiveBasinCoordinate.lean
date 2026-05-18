import Mlc.Quadratic.Complex.Bottcher.BottcherOutsidePlan

namespace MLC

open Quadratic Complex Topology Set Filter Metric Real

namespace Quadratic

/-- The explicit proxy has the expected Green-function modulus everywhere. -/
lemma norm_polar_green_map_eq_exp_green (c z : ℂ) :
    ‖polar_green_map c z‖ = Real.exp (green_function c z) := by
  by_cases hz : z = 0
  · simp [polar_green_map, hz, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  · have hnormz : (‖z‖ : ℝ) ≠ 0 := norm_ne_zero_iff.2 hz
    have hdir : ‖z / (‖z‖ : ℂ)‖ = 1 := by
      rw [norm_div, Complex.norm_real, norm_norm, div_self hnormz]
    have hexp :
        ‖(Real.exp (green_function c z) : ℂ)‖ = Real.exp (green_function c z) := by
      simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc
      ‖polar_green_map c z‖
          = ‖(z / (‖z‖ : ℂ)) * (Real.exp (green_function c z) : ℂ)‖ := by
              simp [polar_green_map, hz]
      _ = ‖z / (‖z‖ : ℂ)‖ * ‖(Real.exp (green_function c z) : ℂ)‖ := by
            rw [norm_mul]
      _ = 1 * Real.exp (green_function c z) := by
            rw [hdir, hexp]
      _ = Real.exp (green_function c z) := by ring

/-- On the basin of infinity, the explicit proxy is exterior-valued. -/
lemma one_lt_norm_polar_green_map_of_mem_basin (c z : ℂ)
    (hz : z ∈ basin_of_infinity c) :
    1 < ‖polar_green_map c z‖ := by
  have hgreen_pos : 0 < green_function c z :=
    green_function_pos_of_basin c z hz
  rw [norm_polar_green_map_eq_exp_green]
  simpa using (Real.one_lt_exp_iff.mpr hgreen_pos)

/-- Constructive basin-valued Böttcher coordinate obtained by restricting the
explicit proxy to the basin of infinity. -/
noncomputable def basin_polar_green_map (c : ℂ) :
    {z : ℂ // z ∈ basin_of_infinity c} → {w : ℂ // 1 < ‖w‖} :=
  fun z => ⟨polar_green_map c z.1, one_lt_norm_polar_green_map_of_mem_basin c z.1 z.2⟩

@[simp] lemma basin_polar_green_map_coe (c : ℂ) (z : {z : ℂ // z ∈ basin_of_infinity c}) :
    ((basin_polar_green_map c z : {w : ℂ // 1 < ‖w‖}) : ℂ) = polar_green_map c z := rfl

/-- The basin-valued constructive coordinate has the expected Green-function
modulus. -/
lemma norm_basin_polar_green_map_eq_exp_green (c : ℂ)
    (z : {z : ℂ // z ∈ basin_of_infinity c}) :
    ‖((basin_polar_green_map c z : {w : ℂ // 1 < ‖w‖}) : ℂ)‖ =
      Real.exp (green_function c z) := by
  simpa using norm_polar_green_map_eq_exp_green c z

/-- Continuity of the explicit constructive coordinate away from `0`. -/
lemma polar_green_map_continuousAt_of_ne_zero (c z : ℂ) (hz : z ≠ 0) :
    ContinuousAt (polar_green_map c) z :=
  polar_green_map_continuousAt_of_ne_zero_outsidePlan c z hz

/-- The basin-valued constructive coordinate is continuous away from `0` on the
subspace basin. -/
lemma basin_polar_green_map_continuousAt_of_ne_zero (c : ℂ)
    (z : {z : ℂ // z ∈ basin_of_infinity c}) (hz : (z : ℂ) ≠ 0) :
    ContinuousAt (fun w : {z : ℂ // z ∈ basin_of_infinity c} =>
      (((basin_polar_green_map c w : {u : ℂ // 1 < ‖u‖}) : ℂ))) z := by
  simpa [basin_polar_green_map] using
    (polar_green_map_continuousAt_of_ne_zero c (z : ℂ) hz).comp
      continuous_subtype_val.continuousAt

/-- Exact ray formula for the constructive coordinate. -/
lemma polar_green_map_apply_ray (c u : ℂ) (hu : ‖u‖ = 1) (ρ : ℝ) (hρ : 0 < ρ) :
    polar_green_map c ((ρ : ℂ) * u) =
      u * ↑(Real.exp (green_function c ((ρ : ℂ) * u))) := by
  have hu0 : u ≠ 0 := by
    intro hu'
    simpa [hu'] using hu
  have hρ0 : ((ρ : ℂ)) ≠ 0 := by
    exact_mod_cast (ne_of_gt hρ)
  have hz0 : ((ρ : ℂ) * u) ≠ 0 := mul_ne_zero hρ0 hu0
  have hnorm : ‖((ρ : ℂ) * u)‖ = ρ := by
    calc
      ‖((ρ : ℂ) * u)‖ = ‖((ρ : ℂ))‖ * ‖u‖ := by simpa using norm_mul (ρ : ℂ) u
      _ = |ρ| * 1 := by simp [Complex.norm_real, hu]
      _ = ρ := by simp [abs_of_pos hρ]
  have hnormC : (‖((ρ : ℂ) * u)‖ : ℂ) = (ρ : ℂ) := by
    exact_mod_cast hnorm
  have hdir' : ((ρ : ℂ) * u) / (ρ : ℂ) = u := by
    field_simp [hρ0]
  have hdir : ((ρ : ℂ) * u) / (‖((ρ : ℂ) * u)‖ : ℂ) = u := by
    rw [hnormC]
    exact hdir'
  calc
    polar_green_map c ((ρ : ℂ) * u)
        = ((((ρ : ℂ) * u) / (‖((ρ : ℂ) * u)‖ : ℂ)) *
            ↑(Real.exp (green_function c ((ρ : ℂ) * u)))) := by
              simp [polar_green_map, hz0]
    _ = u * ↑(Real.exp (green_function c ((ρ : ℂ) * u))) := by rw [hdir]

/-- The explicit constructive coordinate is normalized at infinity. -/
lemma tendsto_polar_green_map_div_atInfinity (c : ℂ) :
    Tendsto (fun z => (polar_green_map c z) / z) atInfinity (𝓝 (1 : ℂ)) := by
  have hgreen := tendsto_green_function_minus_log_norm_atInfinity c
  have hExpR :
      Tendsto (fun z => Real.exp (green_function c z - Real.log ‖z‖))
        atInfinity (𝓝 (Real.exp (0 : ℝ))) :=
    (Real.continuous_exp.tendsto (0 : ℝ)).comp hgreen
  have hExpR' :
      Tendsto (fun z => Real.exp (green_function c z - Real.log ‖z‖))
        atInfinity (𝓝 (1 : ℝ)) := by
    simpa using hExpR
  have hExpC :
      Tendsto (fun z => ((Real.exp (green_function c z - Real.log ‖z‖)) : ℂ))
        atInfinity (𝓝 (1 : ℂ)) := by
    exact (Filter.tendsto_ofReal_iff).2 hExpR'
  have hpos : ∀ᶠ z in atInfinity, 0 < ‖z‖ :=
    eventually_atInfinity_norm_gt (0 : ℝ)
  have hratio :
      (fun z => (polar_green_map c z) / z) =ᶠ[atInfinity]
        fun z => ((Real.exp (green_function c z - Real.log ‖z‖)) : ℂ) := by
    refine hpos.mono ?_
    intro z hz
    have hz' : z ≠ 0 := (norm_ne_zero_iff).1 (ne_of_gt hz)
    have hz'' : (‖z‖ : ℝ) ≠ 0 := ne_of_gt hz
    have hz''' : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hz''
    have happly :
        polar_green_map c z = (z / ↑‖z‖) * ↑(Real.exp (green_function c z)) := by
      simp [polar_green_map, hz']
    calc
      (polar_green_map c z) / z
          = ((z / ↑‖z‖) * (Real.exp (green_function c z)) : ℂ) / z := by
              rw [happly]
      _ = ((Real.exp (green_function c z)) : ℂ) / (‖z‖ : ℂ) := by
            field_simp [hz', hz''', mul_comm, mul_left_comm, mul_assoc]
      _ = ((Real.exp (green_function c z - Real.log ‖z‖)) : ℂ) := by
            simp [Real.exp_sub, Real.exp_log hz, div_eq_mul_inv]
  exact (tendsto_congr' hratio).2 hExpC

/-- Optional theorem-facing summary of the constructive basin-valued coordinate
carried by the explicit proxy. -/
def ConstructiveBasinBottcherCoordinateData (c : ℂ) : Prop :=
  ∃ φ : ℂ → ℂ,
    (∀ z, z ∈ basin_of_infinity c → 1 < ‖φ z‖) ∧
    (∀ z, ‖φ z‖ = Real.exp (green_function c z)) ∧
    (∀ z, z ≠ 0 → ContinuousAt φ z) ∧
    Tendsto (fun z => φ z / z) atInfinity (𝓝 (1 : ℂ)) ∧
    (∀ u : ℂ, ‖u‖ = 1 → ∀ ρ : ℝ, 0 < ρ →
      φ ((ρ : ℂ) * u) = u * ↑(Real.exp (green_function c ((ρ : ℂ) * u))))

/-- Constructive realization of the missing basin-valued Böttcher coordinate
using the explicit proxy `polar_green_map`. -/
theorem constructive_basin_bottcher_coordinate_data (c : ℂ) :
    ConstructiveBasinBottcherCoordinateData c := by
  refine ⟨polar_green_map c, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact one_lt_norm_polar_green_map_of_mem_basin c z hz
  · intro z
    exact norm_polar_green_map_eq_exp_green c z
  · intro z hz
    exact polar_green_map_continuousAt_of_ne_zero c z hz
  · exact tendsto_polar_green_map_div_atInfinity c
  · intro u hu ρ hρ
    exact polar_green_map_apply_ray c u hu ρ hρ

end Quadratic

end MLC
