import Mlc.Quadratic.Complex.PuzzleBoundaryMotion
import Yoccoz.Quadratic.Complex.Escape
import Mlc.Quadratic.Complex.Bottcher.BottcherOnMDefs
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.Complex.Polynomial.Basic

namespace MLC

open Quadratic Complex Topology Set Filter Metric

namespace Quadratic

/-- Explicit total proxy built from the Green function and radial direction.
This is the current repository-level computational stand-in, not yet the final
theorem-facing Böttcher coordinate API. -/
noncomputable def polar_green_map (c : ℂ) (z : ℂ) : ℂ :=
  let u := if z = 0 then 1 else z / ↑‖z‖
  u * ↑(Real.exp (MLC.Quadratic.green_function c z))

/-- The domain where the Böttcher map is defined (basin of infinity). -/
def basin_of_infinity (c : ℂ) : Set ℂ :=
  MLC.basin_of_infinity c

/-- The theorem-facing Böttcher coordinate is now realized constructively by the
explicit proxy `polar_green_map`. The remaining frontier no longer needs a
separate coordinate-data axiom for the norm/continuity/ray package. -/
noncomputable def proxy_bottcher_map (c : ℂ) (z : ℂ) : ℂ :=
  polar_green_map c z

lemma orbit_eq_iter_quadratic_map (c z : ℂ) (n : ℕ) :
    MLC.Quadratic.orbit c z n = (MLC.quadratic_map c)^[n] z := by
  have hfc : MLC.Quadratic.fc c = MLC.quadratic_map c := by
    funext w
    rfl
  simpa [MLC.Quadratic.orbit] using congrArg (fun f => f^[n] z) hfc

lemma boundedOrbit_iff_not_tendsto_infty (c z : ℂ) :
    MLC.Quadratic.boundedOrbit c z ↔
      ¬ Tendsto (fun n => ‖(MLC.quadratic_map c)^[n] z‖) atTop atTop := by
  constructor
  · intro h_bounded h_tendsto
    rcases h_bounded with ⟨M, hM⟩
    have h_tendsto' := (Filter.tendsto_atTop.1 h_tendsto) (M + 1)
    rcases (Filter.eventually_atTop.1 h_tendsto') with ⟨N, hN⟩
    have hN' : M + 1 ≤ ‖(MLC.quadratic_map c)^[N] z‖ := hN N (le_rfl)
    have hbound' : ‖(MLC.quadratic_map c)^[N] z‖ ≤ M := by
      have h := hM N
      simpa [orbit_eq_iter_quadratic_map c z N] using h
    linarith
  · intro h_not_tendsto
    by_contra h_unbounded
    have h_unbounded' : ∀ M : ℝ, ∃ n : ℕ, ‖MLC.Quadratic.orbit c z n‖ > M := by
      intro M
      by_contra hM
      have h_le : ∀ n : ℕ, ‖MLC.Quadratic.orbit c z n‖ ≤ M := by
        intro n
        by_contra h_le
        exact hM ⟨n, lt_of_not_ge h_le⟩
      exact h_unbounded ⟨M, h_le⟩
    rcases h_unbounded' (MLC.Quadratic.R c) with ⟨n0, hn0⟩
    have h_tendsto_orbit :
        Tendsto (fun k => ‖MLC.Quadratic.orbit c z k‖) atTop atTop := by
      rw [Filter.tendsto_atTop]
      intro M
      rcases (MLC.Quadratic.escape_lemma (c := c) (z := z) n0 hn0 M) with ⟨N, hN⟩
      rw [Filter.eventually_atTop]
      refine ⟨N, ?_⟩
      intro m hm
      exact le_of_lt (hN m hm)
    have h_tendsto :
        Tendsto (fun n => ‖(MLC.quadratic_map c)^[n] z‖) atTop atTop := by
      simpa [orbit_eq_iter_quadratic_map c z] using h_tendsto_orbit
    exact h_not_tendsto h_tendsto

theorem basin_eq_compl_K (c : ℂ) : basin_of_infinity c = (MLC.Quadratic.K c)ᶜ := by
  ext z
  constructor
  · intro hz
    have hz' : Tendsto (fun n => ‖(MLC.quadratic_map c)^[n] z‖) atTop atTop := by
      simpa [basin_of_infinity, MLC.basin_of_infinity] using hz
    have hnot : ¬ MLC.Quadratic.boundedOrbit c z := by
      intro hbounded
      have hnt : ¬ Tendsto (fun n => ‖(MLC.quadratic_map c)^[n] z‖) atTop atTop :=
        (boundedOrbit_iff_not_tendsto_infty c z).1 hbounded
      exact hnt hz'
    simpa [Set.mem_compl_iff, MLC.Quadratic.K, Set.mem_setOf_eq] using hnot
  · intro hz
    have hnot : ¬ MLC.Quadratic.boundedOrbit c z := by
      simpa [Set.mem_compl_iff, MLC.Quadratic.K, Set.mem_setOf_eq] using hz
    have hz' : Tendsto (fun n => ‖(MLC.quadratic_map c)^[n] z‖) atTop atTop := by
      by_contra hnt
      exact hnot ((boundedOrbit_iff_not_tendsto_infty c z).2 hnt)
    simpa [basin_of_infinity, MLC.basin_of_infinity] using hz'

/-- Data package for an exterior inverse of a theorem-facing coordinate. -/
def ExternalRayMapDataFor (c : ℂ) (φ : ℂ → ℂ) : Prop :=
    ∃ f : ℂ → ℂ,
      (∀ w, 1 < ‖w‖ → φ (f w) = w) ∧
        (∀ z, ‖z‖ > ‖c‖ + 2 → f (φ z) = z)

/-- Data package for an exterior inverse of the current theorem-facing
`proxy_bottcher_map`. -/
def ExternalRayMapData (c : ℂ) : Prop :=
  ExternalRayMapDataFor c (proxy_bottcher_map c)

/-- Preferred basin-valued theorem-facing package suggested by the current
mathematical analysis. Unlike `ExternalRayMapData`, this formulation keeps the
actual coordinate fixed to `proxy_bottcher_map` and only asks for exterior-valuedness
on the basin itself, so it avoids the false full-exterior surjectivity demand
for the restricted outside map. -/
def BasinExternalRayMapDataFor (c : ℂ) (φ : ℂ → ℂ) : Prop :=
    ∃ Ψ : ℂ → ℂ,
      (∀ z, z ∈ basin_of_infinity c → 1 < ‖φ z‖) ∧
      (∀ z, z ∈ basin_of_infinity c →
        φ (MLC.quadratic_map c z) = (φ z)^2) ∧
      (∀ w, 1 < ‖w‖ → Ψ w ∈ basin_of_infinity c ∧ φ (Ψ w) = w) ∧
      (∀ z, ‖z‖ > ‖c‖ + 2 → Ψ (φ z) = z)

/-- Preferred basin-valued theorem-facing package specialized to the current
`proxy_bottcher_map`. -/
def BasinExternalRayMapData (c : ℂ) : Prop :=
  BasinExternalRayMapDataFor c (proxy_bottcher_map c)

/-- `c = 2` specialization of the basin-valued package. -/
def BasinExternalRayMapDataTwo : Prop :=
  BasinExternalRayMapData (2 : ℂ)

/-- Forget the basin-membership refinement from a basin-valued package and
recover the usual exterior inverse data for the same coordinate. -/
lemma externalRayMapDataFor_of_basinExternalRayMapDataFor (c : ℂ) (φ : ℂ → ℂ)
    (h_data : BasinExternalRayMapDataFor c φ) :
    ExternalRayMapDataFor c φ := by
  rcases h_data with ⟨Ψ, _, _, hright, hleft⟩
  exact ⟨Ψ, fun w hw => (hright w hw).2, hleft⟩

/-- Forget the basin-membership refinement from the basin-valued package and
recover the usual exterior inverse data. -/
lemma externalRayMapData_of_basinExternalRayMapData (c : ℂ)
    (h_data : BasinExternalRayMapData c) :
    ExternalRayMapData c :=
  externalRayMapDataFor_of_basinExternalRayMapDataFor c (proxy_bottcher_map c) h_data

/-- Unpack the ray-map data package into its existential form. -/
theorem external_ray_map_exists_of_data (c : ℂ) (h_data : ExternalRayMapData c) :
    ∃ f : ℂ → ℂ,
      (∀ w, 1 < ‖w‖ → proxy_bottcher_map c (f w) = w) ∧
        (∀ z, ‖z‖ > ‖c‖ + 2 → f (proxy_bottcher_map c z) = z) :=
  h_data

theorem external_ray_map_data_of_exists (c : ℂ)
    (h_exists :
      ∃ f : ℂ → ℂ,
        (∀ w, 1 < ‖w‖ → proxy_bottcher_map c (f w) = w) ∧
          (∀ z, ‖z‖ > ‖c‖ + 2 → f (proxy_bottcher_map c z) = z)) :
    ExternalRayMapData c :=
  h_exists

noncomputable def external_ray_map_of_data {c : ℂ}
    (h_data : ExternalRayMapData c) (w : ℂ) : ℂ :=
  (Classical.choose h_data) w

lemma external_ray_map_of_data_right_inverse {c : ℂ}
    (h_data : ExternalRayMapData c) (w : ℂ) (hw : 1 < ‖w‖) :
    proxy_bottcher_map c (external_ray_map_of_data h_data w) = w := by
  exact (Classical.choose_spec h_data).1 w hw

lemma external_ray_map_of_data_left_inverse_large {c : ℂ}
    (h_data : ExternalRayMapData c) (z : ℂ) (hz : ‖z‖ > ‖c‖ + 2) :
    external_ray_map_of_data h_data (proxy_bottcher_map c z) = z := by
  exact (Classical.choose_spec h_data).2 z hz

theorem norm_bottcher_eq_exp_green (c : ℂ) (z : ℂ) :
    ‖proxy_bottcher_map c z‖ = Real.exp (MLC.Quadratic.green_function c z) := by
  by_cases hz : z = 0
  · simp [proxy_bottcher_map, polar_green_map, hz]
  · have hnormz : (‖z‖ : ℝ) ≠ 0 := norm_ne_zero_iff.2 hz
    have hdir : ‖z / (‖z‖ : ℂ)‖ = 1 := by
      rw [norm_div, Complex.norm_real, norm_norm, div_self hnormz]
    have hexp :
        ‖(Real.exp (MLC.Quadratic.green_function c z) : ℂ)‖ =
          Real.exp (MLC.Quadratic.green_function c z) := by
      simp [Complex.norm_real, abs_of_pos (Real.exp_pos _)]
    calc
      ‖proxy_bottcher_map c z‖
          = ‖(z / (‖z‖ : ℂ)) * (Real.exp (MLC.Quadratic.green_function c z) : ℂ)‖ := by
              simp [proxy_bottcher_map, polar_green_map, hz]
      _ = ‖z / (‖z‖ : ℂ)‖ * ‖(Real.exp (MLC.Quadratic.green_function c z) : ℂ)‖ := by
            rw [norm_mul]
      _ = 1 * Real.exp (MLC.Quadratic.green_function c z) := by
            rw [hdir, hexp]
      _ = Real.exp (MLC.Quadratic.green_function c z) := by ring

theorem proxy_bottcher_map_continuousAt_of_ne_zero (c : ℂ) (z : ℂ) (hz : z ≠ 0) :
    ContinuousAt (proxy_bottcher_map c) z := by
  have hnorm_ne : (‖z‖ : ℂ) ≠ 0 := by
    exact_mod_cast (norm_ne_zero_iff.2 hz)
  have hdiv : ContinuousAt (fun w : ℂ => w / (‖w‖ : ℂ)) z :=
    continuousAt_id.div
      ((Complex.continuous_ofReal.comp continuous_norm).continuousAt) hnorm_ne
  have hif :
      (fun w : ℂ => if w = 0 then (1 : ℂ) else w / (‖w‖ : ℂ)) =ᶠ[𝓝 z]
        (fun w : ℂ => w / (‖w‖ : ℂ)) := by
    filter_upwards [eventually_ne_nhds hz] with w hw
    simp [hw]
  have hdir : ContinuousAt (fun w : ℂ => if w = 0 then (1 : ℂ) else w / (‖w‖ : ℂ)) z :=
    hdiv.congr_of_eventuallyEq hif
  have hexp :
      ContinuousAt (fun w : ℂ => (Real.exp (MLC.Quadratic.green_function c w) : ℂ)) z :=
    (Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp (MLC.Quadratic.continuous_green_function c))).continuousAt
  change ContinuousAt (Quadratic.polar_green_map c) z
  change ContinuousAt
    (fun w : ℂ =>
      (if w = 0 then (1 : ℂ) else w / (‖w‖ : ℂ)) *
        (Real.exp (MLC.Quadratic.green_function c w) : ℂ)) z
  exact hdir.mul hexp

theorem proxy_bottcher_map_apply_ray (c : ℂ) (u : ℂ) (hu : ‖u‖ = 1) (ρ : ℝ)
    (hρ : 0 < ρ) :
    proxy_bottcher_map c ((ρ : ℂ) * u) =
      u * ↑(Real.exp (MLC.Quadratic.green_function c ((ρ : ℂ) * u))) := by
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
    proxy_bottcher_map c ((ρ : ℂ) * u)
        = ((((ρ : ℂ) * u) / (‖((ρ : ℂ) * u)‖ : ℂ)) *
            ↑(Real.exp (MLC.Quadratic.green_function c ((ρ : ℂ) * u)))) := by
              simp [proxy_bottcher_map, polar_green_map, hz0]
    _ = u * ↑(Real.exp (MLC.Quadratic.green_function c ((ρ : ℂ) * u))) := by rw [hdir]

lemma bottcher_left_inv_of_data {c : ℂ} (h_data : ExternalRayMapData c)
    (z : ℂ) (hz : z ∈ basin_of_infinity c)
    (h_inj : Function.Injective (proxy_bottcher_map c)) :
    external_ray_map_of_data h_data (proxy_bottcher_map c z) = z := by
  have hz' : z ∉ MLC.Quadratic.K c := by
    have : z ∈ (MLC.Quadratic.K c)ᶜ := by
      simpa [basin_eq_compl_K c] using hz
    simpa [Set.mem_compl_iff] using this
  have hpos : 0 < MLC.Quadratic.green_function c z :=
    (MLC.Quadratic.green_function_pos_iff_not_mem_K c z).2 hz'
  have hnorm : 1 < ‖proxy_bottcher_map c z‖ := by
    have hnorm' : ‖proxy_bottcher_map c z‖ = Real.exp (MLC.Quadratic.green_function c z) :=
      norm_bottcher_eq_exp_green c z
    have hgt : 1 < Real.exp (MLC.Quadratic.green_function c z) := by
      simpa using (Real.one_lt_exp_iff.mpr hpos)
    simpa [hnorm'] using hgt
  have hright :
      proxy_bottcher_map c (external_ray_map_of_data h_data (proxy_bottcher_map c z)) =
        proxy_bottcher_map c z := by
    simpa using external_ray_map_of_data_right_inverse h_data (proxy_bottcher_map c z) hnorm
  exact h_inj hright

lemma external_ray_map_left_inverse_outside_open_of_data {c : ℂ}
    (h_data : ExternalRayMapData c) (z : ℂ) (hz : ‖z‖ > ‖c‖ + 2) :
    external_ray_map_of_data h_data (proxy_bottcher_map c z) = z := by
  exact external_ray_map_of_data_left_inverse_large h_data z hz

end Quadratic

end MLC
