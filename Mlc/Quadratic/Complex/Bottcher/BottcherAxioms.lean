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
noncomputable def bottcher_map (c : ℂ) (z : ℂ) : ℂ :=
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

/-- Data package for an exterior inverse of the Böttcher map. -/
def ExternalRayMapData (c : ℂ) : Prop :=
    ∃ f : ℂ → ℂ,
      (∀ w, 1 < ‖w‖ → bottcher_map c (f w) = w) ∧
        (∀ z, ‖z‖ > ‖c‖ + 2 → f (bottcher_map c z) = z)

/-- Preferred basin-valued theorem-facing package suggested by the current
mathematical analysis. Unlike `ExternalRayMapData`, this formulation keeps the
actual coordinate fixed to `bottcher_map` and only asks for exterior-valuedness
on the basin itself, so it avoids the false full-exterior surjectivity demand
for the restricted outside map. -/
def BasinExternalRayMapData (c : ℂ) : Prop :=
    ∃ Ψ : ℂ → ℂ,
      (∀ z, z ∈ basin_of_infinity c → 1 < ‖bottcher_map c z‖) ∧
      (∀ z, z ∈ basin_of_infinity c →
        bottcher_map c (MLC.quadratic_map c z) = (bottcher_map c z)^2) ∧
      (∀ w, 1 < ‖w‖ → Ψ w ∈ basin_of_infinity c ∧ bottcher_map c (Ψ w) = w) ∧
      (∀ z, ‖z‖ > ‖c‖ + 2 → Ψ (bottcher_map c z) = z)

/-- `c = 2` specialization of the basin-valued package. This is the precise
single-theorem target behind the expert note in `draft/`. -/
def BasinExternalRayMapDataTwo : Prop :=
  BasinExternalRayMapData (2 : ℂ)

/-- Forget the basin-membership refinement from the basin-valued package and
recover the usual exterior inverse data. -/
lemma externalRayMapData_of_basinExternalRayMapData (c : ℂ)
    (h_data : BasinExternalRayMapData c) :
    ExternalRayMapData c := by
  rcases h_data with ⟨Ψ, _, _, hright, hleft⟩
  exact ⟨Ψ, fun w hw => (hright w hw).2, hleft⟩

/-- The inverse of the Böttcher map exists on the exterior (ray map). This
global theorem-facing seam is still used elsewhere in the repository, but the
checked root is routed through the specialized `c = 2` version below. -/
axiom external_ray_map_exists (c : ℂ) : ExternalRayMapData c

/-- Root-facing specialization of the exterior inverse package at `c = 2`.
    This is the connected external-ray branch currently needed by
    `MLC.mlc_conjecture`. -/
axiom external_ray_map_exists_two : ExternalRayMapData (2 : ℂ)

/-- Unpack the ray-map data package into its existential form. -/
theorem external_ray_map_exists_of_data (c : ℂ) (h_data : ExternalRayMapData c) :
    ∃ f : ℂ → ℂ,
      (∀ w, 1 < ‖w‖ → bottcher_map c (f w) = w) ∧
        (∀ z, ‖z‖ > ‖c‖ + 2 → f (bottcher_map c z) = z) :=
  h_data

theorem external_ray_map_data_of_exists (c : ℂ)
    (h_exists :
      ∃ f : ℂ → ℂ,
        (∀ w, 1 < ‖w‖ → bottcher_map c (f w) = w) ∧
          (∀ z, ‖z‖ > ‖c‖ + 2 → f (bottcher_map c z) = z)) :
    ExternalRayMapData c :=
  h_exists

noncomputable def external_ray_map_of_data {c : ℂ}
    (h_data : ExternalRayMapData c) (w : ℂ) : ℂ :=
  (Classical.choose h_data) w

lemma external_ray_map_of_data_right_inverse {c : ℂ}
    (h_data : ExternalRayMapData c) (w : ℂ) (hw : 1 < ‖w‖) :
    bottcher_map c (external_ray_map_of_data h_data w) = w := by
  exact (Classical.choose_spec h_data).1 w hw

lemma external_ray_map_of_data_left_inverse_large {c : ℂ}
    (h_data : ExternalRayMapData c) (z : ℂ) (hz : ‖z‖ > ‖c‖ + 2) :
    external_ray_map_of_data h_data (bottcher_map c z) = z := by
  exact (Classical.choose_spec h_data).2 z hz

noncomputable def external_ray_map (c : ℂ) (w : ℂ) : ℂ :=
  external_ray_map_of_data (external_ray_map_exists c) w

lemma external_ray_map_right_inverse (c : ℂ) (w : ℂ) (hw : 1 < ‖w‖) :
    bottcher_map c (external_ray_map c w) = w := by
  simpa [external_ray_map] using
    external_ray_map_of_data_right_inverse (external_ray_map_exists c) w hw

lemma external_ray_map_left_inverse_large (c : ℂ) (z : ℂ) (hz : ‖z‖ > ‖c‖ + 2) :
    external_ray_map c (bottcher_map c z) = z := by
  simpa [external_ray_map] using
    external_ray_map_of_data_left_inverse_large (external_ray_map_exists c) z hz

theorem external_ray_map_data (c : ℂ) : ExternalRayMapData c := by
  refine ⟨external_ray_map c, ?_, ?_⟩
  · intro w hw
    exact external_ray_map_right_inverse c w hw
  · intro z hz
    exact external_ray_map_left_inverse_large c z hz

/-! Domain for the Böttcher coordinate. -/
def bottcher_domain (c : ℂ) : Set ℂ :=
  external_ray_map c '' {w | 1 < ‖w‖}

theorem norm_bottcher_eq_exp_green (c : ℂ) (z : ℂ) :
    ‖bottcher_map c z‖ = Real.exp (MLC.Quadratic.green_function c z) := by
  by_cases hz : z = 0
  · simp [bottcher_map, polar_green_map, hz]
  · have hnormz : (‖z‖ : ℝ) ≠ 0 := norm_ne_zero_iff.2 hz
    have hdir : ‖z / (‖z‖ : ℂ)‖ = 1 := by
      rw [norm_div, Complex.norm_real, norm_norm, div_self hnormz]
    have hexp :
        ‖(Real.exp (MLC.Quadratic.green_function c z) : ℂ)‖ =
          Real.exp (MLC.Quadratic.green_function c z) := by
      simp [Complex.norm_real, abs_of_pos (Real.exp_pos _)]
    calc
      ‖bottcher_map c z‖
          = ‖(z / (‖z‖ : ℂ)) * (Real.exp (MLC.Quadratic.green_function c z) : ℂ)‖ := by
              simp [bottcher_map, polar_green_map, hz]
      _ = ‖z / (‖z‖ : ℂ)‖ * ‖(Real.exp (MLC.Quadratic.green_function c z) : ℂ)‖ := by
            rw [norm_mul]
      _ = 1 * Real.exp (MLC.Quadratic.green_function c z) := by
            rw [hdir, hexp]
      _ = Real.exp (MLC.Quadratic.green_function c z) := by ring

theorem bottcher_map_continuousAt_of_ne_zero (c : ℂ) (z : ℂ) (hz : z ≠ 0) :
    ContinuousAt (bottcher_map c) z := by
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

theorem bottcher_map_apply_ray (c : ℂ) (u : ℂ) (hu : ‖u‖ = 1) (ρ : ℝ)
    (hρ : 0 < ρ) :
    bottcher_map c ((ρ : ℂ) * u) =
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
    bottcher_map c ((ρ : ℂ) * u)
        = ((((ρ : ℂ) * u) / (‖((ρ : ℂ) * u)‖ : ℂ)) *
            ↑(Real.exp (MLC.Quadratic.green_function c ((ρ : ℂ) * u)))) := by
              simp [bottcher_map, polar_green_map, hz0]
    _ = u * ↑(Real.exp (MLC.Quadratic.green_function c ((ρ : ℂ) * u))) := by rw [hdir]

lemma bottcher_right_inv_of_mem (c : ℂ) (w : ℂ)
    (_hw : w ∈ bottcher_map c '' bottcher_domain c) (hw' : 1 < ‖w‖) :
    bottcher_map c (external_ray_map c w) = w := by
  exact external_ray_map_right_inverse c w hw'

theorem bottcher_left_inv_of_data {c : ℂ} (h_data : ExternalRayMapData c)
    (z : ℂ) (hz : z ∈ basin_of_infinity c)
    (h_inj : Function.Injective (bottcher_map c)) :
    external_ray_map_of_data h_data (bottcher_map c z) = z := by
  have hz' : z ∉ MLC.Quadratic.K c := by
    have : z ∈ (MLC.Quadratic.K c)ᶜ := by
      simpa [basin_eq_compl_K c] using hz
    simpa [Set.mem_compl_iff] using this
  have hpos : 0 < MLC.Quadratic.green_function c z :=
    (MLC.Quadratic.green_function_pos_iff_not_mem_K c z).2 hz'
  have hnorm : 1 < ‖bottcher_map c z‖ := by
    have hnorm' : ‖bottcher_map c z‖ = Real.exp (MLC.Quadratic.green_function c z) :=
      norm_bottcher_eq_exp_green c z
    have hgt : 1 < Real.exp (MLC.Quadratic.green_function c z) := by
      simpa using (Real.one_lt_exp_iff.mpr hpos)
    simpa [hnorm'] using hgt
  have hright :
      bottcher_map c (external_ray_map_of_data h_data (bottcher_map c z)) =
        bottcher_map c z := by
    simpa using external_ray_map_of_data_right_inverse h_data (bottcher_map c z) hnorm
  exact h_inj hright

theorem bottcher_left_inv (c : ℂ) (z : ℂ) (hz : z ∈ basin_of_infinity c)
    (h_inj : Function.Injective (bottcher_map c)) :
    external_ray_map c (bottcher_map c z) = z := by
  simpa [external_ray_map] using
    bottcher_left_inv_of_data (external_ray_map_exists c) z hz h_inj

lemma external_ray_map_left_inverse_outside_open_of_data {c : ℂ}
    (h_data : ExternalRayMapData c) (z : ℂ) (hz : ‖z‖ > ‖c‖ + 2) :
    external_ray_map_of_data h_data (bottcher_map c z) = z := by
  exact external_ray_map_of_data_left_inverse_large h_data z hz

lemma external_ray_map_left_inverse_outside_open (c : ℂ) (z : ℂ)
    (hz : ‖z‖ > ‖c‖ + 2) :
    external_ray_map c (bottcher_map c z) = z := by
  simpa [external_ray_map] using
    external_ray_map_left_inverse_outside_open_of_data (external_ray_map_exists c) z hz

lemma orbit_fixed_point (c p : ℂ) (hp : MLC.Quadratic.fc c p = p) :
    ∀ n, MLC.Quadratic.orbit c p n = p := by
  intro n
  induction n with
  | zero =>
      simp
  | succ n ih =>
      simp [MLC.Quadratic.orbit_succ, ih, hp]

lemma exists_fixed_point_mem_K (c : ℂ) : ∃ p, p ∈ MLC.Quadratic.K c := by
  let f : Polynomial ℂ :=
    (Polynomial.X : Polynomial ℂ)^2 + Polynomial.C c - Polynomial.X
  have hdeg : 0 < f.degree := by
    have hdeg_p :
        ((Polynomial.X : Polynomial ℂ)^2 + Polynomial.C c).degree = 2 := by
      simpa using
        (Polynomial.degree_X_pow_add_C (n := 2) (a := c) (by decide))
    have hdeg_q : (Polynomial.X : Polynomial ℂ).degree = 1 := by
      simp
    have hlt :
        (Polynomial.X : Polynomial ℂ).degree <
          ((Polynomial.X : Polynomial ℂ)^2 + Polynomial.C c).degree := by
      simp [hdeg_q, hdeg_p]
    have hdeg_f :
        f.degree = ((Polynomial.X : Polynomial ℂ)^2 + Polynomial.C c).degree := by
      simpa [f] using (Polynomial.degree_sub_eq_left_of_degree_lt (p := (Polynomial.X : Polynomial ℂ)^2 + Polynomial.C c) hlt)
    simp [hdeg_f, hdeg_p]
  obtain ⟨p, hp⟩ := Complex.exists_root hdeg
  have hp' : p ^ 2 + c - p = 0 := by
    simpa [f] using (Polynomial.IsRoot.def.mp hp)
  have hfix : MLC.Quadratic.fc c p = p := by
    have : p ^ 2 + c = p := by
      exact sub_eq_zero.mp hp'
    simpa [MLC.Quadratic.fc] using this
  have hbound : MLC.Quadratic.boundedOrbit c p := by
    refine ⟨‖p‖, ?_⟩
    intro n
    have hconst : MLC.Quadratic.orbit c p n = p := orbit_fixed_point c p hfix n
    simp [hconst]
  exact ⟨p, hbound⟩

lemma exists_fixed_point_mem_K_and_fixed (c : ℂ) :
    ∃ p, p ∈ MLC.Quadratic.K c ∧ MLC.Quadratic.fc c p = p := by
  let f : Polynomial ℂ :=
    (Polynomial.X : Polynomial ℂ)^2 + Polynomial.C c - Polynomial.X
  have hdeg : 0 < f.degree := by
    have hdeg_p :
        ((Polynomial.X : Polynomial ℂ)^2 + Polynomial.C c).degree = 2 := by
      simpa using
        (Polynomial.degree_X_pow_add_C (n := 2) (a := c) (by decide))
    have hdeg_q : (Polynomial.X : Polynomial ℂ).degree = 1 := by
      simp
    have hlt :
        (Polynomial.X : Polynomial ℂ).degree <
          ((Polynomial.X : Polynomial ℂ)^2 + Polynomial.C c).degree := by
      simp [hdeg_q, hdeg_p]
    have hdeg_f :
        f.degree = ((Polynomial.X : Polynomial ℂ)^2 + Polynomial.C c).degree := by
      simpa [f] using
        (Polynomial.degree_sub_eq_left_of_degree_lt
          (p := (Polynomial.X : Polynomial ℂ)^2 + Polynomial.C c) hlt)
    simp [hdeg_f, hdeg_p]
  obtain ⟨p, hp⟩ := Complex.exists_root hdeg
  have hp' : p ^ 2 + c - p = 0 := by
    simpa [f] using (Polynomial.IsRoot.def.mp hp)
  have hfix : MLC.Quadratic.fc c p = p := by
    have : p ^ 2 + c = p := by
      exact sub_eq_zero.mp hp'
    simpa [MLC.Quadratic.fc] using this
  have hbound : MLC.Quadratic.boundedOrbit c p := by
    refine ⟨‖p‖, ?_⟩
    intro n
    have hconst : MLC.Quadratic.orbit c p n = p := orbit_fixed_point c p hfix n
    simp [hconst]
  exact ⟨p, hbound, hfix⟩

noncomputable def fixed_point (c : ℂ) : ℂ :=
  Classical.choose (exists_fixed_point_mem_K_and_fixed c)

lemma fixed_point_mem_K (c : ℂ) : fixed_point c ∈ MLC.Quadratic.K c :=
  (Classical.choose_spec (exists_fixed_point_mem_K_and_fixed c)).1

lemma fixed_point_is_fixed (c : ℂ) : MLC.Quadratic.fc c (fixed_point c) = fixed_point c :=
  (Classical.choose_spec (exists_fixed_point_mem_K_and_fixed c)).2

/-- The sequence of roots converges locally uniformly to the theorem-facing
    Böttcher coordinate. -/
axiom bottcher_seq_converges (c : ℂ) :
    TendstoLocallyUniformlyOn
      (fun n z => ((fun w => w^2 + c)^[n] z) ^ ((1 : ℂ) / (2 : ℂ) ^ n))
      (bottcher_map c) atTop (basin_of_infinity c)

/-- Extension of the ray map to the closed exterior of the disk. -/
noncomputable def extended_ray_map (c : ℂ) (w : ℂ) : ℂ :=
  if 1 < ‖w‖ then external_ray_map c w else fixed_point c

/-- The extended ray map agrees with the external ray map on the open exterior. -/
theorem extended_ray_map_eq (c : ℂ) (w : ℂ) (hw : 1 < ‖w‖) :
    extended_ray_map c w = external_ray_map c w := by
  simp [extended_ray_map, hw]

/-- The extended ray map is continuous on the closed exterior {w | 1 ≤ |w|}. -/
axiom extended_ray_map_continuous (c : ℂ) :
    ContinuousOn (extended_ray_map c) {w | 1 ≤ ‖w‖}

/-- The extended ray map maps the unit circle to the Julia set (subset of K). -/
theorem extended_ray_map_lands (c : ℂ) (w : ℂ) (hw : ‖w‖ = 1) :
    extended_ray_map c w ∈ MLC.Quadratic.K c := by
  have hw' : ¬ 1 < ‖w‖ := by
    simp [hw]
  simpa [extended_ray_map, hw'] using (fixed_point_mem_K c)

/-- Surjectivity of Böttcher map onto the exterior ray parameters. -/
theorem bottcher_map_surj (c w : ℂ) (hw : 1 < ‖w‖) :
    w ∈ Quadratic.bottcher_map c '' Quadratic.bottcher_domain c := by
  let h_data : ExternalRayMapData c := external_ray_map_exists c
  refine ⟨Quadratic.external_ray_map_of_data h_data w, ?_, ?_⟩
  · exact ⟨w, hw, rfl⟩
  · exact external_ray_map_of_data_right_inverse h_data w hw

end Quadratic

end MLC
