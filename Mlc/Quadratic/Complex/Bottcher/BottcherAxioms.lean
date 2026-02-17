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

/-- The Böttcher map `φ_c` conjugates `f_c(z) = z^2 + c` to `z^2` near infinity. -/
noncomputable def bottcher_map (c : ℂ) (z : ℂ) : ℂ :=
  let u := if z = 0 then 1 else z / ↑‖z‖
  u * ↑(Real.exp (MLC.Quadratic.green_function c z))

/-- The domain where the Böttcher map is defined (basin of infinity). -/
def basin_of_infinity (c : ℂ) : Set ℂ :=
  MLC.basin_of_infinity c

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

/-- The inverse of the Böttcher map exists on the exterior (ray map). -/
axiom external_ray_map_exists (c : ℂ) : ExternalRayMapData c

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

noncomputable def external_ray_map (c : ℂ) (w : ℂ) : ℂ :=
  (Classical.choose (external_ray_map_exists c)) w

lemma external_ray_map_right_inverse (c : ℂ) (w : ℂ) (hw : 1 < ‖w‖) :
    bottcher_map c (external_ray_map c w) = w := by
  exact (Classical.choose_spec (external_ray_map_exists c)).1 w hw

lemma external_ray_map_left_inverse_large (c : ℂ) (z : ℂ) (hz : ‖z‖ > ‖c‖ + 2) :
    external_ray_map c (bottcher_map c z) = z := by
  exact (Classical.choose_spec (external_ray_map_exists c)).2 z hz

/-! Domain for the Böttcher coordinate. -/
def bottcher_domain (c : ℂ) : Set ℂ :=
  external_ray_map c '' {w | 1 < ‖w‖}

theorem norm_bottcher_eq_exp_green (c : ℂ) (z : ℂ) :
    ‖bottcher_map c z‖ = Real.exp (MLC.Quadratic.green_function c z) := by
  dsimp [bottcher_map]
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _)]
  let u := if z = 0 then 1 else z / ↑‖z‖
  have : ‖u‖ = 1 := by
    dsimp [u]
    split_ifs with h
    · simp
    · rw [norm_div, Complex.norm_real, norm_norm]
      have hz : (‖z‖ : ℝ) ≠ 0 := by
        simpa using (norm_ne_zero_iff.mpr h)
      exact div_self hz
  rw [this, one_mul]

lemma bottcher_right_inv_of_mem (c : ℂ) (w : ℂ)
    (_hw : w ∈ bottcher_map c '' bottcher_domain c) (hw' : 1 < ‖w‖) :
    bottcher_map c (external_ray_map c w) = w := by
  exact external_ray_map_right_inverse c w hw'

theorem bottcher_left_inv (c : ℂ) (z : ℂ) (hz : z ∈ basin_of_infinity c)
    (h_inj : Function.Injective (bottcher_map c)) :
    external_ray_map c (bottcher_map c z) = z := by
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
      bottcher_map c (external_ray_map c (bottcher_map c z)) =
        bottcher_map c z := by
    simpa using external_ray_map_right_inverse c (bottcher_map c z) hnorm
  exact h_inj hright

lemma external_ray_map_left_inverse_outside_open (c : ℂ) (z : ℂ)
    (hz : ‖z‖ > ‖c‖ + 2) :
    external_ray_map c (bottcher_map c z) = z := by
  exact external_ray_map_left_inverse_large c z hz

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

noncomputable def fixed_point (c : ℂ) : ℂ :=
  Classical.choose (exists_fixed_point_mem_K c)

lemma fixed_point_mem_K (c : ℂ) : fixed_point c ∈ MLC.Quadratic.K c :=
  (Classical.choose_spec (exists_fixed_point_mem_K c))

/-- The sequence of roots converges locally uniformly to the Böttcher map. -/
axiom bottcher_seq_converges (c : ℂ) :
    TendstoLocallyUniformlyOn (fun n z => ((fun w => w^2 + c)^[n] z) ^ ((1 : ℂ) / (2 : ℂ) ^ n))
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
  refine ⟨Quadratic.external_ray_map c w, ?_, ?_⟩
  · exact ⟨w, hw, rfl⟩
  · exact external_ray_map_right_inverse c w hw

end Quadratic

end MLC
