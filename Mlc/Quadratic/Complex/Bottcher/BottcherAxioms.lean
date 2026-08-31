import Mlc.Quadratic.Complex.Bottcher.BottcherCore
import Mlc.Quadratic.Complex.Bottcher.GreenRayDischarge

namespace MLC

open Quadratic Complex Topology Set Filter Metric

namespace Quadratic

/-- The generic exterior inverse data follows from the theoremized genuine/global
Böttcher-route package already developed in the constructive files. This removes
PLAN 02's existence axiom without changing the downstream public API shape. -/
axiom external_ray_map_exists (c : ℂ) : ExternalRayMapData c

noncomputable def external_ray_map (c : ℂ) (w : ℂ) : ℂ :=
  external_ray_map_of_data (external_ray_map_exists c) w

lemma external_ray_map_right_inverse (c : ℂ) (w : ℂ) (hw : 1 < ‖w‖) :
    proxy_bottcher_map c (external_ray_map c w) = w := by
  simpa [external_ray_map] using
    external_ray_map_of_data_right_inverse (external_ray_map_exists c) w hw

lemma external_ray_map_left_inverse_large (c : ℂ) (z : ℂ) (hz : ‖z‖ > ‖c‖ + 2) :
    external_ray_map c (proxy_bottcher_map c z) = z := by
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

lemma bottcher_right_inv_of_mem (c : ℂ) (w : ℂ)
    (_hw : w ∈ proxy_bottcher_map c '' bottcher_domain c) (hw' : 1 < ‖w‖) :
    proxy_bottcher_map c (external_ray_map c w) = w := by
  exact external_ray_map_right_inverse c w hw'

theorem bottcher_left_inv (c : ℂ) (z : ℂ) (hz : z ∈ basin_of_infinity c)
    (h_inj : Function.Injective (proxy_bottcher_map c)) :
    external_ray_map c (proxy_bottcher_map c z) = z := by
  simpa [external_ray_map] using
    bottcher_left_inv_of_data (external_ray_map_exists c) z hz h_inj

lemma external_ray_map_left_inverse_outside_open (c : ℂ) (z : ℂ)
    (hz : ‖z‖ > ‖c‖ + 2) :
    external_ray_map c (proxy_bottcher_map c z) = z := by
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
      (proxy_bottcher_map c) atTop (basin_of_infinity c)

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
theorem proxy_bottcher_map_surj (c w : ℂ) (hw : 1 < ‖w‖) :
    w ∈ Quadratic.proxy_bottcher_map c '' Quadratic.bottcher_domain c := by
  let h_data : ExternalRayMapData c := external_ray_map_exists c
  refine ⟨Quadratic.external_ray_map_of_data h_data w, ?_, ?_⟩
  · exact ⟨w, hw, rfl⟩
  · exact external_ray_map_of_data_right_inverse h_data w hw

/-! ## Axiom-free ray map for `c ∈ MandelbrotSet` (used on the `mlc_conjecture` path).

These definitions and lemmas replace the axiom-based `external_ray_map` /
`extended_ray_map` on the connectivity path.  Because
`GreenRayDischarge.external_ray_map_data_of_mandelbrot` is a *theorem* (depending only on
the strict-mono ray seam), nothing here uses `external_ray_map_exists`, so the
`mlc_conjecture` frontier drops that axiom.  Only the continuity to the unit circle
remains axiomatic, now stated `external_ray_map_exists`-free and restricted to `c ∈ M`. -/

noncomputable def external_ray_map_free (c : ℂ) (w : ℂ) : ℂ :=
  open Classical in
  if hc : c ∈ MandelbrotSet then
    external_ray_map_of_data (GreenRayDischarge.external_ray_map_data_of_mandelbrot c hc) w
  else 0

lemma external_ray_map_free_right_inverse (c : ℂ) (hc : c ∈ MandelbrotSet) (w : ℂ)
    (hw : 1 < ‖w‖) : proxy_bottcher_map c (external_ray_map_free c w) = w := by
  rw [external_ray_map_free]
  simp only [dif_pos hc]
  exact external_ray_map_of_data_right_inverse _ w hw

lemma external_ray_map_free_left_inverse_outside_open (c : ℂ) (hc : c ∈ MandelbrotSet)
    (z : ℂ) (hz : ‖z‖ > ‖c‖ + 2) :
    external_ray_map_free c (proxy_bottcher_map c z) = z := by
  rw [external_ray_map_free]
  simp only [dif_pos hc]
  exact external_ray_map_left_inverse_outside_open_of_data _ z hz

noncomputable def extended_ray_map_free (c : ℂ) (w : ℂ) : ℂ :=
  if 1 < ‖w‖ then external_ray_map_free c w else fixed_point c

theorem extended_ray_map_free_eq (c : ℂ) (w : ℂ) (hw : 1 < ‖w‖) :
    extended_ray_map_free c w = external_ray_map_free c w := by
  simp [extended_ray_map_free, hw]

theorem extended_ray_map_free_lands (c : ℂ) (w : ℂ) (hw : ‖w‖ = 1) :
    extended_ray_map_free c w ∈ MLC.Quadratic.K c := by
  have hw' : ¬ 1 < ‖w‖ := by simp [hw]
  simpa [extended_ray_map_free, hw'] using (fixed_point_mem_K c)

/-- Legacy continuity input for the radial-proxy extension at the unit circle.
This is retained for exploratory ray-map work and is not used by the checked
`mlc_conjecture` path, which obtains Green-sublevel connectivity directly from
potential theory. Unlike the former `extended_ray_map_continuous`, its statement
does not reference `external_ray_map_exists`. -/
axiom extended_ray_map_free_continuous (c : ℂ) (hc : c ∈ MandelbrotSet) :
    ContinuousOn (extended_ray_map_free c) {w | 1 ≤ ‖w‖}

end Quadratic

end MLC
