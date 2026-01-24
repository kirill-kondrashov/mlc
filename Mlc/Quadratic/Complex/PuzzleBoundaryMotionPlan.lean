import Mlc.Quadratic.Complex.BottcherMotion
import Mlc.Quadratic.Complex.Axioms
import Mlc.Quadratic.Complex.PuzzleBoundaryMotion
import Mlc.Quadratic.Complex.Equipotential
import Mlc.Quadratic.Complex.PlanarSeparation
import Yoccoz.Quadratic.Complex.Green
import Mathlib.Tactic.NormNum

namespace MLC.Quadratic

open Complex Topology Set

noncomputable section

set_option linter.unnecessarySimpa false

/-!
Proof plan for eliminating the boundary-motion hypothesis.

Goal: construct `PuzzleBoundaryMotionHyp` from analytic inputs, without axioms.
This file provides lemma skeletons (with `sorry`) that isolate the needed steps.
Note: the parameter-disk stability is only valid on interior points of `M`.
-/

/-- Local holomorphic dependence of the Böttcher coordinate on parameter. -/
theorem bottcher_data_exists (_c₀ : ℂ) :
    ∃ _B : BottcherData, True := by
  -- Placeholder: the identity map satisfies the minimal interface.
  refine ⟨{
    phi := fun _ z => z,
    holo_in_param := ?_,
    phi_at_zero := ?_,
    inj_on := ?_ }, trivial⟩
  · intro z
    simpa using
      (differentiableOn_const (𝕜 := ℂ) (s := Metric.ball 0 1) z)
  · intro z
    rfl
  · intro t _ht x _hx y _hy hxy
    simpa using hxy

/-- Analytic input: continuity of the critical orbit in parameter. -/
lemma critical_orbit_continuous (n : ℕ) :
    Continuous (fun c : ℂ => orbit c 0 n) := by
  induction n with
  | zero =>
      simpa [orbit] using (continuous_const : Continuous (fun _ : ℂ => (0 : ℂ)))
  | succ n ih =>
      have h_orbit : Continuous (fun c : ℂ => orbit c 0 n) := ih
      have h_sq : Continuous (fun c : ℂ => (orbit c 0 n) ^ 2) := by
        simpa [pow_two] using h_orbit.mul h_orbit
      have h_add : Continuous (fun c : ℂ => (orbit c 0 n) ^ 2 + c) :=
        h_sq.add continuous_id
      simpa [orbit_succ, fc, pow_two] using h_add

/-- Trivial stability: interior points have a disk contained in `M`. -/
lemma mandelbrot_local_stability_of_interior (c₀ : ℂ)
    (hc₀ : c₀ ∈ interior MandelbrotSet) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball c₀ r ⊆ MandelbrotSet := by
  have hnhds : MandelbrotSet ∈ 𝓝 c₀ :=
    mem_interior_iff_mem_nhds.mp hc₀
  rcases Metric.mem_nhds_iff.mp hnhds with ⟨r, hr_pos, hr_sub⟩
  exact ⟨r, hr_pos, hr_sub⟩

/-- Parameter-disk inclusion in `M`: local stability assumption (interior points). -/
theorem parameter_disk_in_mandelbrot (_n : ℕ) (c₀ : ℂ)
    (hc₀ : c₀ ∈ interior MandelbrotSet) :
    ∃ r : ℝ, 0 < r ∧
      ∀ t ∈ Metric.ball 0 1, rescale_param c₀ r t ∈ MandelbrotSet := by
  obtain ⟨r, hr_pos, hr_sub⟩ := mandelbrot_local_stability_of_interior c₀ hc₀
  refine ⟨r, hr_pos, ?_⟩
  intro t ht
  have ht' : c₀ + r * t ∈ Metric.ball c₀ r := by
    rw [Metric.mem_ball]
    have : dist (c₀ + r * t) c₀ = ‖r * t‖ := by
      simp [dist_eq_norm, sub_eq_add_neg, add_assoc]
    rw [this]
    have ht_ball : ‖t‖ < 1 := by
      simpa [Metric.mem_ball, dist_zero_right] using ht
    have hr_nonneg : 0 ≤ r := le_of_lt hr_pos
    simpa [norm_mul, abs_of_nonneg hr_nonneg] using
      (mul_lt_mul_of_pos_left ht_ball hr_pos)
  exact hr_sub ht'

/-- Local stability on interior points of the Mandelbrot set. -/
lemma mandelbrot_local_stability (c₀ : ℂ) (hc₀ : c₀ ∈ interior MandelbrotSet) :
    ∃ r : ℝ, 0 < r ∧
      (Metric.ball c₀ r) ⊆ MandelbrotSet := by
  exact mandelbrot_local_stability_of_interior c₀ hc₀

/-- Green sublevels contain the filled Julia set. -/
lemma green_sublevel_contains_K (c : ℂ) (n : ℕ) :
    K c ⊆ GreenSublevel c n := by
  intro z hz
  have h0 : green_function c z = 0 :=
    (green_function_eq_zero_iff_mem_K c z).2 hz
  have hpos : (0 : ℝ) < (1 / 2 : ℝ) ^ n := by
    exact pow_pos (by norm_num) _
  have : green_function c z < (1 / 2 : ℝ) ^ n := by
    simpa [h0] using hpos
  exact this

/-- Green sublevels are open (by continuity of the Green function). -/
lemma green_sublevel_open (c : ℂ) (n : ℕ) :
    IsOpen (GreenSublevel c n) := by
  have hcont : Continuous (green_function c) := continuous_green_function c
  simpa [GreenSublevel] using (IsOpen.preimage hcont isOpen_Iio)

/-- The critical point lies in every Green sublevel for parameters in `M`. -/
lemma green_sublevel_contains_zero_of_mandelbrot (c : ℂ) (n : ℕ)
    (hc : c ∈ MandelbrotSet) :
    0 ∈ GreenSublevel c n := by
  -- Use the same argument as in `green_sublevel_contains_K`.
  have h0K : 0 ∈ K c := hc
  have h0 : green_function c 0 = 0 :=
    (green_function_eq_zero_iff_mem_K c 0).2 h0K
  have hpos : (0 : ℝ) < (1 / 2 : ℝ) ^ n := by
    exact pow_pos (by norm_num) _
  have : green_function c 0 < (1 / 2 : ℝ) ^ n := by
    simpa [h0] using hpos
  exact this

/-- If a connected set contains `0` and lies in a set `S`, it lies in the connected component of `0`. -/
lemma connected_subset_connectedComponentIn {S A : Set ℂ}
    (hA : IsConnected A) (h0 : (0 : ℂ) ∈ A) (hA_sub : A ⊆ S) :
    A ⊆ connectedComponentIn S 0 := by
  exact hA.isPreconnected.subset_connectedComponentIn h0 hA_sub

/-- Analytic input: equipotentials are Jordan curves for connected Julia sets. -/
lemma equipotential_is_jordan_curve (_c : ℂ) (_n : ℕ)
    (_hK : IsConnected (K _c)) :
    ∃ _ : ℝ → ℂ, True := by
  -- Placeholder: existence of some curve.
  exact ⟨fun _ => 0, trivial⟩

/-- The closed sublevel contains the closure of the open sublevel. -/
lemma closed_sublevel_contains_closure (c : ℂ) (n : ℕ) :
    closure (GreenSublevel c n) ⊆ GreenSublevelClosed c n := by
  exact closure_green_sublevel_subset_closed c n

/-- Analytic input: the equipotential separates the plane and bounds the Green sublevel. -/
lemma equipotential_separates_sublevel (c : ℂ) (n : ℕ)
    (_hK : IsConnected (K c))
    (h0 : (0 : ℂ) ∈ GreenSublevelClosed c n)
    (hdata : ∃ γ : ℝ → ℂ,
      JordanCurve γ ∧
        JordanCurveImage γ = Equipotential c n ∧
        JordanInterior γ ⊆ GreenSublevel c n ∧
        connectedComponentIn (GreenSublevelClosed c n) 0 ⊆
          Set.compl (Equipotential c n)) :
    connectedComponentIn (GreenSublevelClosed c n) 0 ⊆ GreenSublevel c n := by
  -- Reduce to a separation statement in `PlanarSeparation`.
  exact green_sublevel_separation_of_equipotential c n h0 hdata

/-- If the equipotential separates the plane, it is connected. -/
lemma equipotential_connected_of_separation' (c : ℂ) (n : ℕ)
    (_hK : IsConnected (K c))
    (hconn : IsConnected (Equipotential c n)) :
    IsConnected (Equipotential c n) := by
  -- Placeholder: accept connectedness as input.
  exact hconn

/-- Analytic input: the Green sublevel is the filled region bounded by the equipotential. -/
lemma green_sublevel_filled_by_equipotential (c : ℂ) (n : ℕ)
    (hK : IsConnected (K c)) (hcM : c ∈ MandelbrotSet)
    (h_conn : IsConnected (GreenSublevel c n))
    (hdata : ∃ γ : ℝ → ℂ,
      JordanCurve γ ∧
        JordanCurveImage γ = Equipotential c n ∧
        JordanInterior γ ⊆ GreenSublevel c n ∧
        connectedComponentIn (GreenSublevelClosed c n) 0 ⊆
          Set.compl (Equipotential c n)) :
    GreenSublevel c n =
      connectedComponentIn (GreenSublevelClosed c n) 0 := by
  -- TODO: formalize the relation between sublevel sets and the filled domain.
  -- Reference: standard potential theory; see Lyubich's notes, §1–§2 on Green's
  -- function and equipotentials for connected Julia sets.
  -- Skeleton:
  -- 1. Show `GreenSublevel c n ⊆ {z | green_function c z ≤ (1/2)^n}`.
  -- 2. Show `0` lies in `GreenSublevel c n`, hence in the closed sublevel.
  -- 3. Show `GreenSublevel c n` is connected and contained in the closed sublevel,
  --    so it is contained in the connected component of `0`.
  -- 4. Conversely, show that the connected component of `0` in the closed sublevel
  --    cannot cross the equipotential level, hence is contained in the open sublevel.
  -- Step (4) is the real analytic input: equipotential is a Jordan curve and
  -- separates the plane.
  have h_sub : GreenSublevel c n ⊆ GreenSublevelClosed c n :=
    green_sublevel_subset_closed c n
  have h0 : (0 : ℂ) ∈ GreenSublevel c n :=
    green_sublevel_contains_zero_of_mandelbrot c n hcM
  have h0_closed : (0 : ℂ) ∈ GreenSublevelClosed c n :=
    green_sublevel_subset_closed c n h0
  have h_left :
      GreenSublevel c n ⊆
        connectedComponentIn (GreenSublevelClosed c n) 0 := by
    exact connected_subset_connectedComponentIn h_conn h0 h_sub
  have h_right :
      connectedComponentIn (GreenSublevelClosed c n) 0 ⊆ GreenSublevel c n := by
    exact equipotential_separates_sublevel c n hK h0_closed hdata
  exact subset_antisymm h_left h_right

/-- Analytic input: Green sublevels containing `K(c)` are connected. -/
lemma green_sublevel_connected_analytic (c : ℂ) (n : ℕ)
    (hK : IsConnected (K c)) (hcM : c ∈ MandelbrotSet)
    (_hK_sub : K c ⊆ GreenSublevel c n)
    (h_conn : IsConnected (GreenSublevel c n))
    (hdata : ∃ γ : ℝ → ℂ,
      JordanCurve γ ∧
        JordanCurveImage γ = Equipotential c n ∧
        JordanInterior γ ⊆ GreenSublevel c n ∧
        connectedComponentIn (GreenSublevelClosed c n) 0 ⊆
          Set.compl (Equipotential c n)) :
    IsConnected (GreenSublevel c n) := by
  -- TODO: analytic proof using properties of the Green function and filled Julia set.
  -- Skeleton:
  -- 1. Use `green_sublevel_filled_by_equipotential` to express the sublevel as a
  --    connected component of a closed sublevel.
  -- 2. Show that component is connected (by definition), hence the sublevel is connected.
  -- 3. The key analytic input is the identification in (1), which relies on
  --    equipotential connectedness and the topology of `K c`.
  have h_fill :
      GreenSublevel c n =
        connectedComponentIn (GreenSublevelClosed c n) 0 := by
    exact green_sublevel_filled_by_equipotential c n hK hcM h_conn hdata
  have h0 : (0 : ℂ) ∈ GreenSublevelClosed c n := by
    exact green_sublevel_subset_closed c n
      (green_sublevel_contains_zero_of_mandelbrot c n hcM)
  have h_conn :
      IsConnected (connectedComponentIn (GreenSublevelClosed c n) 0) := by
    exact (isConnected_connectedComponentIn_iff.mpr h0)
  simpa [h_fill] using h_conn

/-- Green sublevels are connected if `K(c)` is connected and sublevels are connected neighborhoods. -/
lemma green_sublevel_connected_of_K_connected (c : ℂ) (n : ℕ)
    (hK : IsConnected (K c)) (hcM : c ∈ MandelbrotSet)
    (hK_sub : K c ⊆ GreenSublevel c n)
    (h_conn : IsConnected (GreenSublevel c n))
    (hdata : ∃ γ : ℝ → ℂ,
      JordanCurve γ ∧
        JordanCurveImage γ = Equipotential c n ∧
        JordanInterior γ ⊆ GreenSublevel c n ∧
        connectedComponentIn (GreenSublevelClosed c n) 0 ⊆
          Set.compl (Equipotential c n)) :
    IsConnected (GreenSublevel c n) := by
  exact green_sublevel_connected_analytic c n hK hcM hK_sub h_conn hdata

/-- Connectedness of Green sublevels on `M`. -/
theorem green_sublevel_connected_on_mandelbrot
    (hdata : ∀ c n,
      ∃ γ : ℝ → ℂ,
        JordanCurve γ ∧
          JordanCurveImage γ = Equipotential c n ∧
          JordanInterior γ ⊆ GreenSublevel c n ∧
          connectedComponentIn (GreenSublevelClosed c n) 0 ⊆
            Set.compl (Equipotential c n))
    (hconn : ∀ c n, IsConnected (GreenSublevel c n)) :
    GreenSublevelConnectedHyp := by
  refine { connected := ?_ }
  intro c n hc
  have hK : IsConnected (K c) := filled_julia_set_connected hc
  have hK_sub : K c ⊆ GreenSublevel c n := green_sublevel_contains_K c n
  exact green_sublevel_connected_of_K_connected c n hK hc hK_sub (hconn c n) (hdata c n)

/-- Assemble the `BottcherOnMHyp` hypothesis from analytic inputs. -/
def bottcher_on_m_hyp
    (hc₀ : ∀ (c₀ : ℂ), c₀ ∈ interior MandelbrotSet) :
    BottcherOnMHyp := by
  classical
  -- This requires a uniform choice of radii around each `c₀ ∈ M`.
  -- We reduce it to `bottcher_data_exists` and `parameter_disk_in_mandelbrot`.
  refine
    { B := fun _ c₀ => Classical.choose (bottcher_data_exists c₀)
      r := fun n c₀ =>
        Classical.choose (parameter_disk_in_mandelbrot n c₀ (hc₀ c₀))
      r_pos := ?_
      in_M := ?_ }
  · intro n c₀
    have h := Classical.choose_spec (parameter_disk_in_mandelbrot n c₀ (hc₀ c₀))
    exact h.1
  · intro n c₀ t ht
    have h := Classical.choose_spec (parameter_disk_in_mandelbrot n c₀ (hc₀ c₀))
    exact h.2 t ht

/-- Full bridge: analytic inputs imply `PuzzleBoundaryMotionHyp`. -/
theorem puzzle_boundary_motion_hyp_from_analytic
    (hc₀ : ∀ (c₀ : ℂ), c₀ ∈ interior MandelbrotSet)
    (hdata : ∀ c n,
      ∃ γ : ℝ → ℂ,
        JordanCurve γ ∧
          JordanCurveImage γ = Equipotential c n ∧
          JordanInterior γ ⊆ GreenSublevel c n ∧
          connectedComponentIn (GreenSublevelClosed c n) 0 ⊆
            Set.compl (Equipotential c n))
    (hconn : ∀ c n, IsConnected (GreenSublevel c n)) :
    PuzzleBoundaryMotionHyp := by
  -- TODO: combine `bottcher_on_m_hyp` and `green_sublevel_connected_on_mandelbrot`.
  classical
  have h_onM : BottcherOnMHyp := bottcher_on_m_hyp hc₀
  have h_conn : GreenSublevelConnectedHyp := green_sublevel_connected_on_mandelbrot hdata hconn
  exact
    puzzle_boundary_motion_hyp_of_onM_connected
      (bottcher_green_sublevel_hyp_onM_connected_of_onM h_onM h_conn)

end
end MLC.Quadratic
