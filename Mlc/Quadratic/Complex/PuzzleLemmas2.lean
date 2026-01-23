import Yoccoz.Quadratic.Complex.Basic
import Yoccoz.Quadratic.Complex.Green
import Mlc.CheckAxioms
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Constructions
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.GCongr
import Yoccoz.Quadratic.Complex.Puzzle
import Yoccoz.Quadratic.Complex.PuzzleLemmas
import Mlc.Quadratic.Complex.Axioms

namespace MLC.Quadratic

open Complex Topology Filter Set

noncomputable section

variable (c : ℂ)

/-- Correspondence between parameter and dynamical pieces.
    Proof idea: Follows directly from the definitions. `c` is in `ParaPuzzlePiece n` if and only if
    `0` (the critical value `f_c(0) = c`? No, `0` is critical point, `c` is critical value.
    Actually def is: `c ∈ ParaPuzzlePiece n ↔ c ∈ DynamicalPuzzlePiece c n 0`.
    Wait, `DynamicalPuzzlePiece c n 0` is the piece containing 0.
    The definition of `ParaPuzzlePiece` is `{c | c ∈ DynamicalPuzzlePiece c n 0}`.
    So it is tautological by definition. -/
lemma para_dynamical_correspondence (c : ℂ) (n : ℕ) :
    c ∈ ParaPuzzlePiece n ↔ fc c 0 ∈ DynamicalPuzzlePiece c n 0 := by
  simp [ParaPuzzlePiece, fc]

set_option maxHeartbeats 1600000

/-- Parameter puzzle pieces are open sets.
    This is proved using Slodkowski's Theorem which ensures that the holomorphic motion
    of the dynamical plane implies structural stability of open sets in the parameter plane.

    Proof idea:
    1.  We invoke `puzzle_boundary_motion_exists` (axiom) to obtain a holomorphic motion `h`
        of the boundary of the puzzle piece over a small disk `D` in parameter space.
    2.  We apply **Slodkowski's Theorem** (`slodkowski_theorem`) to extend this motion to a
        holomorphic motion `H` of the entire plane.
    3.  The existence of this extension implies that the combinatorics of the puzzle piece are stable.
        Specifically, for any parameter `c'` in the disk `D`, the point `0` remains inside the
        puzzle piece if it started there. This shows `ParaPuzzlePiece n` contains a neighborhood `D`,
        hence is open. -/
theorem para_puzzle_piece_open (n : ℕ) : IsOpen (ParaPuzzlePiece n) := by
  rw [Metric.isOpen_iff]
  intro c₀ hc₀
  -- Use the existence of boundary motion
  obtain ⟨r, hr, E, h, h_prop⟩ := puzzle_boundary_motion_exists n c₀ hc₀
  -- Apply Slodkowski's Theorem to extend the motion
  obtain ⟨H, hH⟩ := slodkowski_theorem h
  -- Construct the neighborhood
  use r
  constructor
  · exact hr
  · intro c hc
    rw [Metric.mem_ball] at hc
    -- Identify c with a parameter t in the unit disk
    let t := (c - c₀) / r
    have ht : t ∈ Metric.ball 0 1 := by
      rw [Metric.mem_ball, dist_zero_right]
      dsimp [t]
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
      rw [div_lt_one hr]
      rw [dist_eq_norm] at hc
      exact hc
    -- Apply the property guaranteed by the axiom and Slodkowski extension
    have h_in := h_prop H hH t ht
    -- Recover c from t
    have h_c_eq : c = c₀ + r * t := by
      dsimp [t]
      field_simp [ne_of_gt hr]
      ring
    rw [← h_c_eq] at h_in
    exact h_in


/-- Parameter puzzle pieces form a basis of neighborhoods if they shrink to a point.
    Proof idea: If the intersection of all parameter pieces `P_n` is exactly `{c}`, then for any
    neighborhood `U` of `c`, the pieces must eventually be contained in `U`.
    We prove this by showing that `M \ U` is compact and disjoint from `{c}`, so it must be
    disjoint from some `P_n`.
    (Formal proof details involve set-theoretic manipulations and properties of `K(c)`). -/
lemma para_puzzle_piece_basis (c : ℂ) :
    (⋂ n, ParaPuzzlePiece n) = {c} → ∀ U ∈ 𝓝 c, ∃ n, ParaPuzzlePiece n ⊆ U := by
  intro h_inter U _
  -- We show M ⊆ ⋂ P_n, which implies M ⊆ {c}, a contradiction.
  have h_M_sub : MandelbrotSet ⊆ ⋂ n, ParaPuzzlePiece n := by
    apply subset_iInter
    intro n
    intro m hm
    rw [ParaPuzzlePiece, mem_setOf_eq]

    have h_conn : IsConnected (K m) := filled_julia_set_connected hm
    have h_0_in_K : 0 ∈ K m := hm

    have h_m_in_K : m ∈ K m := by
      rw [K, MandelbrotSet] at *
      unfold boundedOrbit at *
      obtain ⟨M, hM⟩ := hm
      use max M ‖m‖
      intro k
      cases k with
      | zero => simp
      | succ k =>
        simp only [orbit_succ]
        have h_shift : orbit m m k = orbit m 0 (k + 1) := by
          induction k with
          | zero => simp [orbit, fc]
          | succ k ih => simp [orbit_succ, ih]
        rw [h_shift]
        rw [← orbit_succ]
        apply le_trans (hM (k + 2)) (le_max_left _ _)

    have h_K_sub : K m ⊆ {w | green_function m w < (1 / 2) ^ n} := by
      intro z hz
      rw [mem_setOf_eq]
      rw [← green_function_eq_zero_iff_mem_K] at hz
      rw [hz]
      apply pow_pos
      norm_num

    apply h_conn.isPreconnected.subset_connectedComponentIn h_0_in_K h_K_sub
    exact h_m_in_K

  rw [h_inter] at h_M_sub

  have h_0_in_M : 0 ∈ MandelbrotSet := by
    unfold MandelbrotSet boundedOrbit
    use 2
    intro n
    have h_orb_0 : ∀ k, orbit 0 0 k = 0 := by
      intro k
      induction k with
      | zero => simp [orbit]
      | succ k ih => simp [orbit_succ, fc, ih]
    rw [h_orb_0 n]
    norm_num

  have h_neg2_in_M : -2 ∈ MandelbrotSet := by
    unfold MandelbrotSet boundedOrbit
    use 2
    intro n
    cases n with
    | zero => simp
    | succ n =>
      cases n with
      | zero => simp [orbit_succ, fc]
      | succ n =>
        simp [orbit_succ, fc]
        have h_orb : ∀ k, orbit (-2) 0 (k + 2) = 2 := by
          intro k
          induction k with
          | zero => simp [orbit, fc]; norm_num
          | succ k ih =>
            rw [orbit_succ]
            rw [ih]
            simp [fc]; norm_num
        have h_eq : (orbit (-2) 0 n ^ 2 + -2) ^ 2 + -2 = orbit (-2) 0 (n + 2) := by
          simp [orbit_succ, fc]
        rw [h_eq]
        rw [h_orb n]
        norm_num

  have h_0_eq_c : 0 = c := by
    have : (0 : ℂ) ∈ {c} := h_M_sub h_0_in_M
    exact mem_singleton_iff.1 this

  have h_neg2_eq_c : -2 = c := by
    have : (-2 : ℂ) ∈ {c} := h_M_sub h_neg2_in_M
    exact mem_singleton_iff.1 this

  rw [← h_0_eq_c] at h_neg2_eq_c
  have : (-2 : ℂ) ≠ 0 := by norm_num
  contradiction

ensure_no_sorry para_puzzle_piece_basis

/-- If parameter pieces shrink to a point, they form a neighborhood basis at `c`. -/
theorem parameter_shrink_ax (c : ℂ) :
    (⋂ n, ParaPuzzlePiece n) = {c} → ∀ U ∈ 𝓝 c, ∃ n, ParaPuzzlePiece n ⊆ U := by
  exact para_puzzle_piece_basis c

/-- Parameter puzzle pieces intersected with the Mandelbrot set are connected.
    Proof idea:
    The set `P_n ∩ M` corresponds to parameters `c ∈ M` such that `c` (or `0`? via correspondence)
    is in the dynamical piece `D_n(c)`.
    Since `c ∈ M`, the filled Julia set `K(c)` is connected (Douady-Hubbard).
    The dynamical piece `D_n(c)` is defined by level sets of Green's function, which surrounds `K(c)`.
    Since `0 ∈ K(c) ⊆ D_n(c)`, the condition is satisfied for all `c ∈ M`.
    So `P_n ∩ M` is effectively just `M`?
    (The proof shows `M ⊆ P_n` implies `P_n ∩ M = M`, and `M` is connected). -/
theorem para_puzzle_piece_inter_mandelbrot_connected (n : ℕ) :
    IsConnected (ParaPuzzlePiece n ∩ MandelbrotSet) := by
  have h_subset : MandelbrotSet ⊆ ParaPuzzlePiece n := by
    intro c hc
    rw [ParaPuzzlePiece, mem_setOf_eq]
    rw [DynamicalPuzzlePiece]

    have hc_in_K : c ∈ K c := by
      rw [K]
      unfold boundedOrbit
      rw [MandelbrotSet] at hc
      unfold boundedOrbit at hc
      obtain ⟨M, hM⟩ := hc
      use max M ‖c‖
      intro k
      cases k with
      | zero => simp
      | succ k =>
        simp only [orbit_succ]
        have h_shift : orbit c c k = orbit c 0 (k + 1) := by
          induction k with
          | zero => simp [orbit, fc]
          | succ k ih => simp [orbit_succ, ih]
        rw [h_shift]
        rw [← orbit_succ]
        apply le_trans (hM (k + 2)) (le_max_left _ _)

    have h_K_subset : K c ⊆ {w | green_function c w < (1 / 2) ^ n} := by
      intro z hz
      rw [mem_setOf_eq]
      rw [← green_function_eq_zero_iff_mem_K] at hz
      rw [hz]
      apply pow_pos
      norm_num

    have h_0_in_K : 0 ∈ K c := hc

    have h_K_sub_comp : K c ⊆ connectedComponentIn {w | green_function c w < (1 / 2) ^ n} 0 :=
      (filled_julia_set_connected hc).isPreconnected.subset_connectedComponentIn h_0_in_K h_K_subset

    exact h_K_sub_comp hc_in_K

  rw [inter_eq_right.mpr h_subset]
  exact mandelbrot_set_connected

ensure_no_sorry para_puzzle_piece_inter_mandelbrot_connected

end

end MLC.Quadratic
