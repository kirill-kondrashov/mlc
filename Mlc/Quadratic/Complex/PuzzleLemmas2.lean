import Mlc.Quadratic.Complex.Basic
import Mlc.Quadratic.Complex.Groetzsch
import Mlc.Quadratic.Complex.Green
import Mlc.CheckAxioms
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Constructions
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.GCongr
import Mlc.Quadratic.Complex.Puzzle
import Mlc.Quadratic.Complex.PuzzleLemmas

namespace MLC.Quadratic

open Complex Topology Filter Set

noncomputable section

variable (c : ℂ)

/-- Correspondence between parameter and dynamical pieces. -/
lemma para_dynamical_correspondence (c : ℂ) (n : ℕ) :
    c ∈ ParaPuzzlePiece n ↔ fc c 0 ∈ DynamicalPuzzlePiece c n 0 := by
  simp [ParaPuzzlePiece, fc]

/-- The Correspondence Principle:
    If the dynamical pieces shrink to a point, the parameter pieces shrink to a point. -/
lemma parameter_shrink_ax (c : ℂ) :
    (⋂ n, DynamicalPuzzlePiece c n 0) = {0} → (⋂ n, ParaPuzzlePiece n) = {c} := by
  intro h_shrink
  by_cases hc : c ∈ MandelbrotSet
  · -- Case c ∈ M
    have h_K_sub : K c ⊆ {0} := by
      rw [← h_shrink]
      apply subset_iInter
      intro n
      have h_K_subset : K c ⊆ {w | green_function c w < (1 / 2) ^ n} := by
        intro z hz
        rw [mem_setOf_eq]
        rw [← green_function_eq_zero_iff_mem_K] at hz
        rw [hz]
        apply pow_pos
        norm_num
      have h_0_in_K : 0 ∈ K c := hc
      apply (filled_julia_set_connected hc).isPreconnected.subset_connectedComponentIn h_0_in_K h_K_subset

    have hc_in_K : c ∈ K c := by
      rw [K, MandelbrotSet] at *
      unfold boundedOrbit at *
      obtain ⟨M, hM⟩ := hc
      use max M ‖c‖
      intro n
      cases n with
      | zero => simp
      | succ n =>
        simp only [orbit_succ]
        have h_shift : orbit c c n = orbit c 0 (n + 1) := by
          induction n with
          | zero => simp [orbit, fc]
          | succ n ih => simp [orbit_succ, ih]
        rw [h_shift]
        rw [← orbit_succ]
        apply le_trans (hM (n + 2)) (le_max_left _ _)

    have hc_eq_0 : c = 0 := h_K_sub hc_in_K
    subst hc_eq_0
    have h1_in_K : 1 ∈ K 0 := by
      rw [K]
      use 1
      intro n
      have : orbit 0 1 n = 1 := by
        induction n with
        | zero => simp
        | succ n ih => simp [orbit_succ, fc, ih]
      rw [this]
      norm_num
    have h1_eq_0 : (1 : ℂ) = 0 := by
      have : (1 : ℂ) ∈ ({0} : Set ℂ) := h_K_sub h1_in_K
      rw [Set.mem_singleton_iff] at this
      exact this
    exfalso
    exact one_ne_zero h1_eq_0

  · -- Case c ∉ M
    have h_empty : (⋂ n, DynamicalPuzzlePiece c n 0) = ∅ := by
      obtain ⟨N, hN⟩ := dynamical_puzzle_piece_empty_of_large_n c hc
      apply Set.eq_empty_of_subset_empty
      intro x hx
      rw [mem_iInter] at hx
      have hxN := hx N
      have h0_in_s : 0 ∈ {w | green_function c w < (1 / 2) ^ N} := by
        dsimp [DynamicalPuzzlePiece] at hxN
        by_contra h_not
        rw [connectedComponentIn_eq_empty h_not] at hxN
        exact hxN
      have h0_not_in_comp : 0 ∉ DynamicalPuzzlePiece c N 0 := hN N (le_refl N)
      dsimp [DynamicalPuzzlePiece] at h0_not_in_comp
      have h0_in_comp : 0 ∈ connectedComponentIn {w | green_function c w < (1 / 2) ^ N} 0 := by
        apply isPreconnected_singleton.subset_connectedComponentIn (mem_singleton 0)
        · rw [singleton_subset_iff]; exact h0_in_s
        · exact mem_singleton 0
      contradiction

    rw [h_empty] at h_shrink
    simp at h_shrink

ensure_no_sorry parameter_shrink_ax

set_option maxHeartbeats 1600000

/-- Parameter puzzle pieces are open sets.
    See: [Lyubich, The Dynamics of Quadratic Polynomials I-II, Acta Math. 178 (1997), Lemma 3.1] <https://projecteuclid.org/journals/acta-mathematica/volume-178/issue-2/Dynamics-of-quadratic-polynomials-III/10.1007/BF02392694.full>
    Local Reference: `refs/Conformal Geometry and Dynamics of Quadratic Polynomials.pdf` -/
axiom para_puzzle_piece_open (n : ℕ) : IsOpen (ParaPuzzlePiece n)

/-- Parameter puzzle pieces form a basis of neighborhoods if they shrink to a point. -/
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

/-- Parameter puzzle pieces intersected with the Mandelbrot set are connected. -/
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
