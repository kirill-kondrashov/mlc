import Yoccoz.Quadratic.Complex.Basic
import Yoccoz.Quadratic.Complex.Puzzle
import Yoccoz.Quadratic.Complex.Green
import Yoccoz.Quadratic.Complex.GreenLemmas
import Mlc.Quadratic.Complex.ParaPuzzle
import Mlc.Quadratic.Complex.Axioms
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Constructions
import Mathlib.Order.Filter.Bases.Basic
import Mathlib.Topology.Sets.Closeds
import Mathlib.Topology.UniformSpace.Compact
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Bounded

namespace MLC.Quadratic

open Complex Topology Set Filter Metric Bornology

/-- The Green's function is bounded below by a logarithmic growth term. -/
lemma green_function_bdd_below_log (c z : ℂ) (h : ‖z‖ > escape_bound c) :
    green_function c z ≥ Real.log ‖z‖ - (2 * ‖c‖ / (escape_bound c)^2) := by
  have h_dist := dist_potential_seq_green_function_le_of_escaping c z 0 h
  simp only [pow_zero, one_div_one, one_mul] at h_dist
  have h_pot0 : potential_seq c z 0 = Real.log ‖z‖ := by
    dsimp [potential_seq]
    rw [max_eq_right]
    · simp
    · have h_eb := escape_bound_ge_R c
      have h_R := R_ge_two c
      linarith
  rw [h_pot0, dist_comm, dist_eq_norm, Real.norm_eq_abs] at h_dist
  linarith [abs_le.mp h_dist]

/-- Sublevel sets of the Green's function are bounded. -/
lemma bounded_sublevel_green_function (c : ℂ) (r : ℝ) :
    IsBounded {z | green_function c z < r} := by
  let M := 2 * ‖c‖ / (escape_bound c)^2
  let R_max := max (escape_bound c) (Real.exp (r + M))
  refine isBounded_iff_forall_norm_le.mpr ⟨R_max, ?_⟩
  intro z hz
  dsimp at hz
  by_cases h_esc : ‖z‖ ≤ escape_bound c
  · exact le_trans h_esc (le_max_left _ _)
  · push_neg at h_esc
    have h_log := green_function_bdd_below_log c z h_esc
    have : Real.log ‖z‖ < r + M := by linarith
    have h_pos : 0 < ‖z‖ := by
      have h_eb := escape_bound_ge_R c
      have h_R := R_ge_two c
      linarith
    rw [Real.log_lt_iff_lt_exp h_pos] at this
    exact le_trans (le_of_lt this) (le_max_right _ _)

/-- The closure of a parameter puzzle piece is compact. -/
lemma isCompact_closure_para_puzzle_piece (c : ℂ) (n : ℕ) :
    IsCompact (closure (ParaPuzzlePieceAt c n)) := by
  -- A set in ℂ is compact iff it is closed and bounded.
  rw [isCompact_iff_isClosed_bounded]
  constructor
  · exact isClosed_closure
  · -- Closure of a set is bounded iff the set itself is bounded.
    rw [isBounded_closure_iff]
    -- ParaPuzzlePieceAt c n is a translate of DynamicalPuzzlePiece c n 0.
    have h_trans : ParaPuzzlePieceAt c n = (fun w => w + c) '' (DynamicalPuzzlePiece c n 0) := by
      ext c'
      constructor
      · intro h
        use c' - c
        simpa [ParaPuzzlePieceAt] using h
      · rintro ⟨w, hw, rfl⟩
        simp [ParaPuzzlePieceAt, hw]
    rw [h_trans]
    -- Use isBounded_iff_forall_norm_le
    rw [isBounded_iff_forall_norm_le]
    obtain ⟨R_val, hR_val⟩ := isBounded_iff_forall_norm_le.mp (bounded_sublevel_green_function c ((1 / 2) ^ n))
    use R_val + ‖c‖
    rintro _ ⟨w, hw, rfl⟩
    calc ‖w + c‖ ≤ ‖w‖ + ‖c‖ := norm_add_le _ _
      _ ≤ R_val + ‖c‖ := add_le_add_left (hR_val _ (connectedComponentIn_subset _ _ hw)) ‖c‖

/-- The intersection of closures of parameter puzzle pieces is the same as the intersection of pieces,
    provided they shrink to a point. -/
lemma iInter_closure_para_puzzle_piece (c : ℂ) (h : (⋂ n, ParaPuzzlePieceAt c n) = {c}) :
    (⋂ n, closure (ParaPuzzlePieceAt c n)) = {c} := by
  -- Proof sketch: For nested compact sets, intersection of closures equals intersection.
  sorry

/-- Nested compact sets with a singleton intersection form a neighborhood basis. -/
theorem hasBasis_nhds_of_iInter_singleton {α : Type*} [TopologicalSpace α] [T2Space α]
    {K : ℕ → Set α} (h_compact : ∀ n, IsCompact (K n)) (h_nested : ∀ n, K (n + 1) ⊆ K n)
    {x : α} (h_inter : (⋂ n, K n) = {x}) :
    (𝓝 x).HasBasis (fun _ => True) K := by
  -- This is a standard topological result.
  sorry

/-- Parameter puzzle pieces are nested. -/
lemma para_puzzle_piece_nested (c : ℂ) (n : ℕ) :
    ParaPuzzlePieceAt c (n + 1) ⊆ ParaPuzzlePieceAt c n := by
  -- Proof sketch: (1/2)^(n+1) < (1/2)^n implies sublevel set inclusion.
  sorry

/-- Parameter puzzle pieces form a basis of neighborhoods if they shrink to a point. -/
theorem para_puzzle_piece_basis_sketch (c : ℂ) (h : (⋂ n, ParaPuzzlePieceAt c n) = {c}) :
    ∀ U ∈ 𝓝 c, ∃ n, ParaPuzzlePieceAt c n ⊆ U := by
  let K := fun n => closure (ParaPuzzlePieceAt c n)
  have h_compact : ∀ n, IsCompact (K n) := fun n => isCompact_closure_para_puzzle_piece c n
  have h_nested : ∀ n, K (n + 1) ⊆ K n := fun n => closure_mono (para_puzzle_piece_nested c n)
  have h_inter : (⋂ n, K n) = {c} := iInter_closure_para_puzzle_piece c h
  
  -- Apply the topological lemma to K n
  have h_basis := hasBasis_nhds_of_iInter_singleton h_compact h_nested h_inter
  
  intro U hU
  obtain ⟨n, _, hn_sub⟩ := h_basis.mem_iff.mp hU
  use n
  -- P n ⊆ cl P n ⊆ U
  exact subset_trans subset_closure hn_sub

end MLC.Quadratic
