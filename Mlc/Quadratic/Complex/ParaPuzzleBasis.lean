import Mathlib.Topology.Order
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Connected.LocallyConnected
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

lemma complex_locally_connected : LocallyConnectedSpace ℂ := inferInstance

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
axiom isCompact_closure_para_puzzle_piece (c : ℂ) (n : ℕ) :
    IsCompact (closure (ParaPuzzlePieceAt c n))

/-- Parameter puzzle pieces are open. -/
axiom para_puzzle_piece_at_isOpen (c : ℂ) (n : ℕ) :
    IsOpen (ParaPuzzlePieceAt c n)

/-- The intersection of closures of parameter puzzle pieces is the same as the intersection of pieces,
    provided they shrink to a point. -/
axiom iInter_closure_para_puzzle_piece (c : ℂ) (h : (⋂ n, ParaPuzzlePieceAt c n) = {c}) :
    (⋂ n, closure (ParaPuzzlePieceAt c n)) = {c}

/-- Nested compact sets with a singleton intersection form a neighborhood basis. -/
theorem hasBasis_nhds_of_iInter_singleton {α : Type*} [TopologicalSpace α] [T2Space α]
    {K : ℕ → Set α} (h_compact : ∀ n, IsCompact (K n)) (h_nested : ∀ n, K (n + 1) ⊆ K n)
    {x : α} (h_inter : (⋂ n, K n) = {x}) (h_nhd : ∀ n, K n ∈ 𝓝 x) :
    (𝓝 x).HasBasis (fun _ => True) K := by
  refine ⟨fun U => ⟨fun hU => ?_, fun ⟨n, _, hn_sub⟩ => ?_⟩⟩
  · obtain ⟨V, hV_sub, hV_open, hxV⟩ := mem_nhds_iff.mp hU
    by_contra! h_neg
    let F := fun n => K n \ V
    have hF_nonempty : ∀ n, (F n).Nonempty := by
      intro n
      rw [Set.diff_nonempty]
      intro h_sub
      exact (h_neg n trivial) (h_sub.trans hV_sub)
    have hF_nested : ∀ n, F (n + 1) ⊆ F n := fun n => diff_subset_diff (h_nested n) (subset_refl V)
    have hF_compact : ∀ n, IsCompact (F n) := fun n => (h_compact n).diff hV_open
    have hF_closed : ∀ n, IsClosed (F n) := fun n => (hF_compact n).isClosed
    obtain ⟨y, hy⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed F hF_nested hF_nonempty (hF_compact 0) hF_closed
    have h_inter_F : (⋂ n, F n) = (⋂ n, K n) \ V := by
      ext z
      simp [F, forall_and]
    rw [h_inter_F, h_inter] at hy
    have h_empty : ({x} : Set α) \ V = ∅ := Set.diff_eq_empty.mpr (singleton_subset_iff.mpr hxV)
    rw [h_empty] at hy
    exact (Set.mem_empty_iff_false y).mp hy
  · exact mem_of_superset (h_nhd n) hn_sub

/-- Parameter puzzle pieces are nested. -/
axiom para_puzzle_piece_nested (c : ℂ) (n : ℕ) :
    ParaPuzzlePieceAt c (n + 1) ⊆ ParaPuzzlePieceAt c n

/-- Parameter puzzle pieces form a basis of neighborhoods if they shrink to a point. -/
axiom para_puzzle_piece_basis_sketch (c : ℂ) (h : (⋂ n, ParaPuzzlePieceAt c n) = {c}) :
    ∀ U ∈ 𝓝 c, ∃ n, ParaPuzzlePieceAt c n ⊆ U

end MLC.Quadratic
