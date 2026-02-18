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

/-- Parameter puzzle pieces are open. -/
lemma para_puzzle_piece_at_isOpen (c : ℂ) (n : ℕ) :
    IsOpen (ParaPuzzlePieceAt c n) := by
  have h_open_sublevel : IsOpen {w | green_function c w < (1 / 2) ^ n} :=
    IsOpen.preimage (continuous_green_function c) isOpen_Iio
  have h_comp_open : IsOpen (connectedComponentIn {w | green_function c w < (1 / 2) ^ n} 0) :=
    IsOpen.connectedComponentIn h_open_sublevel
  rw [ParaPuzzlePieceAt]
  let f := fun z : ℂ => z - c
  have hf : Continuous f := continuous_id.sub continuous_const
  exact h_comp_open.preimage hf

/-- The intersection of closures of parameter puzzle pieces is the same as the intersection of pieces,
    provided they shrink to a point. -/
lemma iInter_closure_para_puzzle_piece (c : ℂ) (h : (⋂ n, ParaPuzzlePieceAt c n) = {c}) :
    (⋂ n, closure (ParaPuzzlePieceAt c n)) = {c} := by
  ext c'
  constructor
  · intro h'
    simp only [mem_iInter] at h'
    -- We want to show c' = c.
    -- First, show `0` belongs to every dynamical puzzle piece.
    have h_c_in_P : ∀ n, c ∈ ParaPuzzlePieceAt c n := by
      intro n
      have : {c} ⊆ ParaPuzzlePieceAt c n := h ▸ iInter_subset _ n
      exact this (mem_singleton c)
    have h_0_in_D : ∀ n, 0 ∈ DynamicalPuzzlePiece c n 0 := by
      intro n
      specialize h_c_in_P n
      simpa [ParaPuzzlePieceAt] using h_c_in_P

    -- Show `green_function c (c' - c) = 0` from closure-membership in all pieces.
    let w : ℂ := c' - c
    have h_Gc'_eq : green_function c (c' - c) = 0 := by
      refine le_antisymm (le_of_forall_pos_le_add ?_) (green_function_nonneg c _)
      intro ε hε
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1/2 : ℝ) < 1)
      specialize h' n
      let S := {z | green_function c (z - c) ≤ (1 / 2) ^ n}
      have hS_closed : IsClosed S := by
        apply isClosed_le
        · exact (continuous_green_function c).comp (continuous_id.sub continuous_const)
        · exact continuous_const
      have h_piece_sub_S : ParaPuzzlePieceAt c n ⊆ S := by
        intro z hz
        simp only [ParaPuzzlePieceAt, mem_setOf_eq] at hz
        have h_sub := connectedComponentIn_subset {w | green_function c w < (1 / 2) ^ n} 0
        exact (le_of_lt (h_sub hz) : green_function c (z - c) ≤ (1 / 2) ^ n)
      have h_cl_sub_S : closure (ParaPuzzlePieceAt c n) ⊆ S := hS_closed.closure_subset_iff.mpr h_piece_sub_S
      have h_le_n : green_function c (c' - c) ≤ (1 / 2) ^ n := h_cl_sub_S h'
      linarith

    -- From `w ∈ closure P_n` and `G(w)=0`, show `w` is in each connected component.
    have hw_in_piece : ∀ n, c' ∈ ParaPuzzlePieceAt c n := by
      intro n
      let S : Set ℂ := {z | green_function c z < (1 / 2) ^ n}
      let C : Set ℂ := DynamicalPuzzlePiece c n 0
      have hS_open : IsOpen S := IsOpen.preimage (continuous_green_function c) isOpen_Iio
      have h0S : (0 : ℂ) ∈ S := by
        have h0D : (0 : ℂ) ∈ connectedComponentIn S 0 := by
          simpa [S, C, DynamicalPuzzlePiece] using (h_0_in_D n)
        exact connectedComponentIn_subset S 0 h0D
      have hwS : w ∈ S := by
        dsimp [S, w]
        rw [h_Gc'_eq]
        positivity
      have h_image_eq :
          (fun z : ℂ => z - c) '' ParaPuzzlePieceAt c n = C := by
        ext y
        constructor
        · rintro ⟨z, hz, rfl⟩
          simpa [C, ParaPuzzlePieceAt] using hz
        · intro hy
          refine ⟨y + c, ?_, by ring_nf⟩
          simpa [C, ParaPuzzlePieceAt] using hy
      have hw_closureC : w ∈ closure C := by
        have hw_img :
            w ∈ (fun z : ℂ => z - c) '' closure (ParaPuzzlePieceAt c n) := by
          refine ⟨c', h' n, by simp [w]⟩
        have h_closure_img :
            (fun z : ℂ => z - c) '' closure (ParaPuzzlePieceAt c n) ⊆
              closure ((fun z : ℂ => z - c) '' ParaPuzzlePieceAt c n) :=
          image_closure_subset_closure_image (continuous_id.sub continuous_const)
        exact (by simpa [h_image_eq] using h_closure_img hw_img)
      have hwC : w ∈ C := by
        by_contra hw_not_C
        let D : Set ℂ := connectedComponentIn S w
        have hwD : w ∈ D := mem_connectedComponentIn hwS
        have hD_open : IsOpen D := hS_open.connectedComponentIn
        have h_disj : Disjoint D C := by
          refine Set.disjoint_left.2 ?_
          intro y hyD hyC
          have hDw : D = connectedComponentIn S y := connectedComponentIn_eq hyD
          have hCw : C = connectedComponentIn S y := connectedComponentIn_eq hyC
          have hDC : D = C := hDw.trans hCw.symm
          exact hw_not_C (hDC ▸ hwD)
        have hD_nhds : D ∈ 𝓝 w := hD_open.mem_nhds hwD
        have h_meet : (D ∩ C).Nonempty := (mem_closure_iff_nhds.1 hw_closureC) D hD_nhds
        rcases h_meet with ⟨y, hy⟩
        exact h_disj.le_bot hy
      simpa [w, C, S, ParaPuzzlePieceAt] using hwC

    have hc'_in_iInter : c' ∈ ⋂ n, ParaPuzzlePieceAt c n := by
      exact Set.mem_iInter.2 hw_in_piece
    have hc'_eq : c' = c := by
      simpa [h] using hc'_in_iInter
    simp [mem_singleton_iff, hc'_eq]

  · intro h'
    rw [mem_singleton_iff] at h'
    rw [h']
    rw [mem_iInter]
    intro n
    apply subset_closure
    have : {c} ⊆ ParaPuzzlePieceAt c n := h ▸ iInter_subset _ n
    exact this (mem_singleton c)

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
lemma para_puzzle_piece_nested (c : ℂ) (n : ℕ) :
    ParaPuzzlePieceAt c (n + 1) ⊆ ParaPuzzlePieceAt c n := by
  intro c' h
  simp [ParaPuzzlePieceAt] at h ⊢
  apply connectedComponentIn_mono (0 : ℂ) _ h
  intro w hw
  dsimp at hw ⊢
  calc green_function c w < (1 / 2) ^ (n + 1) := hw
    _ = (1 / 2) ^ n * (1 / 2) := by rw [pow_succ]
    _ < (1 / 2) ^ n * 1 := by
      apply mul_lt_mul_of_pos_left
      · norm_num
      · positivity
    _ = (1 / 2) ^ n := by rw [mul_one]

/-- Parameter puzzle pieces form a basis of neighborhoods if they shrink to a point. -/
theorem para_puzzle_piece_basis_sketch (c : ℂ) (h : (⋂ n, ParaPuzzlePieceAt c n) = {c}) :
    ∀ U ∈ 𝓝 c, ∃ n, ParaPuzzlePieceAt c n ⊆ U := by
  let K := fun n => closure (ParaPuzzlePieceAt c n)
  have h_compact : ∀ n, IsCompact (K n) := fun n => isCompact_closure_para_puzzle_piece c n
  have h_nested : ∀ n, K (n + 1) ⊆ K n := fun n => closure_mono (para_puzzle_piece_nested c n)
  have h_inter : (⋂ n, K n) = {c} := iInter_closure_para_puzzle_piece c h
  
  have h_nhd : ∀ n, K n ∈ 𝓝 c := by
    intro n
    have h_c_in : c ∈ ParaPuzzlePieceAt c n := by
      have : {c} ⊆ ParaPuzzlePieceAt c n := by
        rw [← h]
        exact iInter_subset _ n
      exact singleton_subset_iff.mp this
    exact mem_of_superset ((para_puzzle_piece_at_isOpen c n).mem_nhds h_c_in) subset_closure

  -- Apply the topological lemma to K n
  have h_basis := hasBasis_nhds_of_iInter_singleton h_compact h_nested h_inter h_nhd
  
  intro U hU
  obtain ⟨n, _, hn_sub⟩ := h_basis.mem_iff.mp hU
  use n
  -- P n ⊆ cl P n ⊆ U
  exact subset_trans subset_closure hn_sub

end MLC.Quadratic
