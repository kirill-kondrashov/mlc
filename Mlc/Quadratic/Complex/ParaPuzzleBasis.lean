import Mathlib.Topology.Order
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Connected.LocallyConnected
import Yoccoz.Quadratic.Complex.Basic
import Yoccoz.Quadratic.Complex.Puzzle
import Yoccoz.Quadratic.Complex.Green
import Yoccoz.Quadratic.Complex.GreenLemmas
import Yoccoz.Quadratic.Complex.Escape
import Mlc.Quadratic.Complex.ParaPuzzle
import Mlc.Quadratic.Complex.Axioms
import Mlc.Quadratic.Complex.PrincipalNestShrink
import Mlc.ParaPuzzleContainment
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

set_option maxHeartbeats 4000000

lemma complex_locally_connected : LocallyConnectedSpace ℂ := inferInstance

open Complex Topology Set Filter Metric Bornology

lemma continuous_orbit_zero_param : ∀ n : ℕ, Continuous (fun c : ℂ => orbit c 0 n)
  | 0 => by simpa using (continuous_const : Continuous fun _ : ℂ => (0 : ℂ))
  | n + 1 => by
      simpa [orbit_succ, fc] using
        ((continuous_orbit_zero_param n).pow 2).add continuous_id

lemma not_mandelbrot_of_orbit_gt_R (c : ℂ) (n : ℕ) (h : ‖orbit c 0 n‖ > R c) :
    c ∉ MandelbrotSet := by
  intro hc
  rcases hc with ⟨M, hM⟩
  rcases escape_lemma (c := c) (z := 0) n h (M + 1) with ⟨N, hN⟩
  have h_big : ‖orbit c 0 N‖ > M + 1 := hN N (le_rfl)
  have h_bdd : ‖orbit c 0 N‖ ≤ M := hM N
  linarith

lemma norm_fc_ge_mul_growth_of_norm_ge_norm_c (c z : ℂ) (hz : ‖c‖ ≤ ‖z‖) :
    ‖fc c z‖ ≥ ‖z‖ * (‖c‖ - 1) := by
  calc
    ‖fc c z‖ ≥ ‖z‖^2 - ‖c‖ := norm_fc_ge_norm_sq_sub_norm_c c z
    _ ≥ ‖z‖^2 - ‖z‖ := by linarith
    _ = ‖z‖ * (‖z‖ - 1) := by ring
    _ ≥ ‖z‖ * (‖c‖ - 1) := by
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      linarith

lemma orbit_param_lower_bound_of_norm_gt_two (c : ℂ) (hc : 2 < ‖c‖) :
    ∀ n : ℕ, ‖orbit c c n‖ ≥ ‖c‖ * (‖c‖ - 1) ^ n
  | 0 => by simp
  | n + 1 => by
      have hprev := orbit_param_lower_bound_of_norm_gt_two c hc n
      have hle : ‖c‖ ≤ ‖orbit c c n‖ := by
        calc
          ‖c‖ = ‖c‖ * 1 := by ring
          _ ≤ ‖c‖ * (‖c‖ - 1) ^ n := by
            gcongr
            exact one_le_pow₀ (by linarith : 1 ≤ ‖c‖ - 1)
          _ ≤ ‖orbit c c n‖ := hprev
      calc
        ‖orbit c c (n + 1)‖ = ‖fc c (orbit c c n)‖ := by rw [orbit_succ]
        _ ≥ ‖orbit c c n‖ * (‖c‖ - 1) :=
          norm_fc_ge_mul_growth_of_norm_ge_norm_c c (orbit c c n) hle
        _ ≥ (‖c‖ * (‖c‖ - 1) ^ n) * (‖c‖ - 1) := by
          refine mul_le_mul_of_nonneg_right hprev ?_
          linarith
        _ = ‖c‖ * (‖c‖ - 1) ^ (n + 1) := by
          rw [pow_succ]
          ring

lemma not_mandelbrot_of_norm_gt_two (c : ℂ) (hc : 2 < ‖c‖) :
    c ∉ MandelbrotSet := by
  intro hM
  rcases boundedOrbit_param_of_mandelbrot hM with ⟨M, hMparam⟩
  have h_tendsto :
      Tendsto (fun n : ℕ => ‖c‖ * (‖c‖ - 1) ^ n) atTop atTop := by
    refine Filter.Tendsto.const_mul_atTop ?_ ?_
    · have hnorm : 0 < ‖c‖ := by linarith
      exact hnorm
    · exact tendsto_pow_atTop_atTop_of_one_lt (by linarith)
  rcases (Filter.tendsto_atTop_atTop.mp h_tendsto) (M + 1) with ⟨N, hN⟩
  have h_growth : ‖orbit c c N‖ ≥ ‖c‖ * (‖c‖ - 1) ^ N :=
    orbit_param_lower_bound_of_norm_gt_two c hc N
  have h_large : ‖c‖ * (‖c‖ - 1) ^ N ≥ M + 1 := hN N (le_rfl)
  have h_bdd : ‖orbit c c N‖ ≤ M := hMparam N
  linarith

lemma mandelbrotSet_subset_closedBall_two :
    MandelbrotSet ⊆ Metric.closedBall (0 : ℂ) 2 := by
  intro c hc
  rw [Metric.mem_closedBall, dist_eq_norm]
  by_contra h
  exact not_mandelbrot_of_norm_gt_two c (by simpa using h) hc

theorem isOpen_compl_mandelbrotSet : IsOpen (MandelbrotSetᶜ) := by
  rw [isOpen_iff_mem_nhds]
  intro c hc
  have h_unbounded : ∀ M : ℝ, ∃ n : ℕ, ‖orbit c 0 n‖ > M := by
    intro M
    by_contra hM
    have h_le : ∀ n : ℕ, ‖orbit c 0 n‖ ≤ M := by
      intro n
      by_contra hn
      exact hM ⟨n, lt_of_not_ge hn⟩
    exact hc ⟨M, h_le⟩
  rcases h_unbounded (R c + 2) with ⟨n, hn⟩
  let V : Set ℂ := {d : ℂ | ‖orbit d 0 n‖ > R c + 1} ∩ Metric.ball c (1 / 2)
  have hV_open : IsOpen V := by
    refine (isOpen_Ioi.preimage ((continuous_orbit_zero_param n).norm)).inter isOpen_ball
  have hcV : c ∈ V := by
    refine ⟨?_, by simpa using (show (0 : ℝ) < 1 / 2 by norm_num)⟩
    have : ‖orbit c 0 n‖ > R c + 1 := by linarith [hn]
    exact this
  have hV_sub : V ⊆ MandelbrotSetᶜ := by
    intro d hd
    rcases hd with ⟨hd_orbit, hd_ball⟩
    have hd_norm : ‖d‖ < ‖c‖ + 1 / 2 := by
      have hdc : ‖d - c‖ < 1 / 2 := by simpa [dist_eq_norm] using hd_ball
      have : ‖d‖ ≤ ‖c‖ + ‖d - c‖ := by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
          (norm_add_le c (d - c))
      linarith
    have hRd : R d ≤ R c + 1 := by
      rw [R]
      refine max_le_iff.mpr ?_
      constructor
      · linarith [R_ge_two c]
      · have h1 : 1 + ‖d‖ ≤ 1 + (‖c‖ + 1 / 2) := by linarith
        have h2 : 1 + (‖c‖ + 1 / 2) ≤ R c + 1 := by
          linarith [R_ge_one_plus_c c]
        exact le_trans h1 h2
    have hd_gt_Rd : ‖orbit d 0 n‖ > R d := by
      exact lt_of_le_of_lt hRd hd_orbit
    exact not_mandelbrot_of_orbit_gt_R d n hd_gt_Rd
  exact mem_of_superset (hV_open.mem_nhds hcV) hV_sub

theorem isClosed_mandelbrotSet : IsClosed MandelbrotSet := by
  simpa using isOpen_compl_mandelbrotSet.isClosed_compl

theorem isCompact_mandelbrotSet : IsCompact MandelbrotSet := by
  refine (isCompact_closedBall (0 : ℂ) 2).of_isClosed_subset isClosed_mandelbrotSet ?_
  exact mandelbrotSet_subset_closedBall_two

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
theorem isCompact_closure_para_puzzle_piece (c : ℂ) (n : ℕ) :
    IsCompact (closure (ParaPuzzlePieceAt c n)) := by
  have hsub :
      DynamicalPuzzlePiece c n 0 ⊆ {z | green_function c z < (1 / 2) ^ n} :=
    connectedComponentIn_subset _ _
  have hbdd_dyn : IsBounded (DynamicalPuzzlePiece c n 0) :=
    (bounded_sublevel_green_function c ((1 / 2 : ℝ) ^ n)).subset hsub
  have hisom : Isometry (fun z : ℂ => z + c) := by
    refine Isometry.of_dist_eq ?_
    intro z w
    simpa using dist_add_right z w c
  have himage :
      ParaPuzzlePieceAt c n = (fun z : ℂ => z + c) '' DynamicalPuzzlePiece c n 0 := by
    ext z
    constructor
    · intro hz
      refine ⟨z - c, (mem_paraPuzzlePieceAt_iff c z n).mp hz, by simp⟩
    · rintro ⟨w, hw, rfl⟩
      exact (mem_paraPuzzlePieceAt_iff c (w + c) n).2 (by simpa)
  have hbdd_para : IsBounded (ParaPuzzlePieceAt c n) := by
    rw [himage]
    exact hisom.lipschitz.isBounded_image hbdd_dyn
  exact hbdd_para.isCompact_closure

/-- Parameter puzzle pieces are open. -/
theorem para_puzzle_piece_at_isOpen (c : ℂ) (n : ℕ) :
    IsOpen (ParaPuzzlePieceAt c n) := by
  simpa [ParaPuzzlePieceAt] using
    (Quadratic.PrincipalNest.isOpen_dynamicalPuzzlePiece c n).preimage
      (continuous_id.sub continuous_const)

/-- The intersection of closures of parameter puzzle pieces is the same as the intersection of pieces,
    provided they shrink to a point. -/
lemma para_puzzle_piece_subset_green_sublevel (c : ℂ) (n : ℕ) :
    ParaPuzzlePieceAt c n ⊆ {z | green_function c (z - c) < (1 / 2) ^ n} := by
  intro z hz
  have hz' : z - c ∈ DynamicalPuzzlePiece c n 0 :=
    (mem_paraPuzzlePieceAt_iff c z n).mp hz
  simpa [DynamicalPuzzlePiece] using
    (connectedComponentIn_subset {w | green_function c w < (1 / 2) ^ n} (0 : ℂ) hz')

lemma closure_para_puzzle_piece_subset_green_closedSublevel (c : ℂ) (n : ℕ) :
    closure (ParaPuzzlePieceAt c n) ⊆ {z | green_function c (z - c) ≤ (1 / 2) ^ n} := by
  refine closure_minimal ?_ ?_
  intro z hz
  change green_function c (z - c) ≤ (1 / 2) ^ n
  exact le_of_lt ((para_puzzle_piece_subset_green_sublevel c n) hz)
  exact isClosed_Iic.preimage ((continuous_green_function c).comp (continuous_id.sub continuous_const))
theorem iInter_closure_para_puzzle_piece (c : ℂ) (h : (⋂ n, ParaPuzzlePieceAt c n) = {c}) :
    (⋂ n, closure (ParaPuzzlePieceAt c n)) = {c} := by
  have center_mem_mandelbrot : c ∈ MandelbrotSet := by
    have hc_inter : c ∈ ⋂ n, ParaPuzzlePieceAt c n := by
      rw [h]
      simp
    by_contra hc_notM
    rcases dynamical_puzzle_piece_empty_of_large_n c hc_notM with ⟨N, hN⟩
    have hmem : c ∈ ParaPuzzlePieceAt c N := Set.mem_iInter.mp hc_inter N
    have hzero : 0 ∈ DynamicalPuzzlePiece c N 0 := by
      simpa using (mem_paraPuzzlePieceAt_iff c c N).mp hmem
    exact hN N le_rfl hzero
  have green_zero_of_mem_iInter_closure :
      ∀ {z : ℂ}, z ∈ ⋂ n, closure (ParaPuzzlePieceAt c n) →
        green_function c (z - c) = 0 := by
    intro z hz
    have hz_le : ∀ n, green_function c (z - c) ≤ (1 / 2 : ℝ) ^ n := by
      intro n
      exact closure_para_puzzle_piece_subset_green_closedSublevel c n (Set.mem_iInter.mp hz n)
    have h_nonneg : 0 ≤ green_function c (z - c) := green_function_nonneg c (z - c)
    by_contra hne
    have h_pos : 0 < green_function c (z - c) := lt_of_le_of_ne h_nonneg (Ne.symm hne)
    obtain ⟨N, hN⟩ : ∃ N : ℕ, (1 / 2 : ℝ) ^ N < green_function c (z - c) := by
      have h_tendsto : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) := by
        exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
      exact ((tendsto_order.1 h_tendsto).2 (green_function c (z - c)) h_pos).exists
    exact not_lt_of_ge (hz_le N) hN
  have mem_iInter_of_mem_iInter_closure :
      ∀ {z : ℂ}, z ∈ ⋂ n, closure (ParaPuzzlePieceAt c n) → z ∈ ⋂ n, ParaPuzzlePieceAt c n := by
    intro z hz
    have hz_zero := green_zero_of_mem_iInter_closure hz
    have hzK : z - c ∈ K c := (green_function_eq_zero_iff_mem_K c (z - c)).1 hz_zero
    refine Set.mem_iInter.mpr ?_
    intro n
    exact (mem_paraPuzzlePieceAt_iff c z n).2 (K_subset_dynamicalPuzzlePiece center_mem_mandelbrot n hzK)
  have hc_inter : c ∈ ⋂ n, ParaPuzzlePieceAt c n := by
    rw [h]
    simp
  ext z
  constructor
  · intro hz
    have hz_all : z ∈ ⋂ n, ParaPuzzlePieceAt c n := mem_iInter_of_mem_iInter_closure hz
    have hz_single : z ∈ ({c} : Set ℂ) := by
      rw [← h]
      exact hz_all
    simpa using hz_single
  · intro hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    refine Set.mem_iInter.mpr ?_
    intro n
    exact subset_closure (Set.mem_iInter.mp hc_inter n)

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
theorem para_puzzle_piece_nested (c : ℂ) (n : ℕ) :
    ParaPuzzlePieceAt c (n + 1) ⊆ ParaPuzzlePieceAt c n := by
  intro z hz
  rw [mem_paraPuzzlePieceAt_iff] at hz ⊢
  exact dynamical_puzzle_piece_nested c n hz

/-- Parameter puzzle pieces form a basis of neighborhoods if they shrink to a point. -/
theorem para_puzzle_piece_basis_sketch (c : ℂ) (h : (⋂ n, ParaPuzzlePieceAt c n) = {c}) :
    ∀ U ∈ 𝓝 c, ∃ n, ParaPuzzlePieceAt c n ⊆ U := by
  have h_compact : ∀ n, IsCompact (closure (ParaPuzzlePieceAt c n)) := by
    intro n
    exact isCompact_closure_para_puzzle_piece c n
  have h_nested : ∀ n, closure (ParaPuzzlePieceAt c (n + 1)) ⊆ closure (ParaPuzzlePieceAt c n) := by
    intro n
    exact closure_mono (para_puzzle_piece_nested c n)
  have h_inter : (⋂ n, closure (ParaPuzzlePieceAt c n)) = {c} :=
    iInter_closure_para_puzzle_piece c h
  have h_nhd : ∀ n, closure (ParaPuzzlePieceAt c n) ∈ 𝓝 c := by
    intro n
    have hc_inter : c ∈ ⋂ n, ParaPuzzlePieceAt c n := by
      rw [h]
      simp
    have hmem : c ∈ ParaPuzzlePieceAt c n := Set.mem_iInter.mp hc_inter n
    have hopen : ParaPuzzlePieceAt c n ∈ 𝓝 c :=
      (para_puzzle_piece_at_isOpen c n).mem_nhds hmem
    exact mem_of_superset hopen subset_closure
  intro U hU
  obtain ⟨n, _, hn⟩ :=
    (hasBasis_nhds_of_iInter_singleton h_compact h_nested h_inter h_nhd).mem_iff.mp hU
  exact ⟨n, fun z hz => hn (subset_closure hz)⟩

end MLC.Quadratic
