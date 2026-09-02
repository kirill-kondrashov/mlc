import Mlc.SatelliteRenormalizationTower
import Mlc.Quadratic.Complex.PrincipalNestAnnulus
import Mlc.Quadratic.Complex.PrincipalNestShrink
import Mlc.Quadratic.Complex.YoccozConformal
import Mlc.Quadratic.Complex.ConformalGroetzsch
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace MLC

open Quadratic Complex Topology Set Filter BigOperators

noncomputable section

namespace PrincipalNestTarget

def depthsFromSatelliteTower (c : ℂ) (h : SatelliteRenormalizableTower c) : ℕ → ℕ :=
  RenormalizationTower.cumulativePeriod (satelliteTower c h)

theorem depthsFromSatelliteTower_monotone (c : ℂ) (h : SatelliteRenormalizableTower c) :
    Monotone (depthsFromSatelliteTower c h) :=
  satelliteTower_depths_monotone c h

def ConformalModulusNotSummableTarget (c : ℂ) (h : SatelliteRenormalizableTower c) : Prop :=
  ¬ Summable (fun n =>
    MLC.Quadratic.modulus
      (MLC.Quadratic.PrincipalNest.dynAnnulus c (depthsFromSatelliteTower c h) n))

def UniformConformalLowerBoundTarget (c : ℂ) (h : SatelliteRenormalizableTower c) : Prop :=
  ∃ μ > 0, ∀ n,
    μ ≤ MLC.Quadratic.modulus
      (MLC.Quadratic.PrincipalNest.dynAnnulus c (depthsFromSatelliteTower c h) n)

theorem conformalModulusNotSummableTarget_of_uniformConformalLowerBoundTarget
    (c : ℂ) (h : SatelliteRenormalizableTower c) :
    UniformConformalLowerBoundTarget c h →
    ConformalModulusNotSummableTarget c h := by
  intro h_uniform h_sum
  rcases h_uniform with ⟨μ, hμ_pos, hμ_lb⟩
  have h_lim : Filter.Tendsto
      (fun n =>
        MLC.Quadratic.modulus
          (MLC.Quadratic.PrincipalNest.dynAnnulus c
            (depthsFromSatelliteTower c h) n))
      Filter.atTop (nhds 0) :=
    Summable.tendsto_atTop_zero h_sum
  rw [Metric.tendsto_atTop] at h_lim
  specialize h_lim (μ / 2) (by positivity)
  rcases h_lim with ⟨N, hN⟩
  have h_dist : dist
      (MLC.Quadratic.modulus
        (MLC.Quadratic.PrincipalNest.dynAnnulus c
          (depthsFromSatelliteTower c h) N)) 0 < μ / 2 :=
    hN N (le_refl N)
  have h_lbN : μ ≤
      MLC.Quadratic.modulus
        (MLC.Quadratic.PrincipalNest.dynAnnulus c
          (depthsFromSatelliteTower c h) N) :=
    hμ_lb N
  have h_nonnegN : 0 ≤
      MLC.Quadratic.modulus
        (MLC.Quadratic.PrincipalNest.dynAnnulus c
          (depthsFromSatelliteTower c h) N) :=
    le_trans (le_of_lt hμ_pos) h_lbN
  have h_ltN :
      MLC.Quadratic.modulus
        (MLC.Quadratic.PrincipalNest.dynAnnulus c
          (depthsFromSatelliteTower c h) N) < μ / 2 := by
    simpa [Real.dist_eq, abs_of_nonneg h_nonnegN] using h_dist
  exact (not_lt_of_ge h_lbN) (lt_of_lt_of_le h_ltN (by nlinarith [hμ_pos]))

lemma principal_nest_disjoint_union_of_monotone_depths
    (c : ℂ) (depths : ℕ → ℕ) (hmono : Monotone depths) (n : ℕ) :
    MLC.Quadratic.PrincipalNest.dynAnnulus c depths n =
    ⋃ k ∈ Finset.Ico (depths n) (depths (n + 1)),
      MLC.Quadratic.PuzzleAnnulus c k := by
  classical
  let P := fun n => MLC.Quadratic.DynamicalPuzzlePiece c n 0
  let A := fun n => MLC.Quadratic.PuzzleAnnulus c n
  let B := fun n => MLC.Quadratic.PrincipalNest.dynAnnulus c depths n
  ext z
  dsimp [B, A, MLC.Quadratic.PrincipalNest.dynAnnulus,
    MLC.Quadratic.PuzzleAnnulus]
  constructor
  · intro hz
    by_cases h_empty : depths n = depths (n + 1)
    · rw [h_empty] at hz
      simp at hz
    · have h_lt : depths n < depths (n + 1) :=
        lt_of_le_of_ne (hmono (Nat.le_succ n)) h_empty
      have h_bound_pos : 0 < depths (n + 1) :=
        lt_of_le_of_lt (Nat.zero_le _) h_lt
      let bound := depths (n + 1) - 1
      have h_bound_lt : bound < depths (n + 1) :=
        Nat.pred_lt (ne_of_gt h_bound_pos)
      let p := fun k => z ∈ P k
      let I := Finset.Ico (depths n) (depths (n + 1))
      let S := I.filter p
      have h_nonempty : S.Nonempty := by
        use depths n
        change depths n ∈ I.filter p
        rw [Finset.mem_filter]
        constructor
        · rw [Finset.mem_Ico]
          exact ⟨le_refl _, h_lt⟩
        · exact hz.1
      let k := S.max' h_nonempty
      have hk_in_S : k ∈ S := Finset.max'_mem S h_nonempty
      have hk_in_S' : k ∈ I.filter p := by simpa [S] using hk_in_S
      have hk_idx : k ∈ I := (Finset.mem_filter.mp hk_in_S').1
      have hk_val_p : z ∈ P k := (Finset.mem_filter.mp hk_in_S').2
      simp only [Set.mem_iUnion, Set.mem_diff]
      use k
      use hk_idx
      constructor
      · exact hk_val_p
      · by_contra h_in
        rw [Finset.mem_Ico] at hk_idx
        by_cases h_next_lt : k + 1 < depths (n + 1)
        · have h_next_in_S : k + 1 ∈ S := by
            rw [Finset.mem_filter]
            constructor
            · rw [Finset.mem_Ico]
              exact ⟨le_trans hk_idx.1 (Nat.le_succ k), h_next_lt⟩
            · exact h_in
          have h_le := Finset.le_max' S (k + 1) h_next_in_S
          linarith
        · have h_next_eq : k + 1 = depths (n + 1) := by
            linarith [hk_idx.2]
          rw [h_next_eq] at h_in
          exact hz.2 h_in
  · intro hz
    simp only [Set.mem_iUnion] at hz
    rcases hz with ⟨k, hk_idx, hk_val⟩
    rw [Finset.mem_Ico] at hk_idx
    rcases hk_idx with ⟨hk_ge, hk_lt⟩
    rw [Set.mem_diff] at hk_val
    constructor
    · have h_sub : P k ⊆ P (depths n) :=
        MLC.Quadratic.subset_of_le_nested
          (fun m => MLC.Quadratic.dynamical_puzzle_piece_nested c m) hk_ge
      exact h_sub hk_val.1
    · intro h_in
      have h_sub : P (depths (n + 1)) ⊆ P (k + 1) :=
        MLC.Quadratic.subset_of_le_nested
          (fun m => MLC.Quadratic.dynamical_puzzle_piece_nested c m)
          (Nat.succ_le_of_lt hk_lt)
      exact hk_val.2 (h_sub h_in)

lemma principal_nest_modulus_sum_of_monotone_depths
    (c : ℂ) (depths : ℕ → ℕ) (hmono : Monotone depths) (n : ℕ) :
    MLC.Quadratic.modulus (MLC.Quadratic.PrincipalNest.dynAnnulus c depths n) =
    ∑ k ∈ Finset.Ico (depths n) (depths (n + 1)),
      MLC.Quadratic.modulus (MLC.Quadratic.PuzzleAnnulus c k) := by
  let P := fun n => MLC.Quadratic.DynamicalPuzzlePiece c n 0
  let A := fun n => MLC.Quadratic.PuzzleAnnulus c n
  have h_meas_A : ∀ n, MeasurableSet (A n) := by
    intro n
    exact (MLC.Quadratic.isOpen_dynamicalPuzzlePiece_conformal c n).measurableSet.diff
      (MLC.Quadratic.isOpen_dynamicalPuzzlePiece_conformal c (n + 1)).measurableSet
  rw [principal_nest_disjoint_union_of_monotone_depths c depths hmono n]
  apply MLC.Quadratic.modulus_finset_sum
  · intro i hi j hj hij
    simp at hi hj
    rw [Function.onFun, Set.disjoint_left]
    intro z hzi hzj
    simp [MLC.Quadratic.PuzzleAnnulus] at hzi hzj
    rcases ne_iff_lt_or_gt.mp hij with h_lt | h_gt
    · have h_sub : P j ⊆ P (i + 1) :=
        MLC.Quadratic.subset_of_le_nested
          (fun m => MLC.Quadratic.dynamical_puzzle_piece_nested c m)
          (Nat.succ_le_of_lt h_lt)
      exact hzi.2 (h_sub hzj.1)
    · have h_sub : P i ⊆ P (j + 1) :=
        MLC.Quadratic.subset_of_le_nested
          (fun m => MLC.Quadratic.dynamical_puzzle_piece_nested c m)
          (Nat.succ_le_of_lt h_gt)
      exact hzj.2 (h_sub hzi.1)
  · intro k hk
    exact h_meas_A k

theorem paraPuzzle_shrink_of_conformalModulusNotSummableTarget
    (c : ℂ)
    (hTower : SatelliteRenormalizableTower c)
    (hdiv : ConformalModulusNotSummableTarget c hTower) :
    (⋂ n, MLC.Quadratic.ParaPuzzlePieceAt c n) = {c} := by
  change ¬ Summable (fun n =>
    MLC.Quadratic.modulus
      (MLC.Quadratic.PrincipalNest.dynAnnulus c
        (depthsFromSatelliteTower c hTower) n)) at hdiv
  have h_dyn : (⋂ n, MLC.Quadratic.DynamicalPuzzlePiece c n 0) = {0} := by
    apply MLC.Quadratic.yoccoz_theorem_conformal
    have h_full_div :
        ¬ Summable (fun n =>
          MLC.Quadratic.modulus (MLC.Quadratic.PuzzleAnnulus c n)) := by
      intro h_sum
      apply hdiv
      let depths := depthsFromSatelliteTower c hTower
      let B := fun n => MLC.Quadratic.PrincipalNest.dynAnnulus c depths n
      have h_summable_B : Summable (fun n => MLC.Quadratic.modulus (B n)) := by
        apply summable_of_sum_range_le
          (c := ∑' k, MLC.Quadratic.modulus (MLC.Quadratic.PuzzleAnnulus c k))
        · intro n
          exact MLC.Quadratic.modulus_nonneg _
        · intro N
          have h_collapse :
              ∑ n ∈ Finset.range N, MLC.Quadratic.modulus (B n) =
                ∑ k ∈ Finset.Ico (depths 0) (depths N),
                  MLC.Quadratic.modulus (MLC.Quadratic.PuzzleAnnulus c k) := by
            induction N with
            | zero =>
                simp
            | succ n ih =>
                rw [Finset.sum_range_succ, ih,
                  principal_nest_modulus_sum_of_monotone_depths c depths
                    (depthsFromSatelliteTower_monotone c hTower) n]
                rw [Finset.sum_Ico_consecutive]
                · exact depthsFromSatelliteTower_monotone c hTower (Nat.zero_le n)
                · exact depthsFromSatelliteTower_monotone c hTower (Nat.le_succ n)
          rw [h_collapse]
          exact sum_le_hasSum _ (fun k _ => MLC.Quadratic.modulus_nonneg _)
            h_sum.hasSum
      simpa [B, depths, ConformalModulusNotSummableTarget,
        depthsFromSatelliteTower] using h_summable_B
    exact h_full_div
  exact MLC.Quadratic.PrincipalNest.para_iInter_eq_singleton_of_dyn_iInter_eq_singleton
    c h_dyn

theorem paraPuzzle_shrink_of_uniformConformalLowerBoundTarget
    (c : ℂ)
    (hTower : SatelliteRenormalizableTower c)
    (h_uniform : UniformConformalLowerBoundTarget c hTower) :
    (⋂ n, MLC.Quadratic.ParaPuzzlePieceAt c n) = {c} :=
  paraPuzzle_shrink_of_conformalModulusNotSummableTarget c hTower
    (conformalModulusNotSummableTarget_of_uniformConformalLowerBoundTarget
      c hTower h_uniform)

end PrincipalNestTarget

end

end MLC
