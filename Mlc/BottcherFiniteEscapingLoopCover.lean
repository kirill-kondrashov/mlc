import Mlc.BottcherArbitraryFiniteLevelLift
open MLC MLC.Quadratic Complex Topology Filter Set
namespace MLC.Quadratic

lemma closed_interval_subset_of_mem_open_real
    {s : Set ℝ} {x : ℝ} (hs : IsOpen s) (hx : x ∈ s) :
    ∃ ε > 0, Set.Icc (x - ε / 2) (x + ε / 2) ⊆ s := by
  have hs_nhds : s ∈ 𝓝 x := IsOpen.mem_nhds hs hx
  rcases Metric.mem_nhds_iff.mp hs_nhds with ⟨ε, hεpos, hball⟩
  refine ⟨ε, hεpos, ?_⟩
  intro y hy
  have hy_abs : |y - x| < ε := by
    rw [abs_lt]
    constructor <;> linarith [hy.1, hy.2, hεpos]
  have hy_dist : dist y x < ε := by
    simpa [Real.dist_eq] using hy_abs
  exact hball hy_dist

structure BasinLoopFiniteLocalRootBranchCover
    (c : ℂ) (N : ℕ) (z₀ : ℂ) (γ : BasinLoop c z₀) where
  centers : Finset {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1}
  branchData : ∀ t : {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1},
    LocalPullbackRootBranchData c N (γ.path t)
  cover : ∀ t : {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1},
    ∃ s ∈ centers, γ.path t ∈ (branchData s).U

def BasinLoopFiniteLocalRootBranchCover.coverSet
    {c : ℂ} {N : ℕ} {z₀ : ℂ} {γ : BasinLoop c z₀}
    (cover : BasinLoopFiniteLocalRootBranchCover c N z₀ γ)
    (t : {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1}) :
    Set {s : ℝ // s ∈ Set.Icc (0 : ℝ) 1} :=
  (fun s : {s : ℝ // s ∈ Set.Icc (0 : ℝ) 1} => γ.path s) ⁻¹' interior ((cover.branchData t).U)

lemma BasinLoopFiniteLocalRootBranchCover.coverSet_isOpen
    {c : ℂ} {N : ℕ} {z₀ : ℂ} {γ : BasinLoop c z₀}
    (cover : BasinLoopFiniteLocalRootBranchCover c N z₀ γ)
    (t : {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1}) :
    IsOpen (cover.coverSet t) := by
  have hpath : Continuous (fun s : {s : ℝ // s ∈ Set.Icc (0 : ℝ) 1} => γ.path s) := by
    exact (continuousOn_iff_continuous_restrict).1 (by
      simpa using γ.continuousOn_path)
  exact isOpen_interior.preimage hpath

lemma BasinLoopFiniteLocalRootBranchCover.center_mem_coverSet
    {c : ℂ} {N : ℕ} {z₀ : ℂ} {γ : BasinLoop c z₀}
    (cover : BasinLoopFiniteLocalRootBranchCover c N z₀ γ)
    (t : {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1}) :
    t ∈ cover.coverSet t := by
  have hs_interior : γ.path t ∈ interior ((cover.branchData t).U) :=
    mem_interior_iff_mem_nhds.mpr (cover.branchData t).U_mem_nhds
  exact hs_interior

lemma BasinLoopFiniteLocalRootBranchCover.exists_lebesgue_number
    {c : ℂ} {N : ℕ} {z₀ : ℂ} {γ : BasinLoop c z₀}
    (cover : BasinLoopFiniteLocalRootBranchCover c N z₀ γ) :
    ∃ δ > 0,
      ∀ x : {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1}, ∃ i, Metric.ball x δ ⊆ cover.coverSet i := by
  classical
  rcases lebesgue_number_lemma_of_metric
      (s := (Set.univ : Set {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1}))
      (c := cover.coverSet)
      isCompact_univ
      (fun i => cover.coverSet_isOpen i)
      (by
        intro x _
        refine Set.mem_iUnion.2 ?_
        exact ⟨x, cover.center_mem_coverSet x⟩)
    with ⟨δ, hδ, hball⟩
  refine ⟨δ, hδ, ?_⟩
  intro x
  simpa using hball x (by simp)

lemma mesh_left_mem_Icc (k m : ℕ) (hk : k ≤ m) :
    ((k : ℝ) / (m + 1 : ℝ)) ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · positivity
  · have hk' : (k : ℝ) ≤ (m + 1 : ℝ) := by
      exact_mod_cast (Nat.le_trans hk (Nat.le_succ m))
    have hpos : (0 : ℝ) < (m + 1 : ℝ) := by positivity
    exact (div_le_one hpos).2 hk'

lemma mesh_right_mem_Icc (k m : ℕ) (hk : k < m + 1) :
    ((k + 1 : ℝ) / (m + 1 : ℝ)) ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · positivity
  · have hk' : (k + 1 : ℝ) ≤ (m + 1 : ℝ) := by
      exact_mod_cast (Nat.succ_le_of_lt hk)
    have hpos : (0 : ℝ) < (m + 1 : ℝ) := by positivity
    exact (div_le_one hpos).2 hk'

noncomputable def meshPoint (k m : ℕ) (hk : k ≤ m) : {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1} :=
  ⟨(k : ℝ) / (m + 1 : ℝ), mesh_left_mem_Icc k m hk⟩

noncomputable def meshPointRight (k m : ℕ) (hk : k < m + 1) : {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1} :=
  ⟨((k + 1 : ℝ) / (m + 1 : ℝ)), mesh_right_mem_Icc k m hk⟩

lemma mesh_step_eq (k m : ℕ) :
    ((k + 1 : ℝ) / (m + 1 : ℝ)) - ((k : ℝ) / (m + 1 : ℝ)) = (1 : ℝ) / (m + 1 : ℝ) := by
  have hden : (m + 1 : ℝ) ≠ 0 := by positivity
  field_simp [hden]
  ring

lemma mesh_interval_coord_lt_fin
    {δ : ℝ} {m : ℕ} (hm : 1 / (m + 1 : ℝ) < δ)
    {k : Fin (m + 1)}
    {y : {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1}}
    (hy : y.1 ∈ Set.Icc ((k.1 : ℝ) / (m + 1 : ℝ)) (((k.1 + 1 : ℕ) : ℝ) / (m + 1 : ℝ))) :
    |y.1 - (k.1 : ℝ) / (m + 1 : ℝ)| < δ := by
  have hnonneg : 0 ≤ y.1 - (k.1 : ℝ) / (m + 1 : ℝ) := by linarith [hy.1]
  have hstep_le : y.1 - (k.1 : ℝ) / (m + 1 : ℝ) ≤
      (((k.1 + 1 : ℕ) : ℝ) / (m + 1 : ℝ)) - ((k.1 : ℝ) / (m + 1 : ℝ)) := by
    linarith [hy.2]
  have hlt_step : y.1 - (k.1 : ℝ) / (m + 1 : ℝ) ≤ (1 : ℝ) / (m + 1 : ℝ) := by
    simpa [mesh_step_eq] using hstep_le
  have hlt : y.1 - (k.1 : ℝ) / (m + 1 : ℝ) < δ := lt_of_le_of_lt hlt_step hm
  simpa [abs_of_nonneg hnonneg] using hlt

lemma mesh_interval_dist_lt_fin
    {δ : ℝ} {m : ℕ} (hm : 1 / (m + 1 : ℝ) < δ)
    {k : Fin (m + 1)}
    {y : {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1}}
    (hy : y.1 ∈ Set.Icc ((k.1 : ℝ) / (m + 1 : ℝ)) (((k.1 + 1 : ℕ) : ℝ) / (m + 1 : ℝ))) :
    dist y (meshPoint k.1 m (Nat.le_of_lt_succ k.2)) < δ := by
  rw [Subtype.dist_eq, Real.dist_eq]
  simpa using mesh_interval_coord_lt_fin hm hy

noncomputable def BasinLoopFiniteLocalRootBranchCover.choiceDelta
    {c : ℂ} {N : ℕ} {z₀ : ℂ} {γ : BasinLoop c z₀}
    (cover : BasinLoopFiniteLocalRootBranchCover c N z₀ γ) : ℝ :=
  Classical.choose cover.exists_lebesgue_number

lemma BasinLoopFiniteLocalRootBranchCover.choiceDelta_pos
    {c : ℂ} {N : ℕ} {z₀ : ℂ} {γ : BasinLoop c z₀}
    (cover : BasinLoopFiniteLocalRootBranchCover c N z₀ γ) :
    0 < cover.choiceDelta :=
  (Classical.choose_spec cover.exists_lebesgue_number).1

noncomputable def BasinLoopFiniteLocalRootBranchCover.choiceMeshSize
    {c : ℂ} {N : ℕ} {z₀ : ℂ} {γ : BasinLoop c z₀}
    (cover : BasinLoopFiniteLocalRootBranchCover c N z₀ γ) : ℕ :=
  Classical.choose (exists_nat_one_div_lt cover.choiceDelta_pos)

lemma BasinLoopFiniteLocalRootBranchCover.choiceMeshSize_lt
    {c : ℂ} {N : ℕ} {z₀ : ℂ} {γ : BasinLoop c z₀}
    (cover : BasinLoopFiniteLocalRootBranchCover c N z₀ γ) :
    1 / (cover.choiceMeshSize + 1 : ℝ) < cover.choiceDelta :=
  Classical.choose_spec (exists_nat_one_div_lt cover.choiceDelta_pos)

noncomputable def BasinLoopFiniteLocalRootBranchCover.lebesgueCenterAt
    {c : ℂ} {N : ℕ} {z₀ : ℂ} {γ : BasinLoop c z₀}
    (cover : BasinLoopFiniteLocalRootBranchCover c N z₀ γ)
    (k : Fin (cover.choiceMeshSize + 1)) : {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1} :=
  Classical.choose ((Classical.choose_spec cover.exists_lebesgue_number).2
    (meshPoint k.1 cover.choiceMeshSize (Nat.le_of_lt_succ k.2)))

lemma BasinLoopFiniteLocalRootBranchCover.lebesgueCenterAt_ball_subset
    {c : ℂ} {N : ℕ} {z₀ : ℂ} {γ : BasinLoop c z₀}
    (cover : BasinLoopFiniteLocalRootBranchCover c N z₀ γ)
    (k : Fin (cover.choiceMeshSize + 1)) :
    Metric.ball (meshPoint k.1 cover.choiceMeshSize (Nat.le_of_lt_succ k.2)) cover.choiceDelta ⊆
      cover.coverSet (cover.lebesgueCenterAt k) :=
  Classical.choose_spec ((Classical.choose_spec cover.exists_lebesgue_number).2
    (meshPoint k.1 cover.choiceMeshSize (Nat.le_of_lt_succ k.2)))

noncomputable def BasinLoopFiniteLocalRootBranchCover.centerAt
    {c : ℂ} {N : ℕ} {z₀ : ℂ} {γ : BasinLoop c z₀}
    (cover : BasinLoopFiniteLocalRootBranchCover c N z₀ γ)
    (k : Fin (cover.choiceMeshSize + 1)) : {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1} :=
  Classical.choose (cover.cover (meshPoint k.1 cover.choiceMeshSize (Nat.le_of_lt_succ k.2)))

lemma BasinLoopFiniteLocalRootBranchCover.centerAt_mem_centers
    {c : ℂ} {N : ℕ} {z₀ : ℂ} {γ : BasinLoop c z₀}
    (cover : BasinLoopFiniteLocalRootBranchCover c N z₀ γ)
    (k : Fin (cover.choiceMeshSize + 1)) :
    cover.centerAt k ∈ cover.centers :=
  (Classical.choose_spec (cover.cover (meshPoint k.1 cover.choiceMeshSize
    (Nat.le_of_lt_succ k.2)))).1

lemma exists_mesh_cell_covering
    (m : ℕ) (y : {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1}) :
    ∃ k : Fin (m + 1),
      y.1 ∈ Set.Icc ((k.1 : ℝ) / (m + 1 : ℝ)) (((k.1 + 1 : ℕ) : ℝ) / (m + 1 : ℝ)) := by
  let a : ℝ := (m + 1 : ℝ) * y.1
  let n := Nat.floor a
  by_cases hn : n ≤ m
  · refine ⟨⟨n, Nat.lt_succ_of_le hn⟩, ?_⟩
    change y.1 ∈ Set.Icc ((n : ℝ) / (m + 1 : ℝ)) (((n + 1 : ℕ) : ℝ) / (m + 1 : ℝ))
    constructor
    · have hy0 : 0 ≤ y.1 := y.2.1
      have ha0 : 0 ≤ a := by
        dsimp [a]
        nlinarith [hy0]
      have hfloor_le : (n : ℝ) ≤ a := Nat.floor_le ha0
      dsimp [a] at hfloor_le
      have hden : 0 < (m + 1 : ℝ) := by positivity
      by_contra h
      have h' : y.1 < (n : ℝ) / (m + 1 : ℝ) := lt_of_not_ge h
      have hm := mul_lt_mul_of_pos_left h' hden
      field_simp [hden.ne'] at hm
      linarith
    · have hlt : a < (n + 1 : ℕ) := by
        simpa [a, n] using Nat.lt_floor_add_one a
      dsimp [a] at hlt
      have hden : 0 < (m + 1 : ℝ) := by positivity
      by_contra h
      have h' : (((n + 1 : ℕ) : ℝ) / (m + 1 : ℝ)) < y.1 := lt_of_not_ge h
      have hm := mul_lt_mul_of_pos_left h' hden
      field_simp [hden.ne'] at hm
      linarith
  · refine ⟨⟨m, Nat.lt_succ_self _⟩, ?_⟩
    change y.1 ∈ Set.Icc ((m : ℝ) / (m + 1 : ℝ)) (((m + 1 : ℕ) : ℝ) / (m + 1 : ℝ))
    constructor
    · have hy0 : 0 ≤ y.1 := y.2.1
      have hn' : m + 1 ≤ n := Nat.succ_le_of_lt (lt_of_not_ge hn)
      have ha0 : 0 ≤ a := by
        dsimp [a]
        nlinarith [hy0]
      have hfloor_le : (n : ℝ) ≤ a := Nat.floor_le ha0
      have hm_le : (m : ℝ) ≤ a := by
        exact le_trans (by exact_mod_cast Nat.le_of_succ_le hn') hfloor_le
      dsimp [a] at hm_le
      have hden : 0 < (m + 1 : ℝ) := by positivity
      by_contra h
      have h' : y.1 < (m : ℝ) / (m + 1 : ℝ) := lt_of_not_ge h
      have hm := mul_lt_mul_of_pos_left h' hden
      field_simp [hden.ne'] at hm
      linarith
    · have hy1 : y.1 ≤ 1 := y.2.2
      have hden : (m + 1 : ℝ) ≠ 0 := by positivity
      have hrhs : (((m + 1 : ℕ) : ℝ) / (m + 1 : ℝ)) = 1 := by
        rw [show (((m + 1 : ℕ) : ℝ) : ℝ) = (m + 1 : ℝ) by norm_num, div_self hden]
      rw [hrhs]
      exact hy1

structure BasinLoopMeshChain
    {c : ℂ} {N : ℕ} {z₀ : ℂ} {γ : BasinLoop c z₀}
    (cover : BasinLoopFiniteLocalRootBranchCover c N z₀ γ) where
  meshSize : ℕ
  center : Fin (meshSize + 1) → {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1}
  coverCenter : Fin (meshSize + 1) → {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1}
  coverCenter_mem_centers : ∀ k, coverCenter k ∈ cover.centers
  cell_subset : ∀ k,
    {y : {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1} |
      y.1 ∈ Set.Icc ((k.1 : ℝ) / (meshSize + 1 : ℝ)) (((k.1 + 1 : ℕ) : ℝ) / (meshSize + 1 : ℝ))}
      ⊆ cover.coverSet (center k)
  covers : ∀ y : {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1}, ∃ k : Fin (meshSize + 1),
    y.1 ∈ Set.Icc ((k.1 : ℝ) / (meshSize + 1 : ℝ)) (((k.1 + 1 : ℕ) : ℝ) / (meshSize + 1 : ℝ))
  overlapPoint : Fin meshSize → {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1}
  overlap_eq : ∀ j : Fin meshSize,
    (overlapPoint j).1 = ((j.1 + 1 : ℕ) : ℝ) / (meshSize + 1 : ℝ)
  overlap_mem_left : ∀ j : Fin meshSize,
    overlapPoint j ∈ cover.coverSet (center ⟨j.1, Nat.lt_trans j.2 (Nat.lt_succ_self _)⟩)
  overlap_mem_right : ∀ j : Fin meshSize,
    overlapPoint j ∈ cover.coverSet (center ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩)

noncomputable def BasinLoopFiniteLocalRootBranchCover.toMeshChain
    {c : ℂ} {N : ℕ} {z₀ : ℂ} {γ : BasinLoop c z₀}
    (cover : BasinLoopFiniteLocalRootBranchCover c N z₀ γ) :
    BasinLoopMeshChain cover := by
  classical
  let cell_subset : ∀ k : Fin (cover.choiceMeshSize + 1),
      {y : {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1} |
        y.1 ∈ Set.Icc ((k.1 : ℝ) / (cover.choiceMeshSize + 1 : ℝ))
          (((k.1 + 1 : ℕ) : ℝ) / (cover.choiceMeshSize + 1 : ℝ))}
        ⊆ cover.coverSet (cover.lebesgueCenterAt k) := by
    intro k y hy
    have hyball : dist y (meshPoint k.1 cover.choiceMeshSize (Nat.le_of_lt_succ k.2)) < cover.choiceDelta :=
      mesh_interval_dist_lt_fin cover.choiceMeshSize_lt hy
    exact cover.lebesgueCenterAt_ball_subset k hyball
  refine
    { meshSize := cover.choiceMeshSize
      center := cover.lebesgueCenterAt
      coverCenter := cover.centerAt
      coverCenter_mem_centers := cover.centerAt_mem_centers
      cell_subset := cell_subset
      covers := ?_
      overlapPoint := ?_
      overlap_eq := ?_
      overlap_mem_left := ?_
      overlap_mem_right := ?_ }
  · intro y
    simpa using exists_mesh_cell_covering cover.choiceMeshSize y
  · intro j
    exact meshPointRight j.1 cover.choiceMeshSize (Nat.lt_trans j.2 (Nat.lt_succ_self _))
  · intro j
    simp [meshPointRight]
  · intro j
    have hjlt : j.1 < cover.choiceMeshSize + 1 := Nat.lt_trans j.2 (Nat.lt_succ_self _)
    have hj : (meshPointRight j.1 cover.choiceMeshSize hjlt).1 ∈
        Set.Icc ((j.1 : ℝ) / (cover.choiceMeshSize + 1 : ℝ))
          (((j.1 + 1 : ℕ) : ℝ) / (cover.choiceMeshSize + 1 : ℝ)) := by
      constructor
      · simp [meshPointRight]
        have hpos : (0 : ℝ) < (cover.choiceMeshSize + 1 : ℝ) := by positivity
        exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_succ j.1) hpos.le
      · simp [meshPointRight]
    exact cell_subset ⟨j.1, Nat.lt_trans j.2 (Nat.lt_succ_self _)⟩ hj
  · intro j
    have hjlt : j.1 < cover.choiceMeshSize + 1 := Nat.lt_trans j.2 (Nat.lt_succ_self _)
    have hj : (meshPointRight j.1 cover.choiceMeshSize hjlt).1 ∈
        Set.Icc (((j.1 + 1 : ℕ) : ℝ) / (cover.choiceMeshSize + 1 : ℝ))
          ((((j.1 + 1) + 1 : ℕ) : ℝ) / (cover.choiceMeshSize + 1 : ℝ)) := by
      constructor
      · simp [meshPointRight]
      · simp [meshPointRight]
        have hpos : (0 : ℝ) < (cover.choiceMeshSize + 1 : ℝ) := by positivity
        exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_succ (j.1 + 1)) hpos.le
    exact cell_subset ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩ hj

noncomputable def BasinLoopFiniteLocalRootBranchCover.of_level_escapes
    {c : ℂ} {N : ℕ} {z₀ : ℂ} (γ : BasinLoop c z₀)
    (hesc : BasinLoopLevelEscapes c N γ) :
    BasinLoopFiniteLocalRootBranchCover c N z₀ γ := by
  let I : Type := {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1}
  let houtside : ∀ t : I,
      ‖(MLC.quadratic_map c)^[N] (γ.path t)‖ > ‖c‖ + 2 := by
    intro t
    exact hesc t.1 t.2
  let D : ∀ t : I, LocalPullbackRootBranchData c N (γ.path t) := by
    intro t
    exact localPullbackRootBranchData_of_iterate_outside c N (γ.path t) (houtside t)
  let V : ∀ t : I, Set I := fun t =>
    (fun s : I => γ.path s) ⁻¹' interior (D t).U
  have hpath : Continuous (fun s : I => γ.path s) := by
    exact (continuousOn_iff_continuous_restrict).1 (by
      simpa using γ.continuousOn_path)
  have hVo : ∀ t : I, IsOpen (V t) := by
    intro t
    exact isOpen_interior.preimage hpath
  have hVcover : (Set.univ : Set I) ⊆ ⋃ t : I, V t := by
    intro s _hs
    have hs_interior : γ.path s ∈ interior (D s).U :=
      mem_interior_iff_mem_nhds.mpr (D s).U_mem_nhds
    exact Set.mem_iUnion.2 ⟨s, hs_interior⟩
  let S : Finset I := Classical.choose (isCompact_univ.elim_finite_subcover V hVo hVcover)
  have hS : (Set.univ : Set I) ⊆ ⋃ t ∈ S, V t :=
    Classical.choose_spec (isCompact_univ.elim_finite_subcover V hVo hVcover)
  refine { centers := S, branchData := fun t => D t, cover := ?_ }
  intro t
  have htS : t ∈ ⋃ s ∈ S, V s := hS (by simp)
  rcases Set.mem_iUnion.1 htS with ⟨s, htS⟩
  rcases Set.mem_iUnion.1 htS with ⟨hsS, htVs⟩
  refine ⟨s, hsS, ?_⟩
  exact interior_subset htVs
end MLC.Quadratic
