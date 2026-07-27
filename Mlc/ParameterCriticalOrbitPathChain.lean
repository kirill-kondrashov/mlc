import Mlc.ParameterCriticalOrbitLocal
import Mlc.BottcherFiniteEscapingLoopCover

namespace MLC.Quadratic

open Complex Topology Filter Set Metric

/-- A continuous parameter path on the compact unit interval staying in the
Mandelbrot complement. -/
structure ParameterPath where
  path : ℝ → ℂ
  continuousOn_path : ContinuousOn path (Set.Icc (0 : ℝ) 1)
  maps_to_compl : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → path t ∉ MandelbrotSet

/-- A closed parameter loop on the compact unit interval. -/
structure ParameterLoop extends ParameterPath where
  endpoint_eq : path 0 = path 1

structure ParameterPathFiniteLocalBranchCover (γ : ParameterPath) where
  centers : Finset {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1}
  branchData : ∀ t : {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1},
    ParameterCriticalOrbitLocalBranchData (γ.path t)
  cover : ∀ t : {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1},
    ∃ s ∈ centers, γ.path t ∈ (branchData s).V

def ParameterPathFiniteLocalBranchCover.coverSet
    {γ : ParameterPath}
    (cover : ParameterPathFiniteLocalBranchCover γ)
    (t : {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1}) :
    Set {s : ℝ // s ∈ Set.Icc (0 : ℝ) 1} :=
  (fun s : {s : ℝ // s ∈ Set.Icc (0 : ℝ) 1} => γ.path s) ⁻¹' interior ((cover.branchData t).V)

lemma ParameterPathFiniteLocalBranchCover.coverSet_isOpen
    {γ : ParameterPath}
    (cover : ParameterPathFiniteLocalBranchCover γ)
    (t : {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1}) :
    IsOpen (cover.coverSet t) := by
  have hpath : Continuous (fun s : {s : ℝ // s ∈ Set.Icc (0 : ℝ) 1} => γ.path s) := by
    exact (continuousOn_iff_continuous_restrict).1 (by
      simpa using γ.continuousOn_path)
  exact isOpen_interior.preimage hpath

lemma ParameterPathFiniteLocalBranchCover.center_mem_coverSet
    {γ : ParameterPath}
    (cover : ParameterPathFiniteLocalBranchCover γ)
    (t : {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1}) :
    t ∈ cover.coverSet t := by
  have hs_interior : γ.path t ∈ interior ((cover.branchData t).V) :=
    mem_interior_iff_mem_nhds.mpr (cover.branchData t).V_mem
  exact hs_interior

lemma ParameterPathFiniteLocalBranchCover.exists_lebesgue_number
    {γ : ParameterPath}
    (cover : ParameterPathFiniteLocalBranchCover γ) :
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

noncomputable def ParameterPathFiniteLocalBranchCover.of_path
    (γ : ParameterPath) : ParameterPathFiniteLocalBranchCover γ := by
  let I : Type := {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1}
  let D : ∀ t : I, ParameterCriticalOrbitLocalBranchData (γ.path t) := by
    intro t
    exact Classical.choose (exists_parameterCriticalOrbitLocalBranchData (γ.path t)
      (γ.maps_to_compl t.1 t.2))
  let V : ∀ t : I, Set I := fun t =>
    (fun s : I => γ.path s) ⁻¹' interior (D t).V
  have hpath : Continuous (fun s : I => γ.path s) := by
    exact (continuousOn_iff_continuous_restrict).1 (by
      simpa using γ.continuousOn_path)
  have hVo : ∀ t : I, IsOpen (V t) := by
    intro t
    exact isOpen_interior.preimage hpath
  have hVcover : (Set.univ : Set I) ⊆ ⋃ t : I, V t := by
    intro s _hs
    have hs_interior : γ.path s ∈ interior (D s).V :=
      mem_interior_iff_mem_nhds.mpr (D s).V_mem
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

structure ParameterPathMeshChain {γ : ParameterPath}
    (cover : ParameterPathFiniteLocalBranchCover γ) where
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

noncomputable def ParameterPathFiniteLocalBranchCover.toMeshChain
    {γ : ParameterPath}
    (cover : ParameterPathFiniteLocalBranchCover γ) :
    ParameterPathMeshChain cover := by
  classical
  let δ : ℝ := Classical.choose cover.exists_lebesgue_number
  have hδ : 0 < δ := (Classical.choose_spec cover.exists_lebesgue_number).1
  have hball : ∀ x : {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1}, ∃ i, Metric.ball x δ ⊆ cover.coverSet i :=
    (Classical.choose_spec cover.exists_lebesgue_number).2
  let m : ℕ := Classical.choose (exists_nat_one_div_lt hδ)
  have hm : 1 / (m + 1 : ℝ) < δ := Classical.choose_spec (exists_nat_one_div_lt hδ)
  let lebesgueCenterAt : {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1} → {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1} :=
    fun x => Classical.choose (hball x)
  let centerAt : {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1} → {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1} :=
    fun x => Classical.choose (cover.cover x)
  let cell_subset : ∀ k : Fin (m + 1),
      {y : {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1} |
        y.1 ∈ Set.Icc ((k.1 : ℝ) / (m + 1 : ℝ))
          (((k.1 + 1 : ℕ) : ℝ) / (m + 1 : ℝ))}
        ⊆ cover.coverSet (lebesgueCenterAt (meshPoint k.1 m (Nat.le_of_lt_succ k.2))) := by
    intro k y hy
    have hyball : dist y (meshPoint k.1 m (Nat.le_of_lt_succ k.2)) < δ :=
      mesh_interval_dist_lt_fin hm hy
    exact (Classical.choose_spec (hball (meshPoint k.1 m (Nat.le_of_lt_succ k.2)))) hyball
  refine
    { meshSize := m
      center := fun k => lebesgueCenterAt (meshPoint k.1 m (Nat.le_of_lt_succ k.2))
      coverCenter := fun k => centerAt (meshPoint k.1 m (Nat.le_of_lt_succ k.2))
      coverCenter_mem_centers := fun k => by
        exact (Classical.choose_spec (cover.cover (meshPoint k.1 m (Nat.le_of_lt_succ k.2)))).1
      cell_subset := cell_subset
      covers := ?_
      overlapPoint := ?_
      overlap_eq := ?_
      overlap_mem_left := ?_
      overlap_mem_right := ?_ }
  · intro y
    simpa using exists_mesh_cell_covering m y
  · intro j
    exact meshPointRight j.1 m (Nat.lt_trans j.2 (Nat.lt_succ_self _))
  · intro j
    simp [meshPointRight]
  · intro j
    have hjlt : j.1 < m + 1 := Nat.lt_trans j.2 (Nat.lt_succ_self _)
    have hj : (meshPointRight j.1 m hjlt).1 ∈
        Set.Icc ((j.1 : ℝ) / (m + 1 : ℝ))
          (((j.1 + 1 : ℕ) : ℝ) / (m + 1 : ℝ)) := by
      constructor
      · simp [meshPointRight]
        have hpos : (0 : ℝ) < (m + 1 : ℝ) := by positivity
        exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_succ j.1) hpos.le
      · simp [meshPointRight]
    exact cell_subset ⟨j.1, Nat.lt_trans j.2 (Nat.lt_succ_self _)⟩ hj
  · intro j
    have hjlt : j.1 < m + 1 := Nat.lt_trans j.2 (Nat.lt_succ_self _)
    have hj : (meshPointRight j.1 m hjlt).1 ∈
        Set.Icc (((j.1 + 1 : ℕ) : ℝ) / (m + 1 : ℝ))
          ((((j.1 + 1) + 1 : ℕ) : ℝ) / (m + 1 : ℝ)) := by
      constructor
      · simp [meshPointRight]
      · simp [meshPointRight]
        have hpos : (0 : ℝ) < (m + 1 : ℝ) := by positivity
        exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_succ (j.1 + 1)) hpos.le
    exact cell_subset ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩ hj

lemma Metric.ball_isPreconnected (c : ℂ) (r : ℝ) : IsPreconnected (Metric.ball c r) := by
  simpa [Metric.ball] using (convex_ball c r).isPreconnected

lemma overlap_ball_subset_of_mem_interiors
    {s0 s1 : Set ℂ} {x : ℂ}
    (hs0 : IsOpen s0) (hs1 : IsOpen s1)
    (hx0 : x ∈ s0) (hx1 : x ∈ s1) :
    ∃ r > 0, Metric.ball x r ⊆ s0 ∩ s1 := by
  have hs0_nhds : s0 ∈ 𝓝 x := hs0.mem_nhds hx0
  have hs1_nhds : s1 ∈ 𝓝 x := hs1.mem_nhds hx1
  have hinter : s0 ∩ s1 ∈ 𝓝 x := Filter.inter_mem hs0_nhds hs1_nhds
  rcases Metric.mem_nhds_iff.mp hinter with ⟨r, hr, hsub⟩
  exact ⟨r, hr, hsub⟩

lemma ParameterPathMeshChain.overlap_witness_mem_both
    {γ : ParameterPath} {cover : ParameterPathFiniteLocalBranchCover γ}
    (chain : ParameterPathMeshChain cover) (j : Fin chain.meshSize) :
    γ.path (chain.overlapPoint j) ∈ (cover.branchData (chain.center ⟨j.1, Nat.lt_trans j.2 (Nat.lt_succ_self _)⟩)).V ∩
      (cover.branchData (chain.center ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩)).V := by
  constructor
  · exact interior_subset (chain.overlap_mem_left j)
  · exact interior_subset (chain.overlap_mem_right j)

theorem exists_parameterPathFiniteChartChain
    (γ : ParameterPath) :
    ∃ cover : ParameterPathFiniteLocalBranchCover γ,
      ∃ chain : ParameterPathMeshChain cover,
        True := by
  let cover : ParameterPathFiniteLocalBranchCover γ := ParameterPathFiniteLocalBranchCover.of_path γ
  refine ⟨cover, ParameterPathFiniteLocalBranchCover.toMeshChain cover, trivial⟩

theorem ParameterPathMeshChain.overlap_transition_data
    {γ : ParameterPath} {cover : ParameterPathFiniteLocalBranchCover γ}
    (chain : ParameterPathMeshChain cover) (j : Fin chain.meshSize) :
    ∃ W : Set ℂ,
      IsPreconnected W ∧
      γ.path (chain.overlapPoint j) ∈ W ∧
      W ⊆ (cover.branchData (chain.center ⟨j.1, Nat.lt_trans j.2 (Nat.lt_succ_self _)⟩)).V ∧
      W ⊆ (cover.branchData (chain.center ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩)).V := by
  let c := γ.path (chain.overlapPoint j)
  have hc0 : c ∈ (cover.branchData (chain.center ⟨j.1, Nat.lt_trans j.2 (Nat.lt_succ_self _)⟩)).V :=
    interior_subset (chain.overlap_mem_left j)
  have hc1 : c ∈ (cover.branchData (chain.center ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩)).V :=
    interior_subset (chain.overlap_mem_right j)
  rcases overlap_ball_subset_of_mem_interiors
      (cover.branchData (chain.center ⟨j.1, Nat.lt_trans j.2 (Nat.lt_succ_self _)⟩)).V_open
      (cover.branchData (chain.center ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩)).V_open
      hc0 hc1 with ⟨r, hr, hsub⟩
  refine ⟨Metric.ball c r, Metric.ball_isPreconnected c r, ?_, ?_, ?_⟩
  · simpa [c] using hr
  · intro z hz
    exact (hsub hz).1
  · intro z hz
    exact (hsub hz).2

end MLC.Quadratic
