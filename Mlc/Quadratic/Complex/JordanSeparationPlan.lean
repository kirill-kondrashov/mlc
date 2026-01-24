import Mlc.Quadratic.Complex.JordanBasics
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Connected.LocPathConnected
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Path
import Mathlib.Topology.Closure

namespace MLC.Quadratic

open Complex Topology Set

noncomputable section

/-!
Plan for proving the Jordan separation statement used by `JordanCurve.lean`.

The goal is to show the complement of a Jordan curve image has exactly two components.
This file now replaces sorries with hypothesis-style lemmas, but the core inputs
are still assumptions: empty interior of the curve image, the boundary decomposition
of the complement into two open components with the curve as frontier, and a
component-separation hypothesis distinguishing the `0`/`1` components.

Until these inputs are proved, `JordanCurve.lean` and `PlanarSeparation.lean`
remain conditional, and the puzzle-boundary motion chain in
`Mlc/Quadratic/Complex/PuzzleBoundaryMotionPlan.lean` cannot be fully discharged.
That, in turn, keeps the MLC proof skeleton dependent on analytic hypotheses.
-/

/-- Consolidated Jordan separation package (placeholders until fully proved). -/
structure JordanSeparationPackage (γ : ℝ → ℂ) : Prop where
  interior_empty :
    interior (JordanCurveImage γ) = ∅
  compl_locPathConnected :
    LocPathConnectedSpace (Set.compl (JordanCurveImage γ))
  compl_path_to_zero_or_one :
    ∀ {z : ℂ}, z ∈ Set.compl (JordanCurveImage γ) →
      (∃ p : Path z 0, ∀ t, p t ∈ Set.compl (JordanCurveImage γ)) ∨
        (∃ p : Path z 1, ∀ t, p t ∈ Set.compl (JordanCurveImage γ))
  compl_mem_interior_or_exterior :
    ∀ {z : ℂ}, z ∈ Set.compl (JordanCurveImage γ) →
      z ∈ JordanInterior γ ∪ JordanExterior γ
  interior_exterior_disjoint :
    Disjoint (JordanInterior γ) (JordanExterior γ)
  complement_has_two_components :
    ∃ U V : Set ℂ,
      IsConnected U ∧ IsConnected V ∧
      U ⊆ Set.compl (JordanCurveImage γ) ∧
      V ⊆ Set.compl (JordanCurveImage γ) ∧
      Disjoint U V ∧ U ∪ V = Set.compl (JordanCurveImage γ) ∧
      (0 : ℂ) ∈ U ∧ (1 : ℂ) ∈ V
  component_frontier :
    ∃ U V : Set ℂ,
      IsConnected U ∧ IsConnected V ∧
      IsOpen U ∧ IsOpen V ∧
      Disjoint U V ∧
      U ∪ V = Set.compl (JordanCurveImage γ) ∧
      frontier U = JordanCurveImage γ ∧
      frontier V = JordanCurveImage γ
  frontier_interior :
    frontier (JordanInterior γ) = JordanCurveImage γ
  local_separation :
    ∀ {z : ℂ}, z ∈ JordanCurveImage γ → ∀ U : Set ℂ,
      IsOpen U → z ∈ U → (U ∩ JordanInterior γ).Nonempty

/-- The curve image is compact and has empty interior. -/
lemma jordan_curve_image_interior_empty_plan (γ : ℝ → ℂ) (_hγ : JordanCurve γ)
    (h : interior (JordanCurveImage γ) = ∅) :
    interior (JordanCurveImage γ) = ∅ := by
  exact h

/-- The complement of a Jordan curve image is open and locally path-connected. -/
lemma jordan_curve_compl_locPathConnected_plan (γ : ℝ → ℂ) (hγ : JordanCurve γ) :
    LocPathConnectedSpace (Set.compl (JordanCurveImage γ)) := by
  have hcont : Continuous γ := hγ.1
  have hcont_on : ContinuousOn γ (Set.Icc (0 : ℝ) 1) := hcont.continuousOn
  have hcompact : IsCompact (JordanCurveImage γ) := by
    simpa [JordanCurveImage] using
      (IsCompact.image_of_continuousOn (s := Set.Icc (0 : ℝ) 1) isCompact_Icc hcont_on)
  have hclosed : IsClosed (JordanCurveImage γ) := hcompact.isClosed
  have hopen : IsOpen (Set.compl (JordanCurveImage γ)) := hclosed.isOpen_compl
  exact hopen.locPathConnectedSpace

private lemma mem_connectedComponentIn_of_path_plan {F : Set ℂ} {x y : ℂ} (γ : Path x y)
    (hγ : ∀ t, γ t ∈ F) :
    x ∈ connectedComponentIn F y := by
  have hpre : IsPreconnected (Set.range γ) :=
    (isConnected_range γ.continuous).isPreconnected
  have hy : y ∈ Set.range γ := ⟨1, by simp [γ.target]⟩
  have hsubset : Set.range γ ⊆ F := by
    intro z hz
    rcases hz with ⟨t, rfl⟩
    exact hγ t
  have hsub := hpre.subset_connectedComponentIn hy hsubset
  have hx : x ∈ Set.range γ := ⟨0, by simp [γ.source]⟩
  exact hsub hx

private lemma mem_jordanInterior_of_path_plan (γ : ℝ → ℂ) {z : ℂ} (p : Path z 0)
    (hp : ∀ t, p t ∈ Set.compl (JordanCurveImage γ)) :
    z ∈ JordanInterior γ := by
  have hz : z ∈ connectedComponentIn (Set.compl (JordanCurveImage γ)) 0 :=
    mem_connectedComponentIn_of_path_plan p hp
  change z ∈ connectedComponentIn (Set.compl (JordanCurveImage γ)) 0
  exact hz

private lemma mem_jordanExterior_of_path_plan (γ : ℝ → ℂ) {z : ℂ} (p : Path z 1)
    (hp : ∀ t, p t ∈ Set.compl (JordanCurveImage γ)) :
    z ∈ JordanExterior γ := by
  have hz : z ∈ connectedComponentIn (Set.compl (JordanCurveImage γ)) 1 :=
    mem_connectedComponentIn_of_path_plan p hp
  change z ∈ connectedComponentIn (Set.compl (JordanCurveImage γ)) 1
  exact hz

private lemma connectedComponentIn_eq_of_disjoint_open_cover_plan {F U V : Set ℂ} {x : ℂ}
    (hF : F = U ∪ V) (hUopen : IsOpen U) (hVopen : IsOpen V)
    (hUconn : IsConnected U) (hUV : Disjoint U V) (hxU : x ∈ U) (hUsub : U ⊆ F) :
    connectedComponentIn F x = U := by
  have hUsubset : U ⊆ connectedComponentIn F x :=
    hUconn.isPreconnected.subset_connectedComponentIn hxU hUsub
  have hcomp_sub : connectedComponentIn F x ⊆ U := by
    intro y hy
    have hcomp : IsPreconnected (connectedComponentIn F x) :=
      isPreconnected_connectedComponentIn
    have hcomp_subF : connectedComponentIn F x ⊆ F := connectedComponentIn_subset F x
    have hcomp_subUV : connectedComponentIn F x ⊆ U ∪ V := by
      simpa [hF] using hcomp_subF
    have hcomp_interU : (connectedComponentIn F x ∩ U).Nonempty := by
      have hxF : x ∈ F := hUsub hxU
      exact ⟨x, mem_connectedComponentIn (F := F) (x := x) hxF, hxU⟩
    have hcomp_subsetU :
        connectedComponentIn F x ⊆ U :=
      hcomp.subset_left_of_subset_union hUopen hVopen hUV hcomp_subUV hcomp_interU
    exact hcomp_subsetU hy
  exact subset_antisymm hcomp_sub hUsubset

private lemma connectedComponentIn_disjoint_of_not_mem_plan {F : Set ℂ} {x y : ℂ}
    (hy : y ∉ connectedComponentIn F x) :
    Disjoint (connectedComponentIn F x) (connectedComponentIn F y) := by
  refine Set.disjoint_left.2 ?_
  intro z hz hx
  have hxz : connectedComponentIn F x = connectedComponentIn F z :=
    connectedComponentIn_eq hz
  have hyz : connectedComponentIn F y = connectedComponentIn F z :=
    connectedComponentIn_eq hx
  have hxy : connectedComponentIn F x = connectedComponentIn F y :=
    hxz.trans hyz.symm
  have hyF : y ∈ F := by
    by_contra hyF
    have hyEmpty : connectedComponentIn F y = ∅ :=
      connectedComponentIn_eq_empty hyF
    have hxEmpty : connectedComponentIn F x = ∅ := by
      simpa [hyEmpty] using hxy
    have : False := by
      simp [hxEmpty] at hz
    exact this
  have hy_mem : y ∈ connectedComponentIn F y := mem_connectedComponentIn hyF
  have : y ∈ connectedComponentIn F x := by
    simpa [hxy] using hy_mem
  exact hy this

private lemma one_not_mem_jordanInterior_of_component_ne (γ : ℝ → ℂ)
    (h01 : connectedComponentIn (Set.compl (JordanCurveImage γ)) 0 ≠
      connectedComponentIn (Set.compl (JordanCurveImage γ)) 1) :
    (1 : ℂ) ∉ JordanInterior γ := by
  intro h1J
  have h1J' : (1 : ℂ) ∈ connectedComponentIn (Set.compl (JordanCurveImage γ)) 0 := by
    simpa [JordanInterior] using h1J
  have hEq : connectedComponentIn (Set.compl (JordanCurveImage γ)) 1 =
      connectedComponentIn (Set.compl (JordanCurveImage γ)) 0 := by
    simpa using
      (connectedComponentIn_eq (F := Set.compl (JordanCurveImage γ))
        (x := (0 : ℂ)) (y := (1 : ℂ)) h1J').symm
  exact h01 hEq.symm

private lemma path_to_zero_of_mem_jordanInterior_plan (γ : ℝ → ℂ) (hγ : JordanCurve γ)
    {z : ℂ} (hz : z ∈ JordanInterior γ) :
    ∃ p : Path z 0, ∀ t, p t ∈ Set.compl (JordanCurveImage γ) := by
  classical
  set F : Set ℂ := Set.compl (JordanCurveImage γ)
  have h0 : (0 : ℂ) ∈ F := by
    exact (connectedComponentIn_nonempty_iff (x := (0 : ℂ)) (F := F)).1 ⟨z, by
      simpa [JordanInterior, F] using hz⟩
  haveI : LocPathConnectedSpace F := jordan_curve_compl_locPathConnected_plan γ hγ
  have hz' : z ∈ (Subtype.val) '' connectedComponent (⟨0, h0⟩ : F) := by
    simpa [JordanInterior, F, connectedComponentIn_eq_image h0] using hz
  rcases hz' with ⟨w, hw, rfl⟩
  have hw' : w ∈ pathComponent (⟨0, h0⟩ : F) := by
    simpa [pathComponent_eq_connectedComponent (x := (⟨0, h0⟩ : F))] using hw
  have hjoined_subtype : Joined w (⟨0, h0⟩ : F) := by
    exact (mem_pathComponent_iff (x := w) (y := (⟨0, h0⟩ : F))).1 hw' |>.symm
  have hjoined : JoinedIn F (w : ℂ) 0 :=
    (joinedIn_iff_joined (x_in := w.property) (y_in := h0)).2 hjoined_subtype
  rcases hjoined with ⟨p, hp⟩
  exact ⟨p, hp⟩

private lemma path_to_one_of_mem_jordanExterior_plan (γ : ℝ → ℂ) (hγ : JordanCurve γ)
    {z : ℂ} (hz : z ∈ JordanExterior γ) :
    ∃ p : Path z 1, ∀ t, p t ∈ Set.compl (JordanCurveImage γ) := by
  classical
  set F : Set ℂ := Set.compl (JordanCurveImage γ)
  have h1 : (1 : ℂ) ∈ F := by
    exact (connectedComponentIn_nonempty_iff (x := (1 : ℂ)) (F := F)).1 ⟨z, by
      simpa [JordanExterior, F] using hz⟩
  haveI : LocPathConnectedSpace F := jordan_curve_compl_locPathConnected_plan γ hγ
  have hz' : z ∈ (Subtype.val) '' connectedComponent (⟨1, h1⟩ : F) := by
    simpa [JordanExterior, F, connectedComponentIn_eq_image h1] using hz
  rcases hz' with ⟨w, hw, rfl⟩
  have hw' : w ∈ pathComponent (⟨1, h1⟩ : F) := by
    simpa [pathComponent_eq_connectedComponent (x := (⟨1, h1⟩ : F))] using hw
  have hjoined_subtype : Joined w (⟨1, h1⟩ : F) := by
    exact (mem_pathComponent_iff (x := w) (y := (⟨1, h1⟩ : F))).1 hw' |>.symm
  have hjoined : JoinedIn F (w : ℂ) 1 :=
    (joinedIn_iff_joined (x_in := w.property) (y_in := h1)).2 hjoined_subtype
  rcases hjoined with ⟨p, hp⟩
  exact ⟨p, hp⟩

/-- Any point in the complement can be connected by a path to one of the basepoints. -/
lemma jordan_compl_path_to_zero_or_one_plan (γ : ℝ → ℂ) (hγ : JordanCurve γ) {z : ℂ}
    (_hz : z ∈ Set.compl (JordanCurveImage γ))
    (h_mem : z ∈ JordanInterior γ ∪ JordanExterior γ) :
    (∃ p : Path z 0, ∀ t, p t ∈ Set.compl (JordanCurveImage γ)) ∨
      (∃ p : Path z 1, ∀ t, p t ∈ Set.compl (JordanCurveImage γ)) := by
  rcases h_mem with hz | hz
  · exact Or.inl (path_to_zero_of_mem_jordanInterior_plan γ hγ hz)
  · exact Or.inr (path_to_one_of_mem_jordanExterior_plan γ hγ hz)

/-- Core separation: the complement is the union of the two components based at `0` and `1`. -/
lemma jordan_compl_mem_interior_or_exterior_plan (γ : ℝ → ℂ) (_hγ : JordanCurve γ) {z : ℂ}
    (_hz : z ∈ Set.compl (JordanCurveImage γ))
    (h_mem : z ∈ JordanInterior γ ∪ JordanExterior γ) :
    z ∈ JordanInterior γ ∪ JordanExterior γ := by
  exact h_mem

/-- Derive interior/exterior membership from a two-component decomposition. -/
lemma jordan_compl_mem_interior_or_exterior_of_two_components (γ : ℝ → ℂ) (_hγ : JordanCurve γ)
    {z : ℂ} (hz : z ∈ Set.compl (JordanCurveImage γ))
    (h_two :
      ∃ U V : Set ℂ,
        IsConnected U ∧ IsConnected V ∧
        U ⊆ Set.compl (JordanCurveImage γ) ∧
        V ⊆ Set.compl (JordanCurveImage γ) ∧
        Disjoint U V ∧ U ∪ V = Set.compl (JordanCurveImage γ) ∧
        (0 : ℂ) ∈ U ∧ (1 : ℂ) ∈ V) :
    z ∈ JordanInterior γ ∪ JordanExterior γ := by
  classical
  obtain ⟨U, V, hUconn, hVconn, hUcomp, hVcomp, hUVdisj, hUVunion, h0U, h1V⟩ := h_two
  have hUsub : U ⊆ connectedComponentIn (Set.compl (JordanCurveImage γ)) 0 := by
    exact hUconn.isPreconnected.subset_connectedComponentIn h0U hUcomp
  have hVsub : V ⊆ connectedComponentIn (Set.compl (JordanCurveImage γ)) 1 := by
    exact hVconn.isPreconnected.subset_connectedComponentIn h1V hVcomp
  have hz' : z ∈ U ∪ V := by
    simpa [hUVunion] using hz
  rcases hz' with hzU | hzV
  · left
    change z ∈ connectedComponentIn (Set.compl (JordanCurveImage γ)) 0
    exact hUsub hzU
  · right
    change z ∈ connectedComponentIn (Set.compl (JordanCurveImage γ)) 1
    exact hVsub hzV

/-- Derive interior/exterior membership from the boundary decomposition. -/
lemma jordan_compl_mem_interior_or_exterior_of_frontier (γ : ℝ → ℂ) (_hγ : JordanCurve γ)
    {z : ℂ} (hz : z ∈ Set.compl (JordanCurveImage γ))
    (h0 : (0 : ℂ) ∈ Set.compl (JordanCurveImage γ))
    (h1 : (1 : ℂ) ∈ Set.compl (JordanCurveImage γ))
    (h01 : connectedComponentIn (Set.compl (JordanCurveImage γ)) 0 ≠
      connectedComponentIn (Set.compl (JordanCurveImage γ)) 1)
    (h_frontier : ∃ U V : Set ℂ,
      IsConnected U ∧ IsConnected V ∧
      IsOpen U ∧ IsOpen V ∧
      Disjoint U V ∧
      U ∪ V = Set.compl (JordanCurveImage γ) ∧
      frontier U = JordanCurveImage γ ∧
      frontier V = JordanCurveImage γ) :
    z ∈ JordanInterior γ ∪ JordanExterior γ := by
  classical
  obtain ⟨U, V, hUconn, hVconn, hUopen, hVopen, hUVdisj, hUVunion, _hfrontU, _hfrontV⟩ :=
    h_frontier
  have hUsub : U ⊆ Set.compl (JordanCurveImage γ) := by
    intro w hw
    have : w ∈ U ∪ V := Or.inl hw
    simpa [hUVunion] using this
  have hVsub : V ⊆ Set.compl (JordanCurveImage γ) := by
    intro w hw
    have : w ∈ U ∪ V := Or.inr hw
    simpa [hUVunion] using this
  have h1notJint : (1 : ℂ) ∉ JordanInterior γ :=
    one_not_mem_jordanInterior_of_component_ne γ h01
  by_cases h0U : (0 : ℂ) ∈ U
  · have hJU : JordanInterior γ = U := by
      have hF : Set.compl (JordanCurveImage γ) = U ∪ V := hUVunion.symm
      simpa [JordanInterior] using
        connectedComponentIn_eq_of_disjoint_open_cover_plan (F := Set.compl (JordanCurveImage γ))
          (U := U) (V := V) (x := (0 : ℂ)) hF hUopen hVopen hUconn hUVdisj h0U hUsub
    have h1notU : (1 : ℂ) ∉ U := by
      intro h1U
      have : (1 : ℂ) ∈ JordanInterior γ := by
        simpa [hJU] using h1U
      exact h1notJint this
    have h1V : (1 : ℂ) ∈ V := by
      have h1UV : (1 : ℂ) ∈ U ∪ V := by
        simpa [hUVunion] using h1
      rcases h1UV with h1U | h1V
      · exact (h1notU h1U).elim
      · exact h1V
    have hJV : JordanExterior γ = V := by
      have hF : Set.compl (JordanCurveImage γ) = V ∪ U := by
        simp [hUVunion, Set.union_comm]
      simpa [JordanExterior] using
        connectedComponentIn_eq_of_disjoint_open_cover_plan (F := Set.compl (JordanCurveImage γ))
          (U := V) (V := U) (x := (1 : ℂ)) hF hVopen hUopen hVconn hUVdisj.symm h1V hVsub
    have hzUV : z ∈ U ∪ V := by
      simpa [hUVunion] using hz
    rcases hzUV with hzU | hzV
    · left
      simpa [hJU] using hzU
    · right
      simpa [hJV] using hzV
  · have h0V : (0 : ℂ) ∈ V := by
      have h0UV : (0 : ℂ) ∈ U ∪ V := by
        simpa [hUVunion] using h0
      rcases h0UV with h0U' | h0V
      · exact (h0U h0U').elim
      · exact h0V
    have hJV : JordanInterior γ = V := by
      have hF : Set.compl (JordanCurveImage γ) = V ∪ U := by
        simp [hUVunion, Set.union_comm]
      simpa [JordanInterior] using
        connectedComponentIn_eq_of_disjoint_open_cover_plan (F := Set.compl (JordanCurveImage γ))
          (U := V) (V := U) (x := (0 : ℂ)) hF hVopen hUopen hVconn hUVdisj.symm h0V hVsub
    have h1notV : (1 : ℂ) ∉ V := by
      intro h1V
      have : (1 : ℂ) ∈ JordanInterior γ := by
        simpa [hJV] using h1V
      exact h1notJint this
    have h1U : (1 : ℂ) ∈ U := by
      have h1UV : (1 : ℂ) ∈ U ∪ V := by
        simpa [hUVunion] using h1
      rcases h1UV with h1U | h1V
      · exact h1U
      · exact (h1notV h1V).elim
    have hJU : JordanExterior γ = U := by
      have hF : Set.compl (JordanCurveImage γ) = U ∪ V := hUVunion.symm
      simpa [JordanExterior] using
        connectedComponentIn_eq_of_disjoint_open_cover_plan (F := Set.compl (JordanCurveImage γ))
          (U := U) (V := V) (x := (1 : ℂ)) hF hUopen hVopen hUconn hUVdisj h1U hUsub
    have hzUV : z ∈ U ∪ V := by
      simpa [hUVunion] using hz
    rcases hzUV with hzU | hzV
    · right
      simpa [hJU] using hzU
    · left
      simpa [hJV] using hzV

/-- Derive the interior frontier equality from the boundary decomposition. -/
lemma jordan_curve_frontier_interior_of_frontier (γ : ℝ → ℂ) (_hγ : JordanCurve γ)
    (h0 : (0 : ℂ) ∈ Set.compl (JordanCurveImage γ))
    (h_frontier : ∃ U V : Set ℂ,
      IsConnected U ∧ IsConnected V ∧
      IsOpen U ∧ IsOpen V ∧
      Disjoint U V ∧
      U ∪ V = Set.compl (JordanCurveImage γ) ∧
      frontier U = JordanCurveImage γ ∧
      frontier V = JordanCurveImage γ) :
    frontier (JordanInterior γ) = JordanCurveImage γ := by
  classical
  obtain ⟨U, V, hUconn, hVconn, hUopen, hVopen, hUVdisj, hUVunion, hfrontU, hfrontV⟩ :=
    h_frontier
  have hUsub : U ⊆ Set.compl (JordanCurveImage γ) := by
    intro w hw
    have : w ∈ U ∪ V := Or.inl hw
    simpa [hUVunion] using this
  have hVsub : V ⊆ Set.compl (JordanCurveImage γ) := by
    intro w hw
    have : w ∈ U ∪ V := Or.inr hw
    simpa [hUVunion] using this
  by_cases h0U : (0 : ℂ) ∈ U
  · have hJU : JordanInterior γ = U := by
      have hF : Set.compl (JordanCurveImage γ) = U ∪ V := hUVunion.symm
      simpa [JordanInterior] using
        connectedComponentIn_eq_of_disjoint_open_cover_plan (F := Set.compl (JordanCurveImage γ))
          (U := U) (V := V) (x := (0 : ℂ)) hF hUopen hVopen hUconn hUVdisj h0U hUsub
    simp [hJU, hfrontU]
  · have h0V : (0 : ℂ) ∈ V := by
      have h0UV : (0 : ℂ) ∈ U ∪ V := by
        simpa [hUVunion] using h0
      rcases h0UV with h0U' | h0V
      · exact (h0U h0U').elim
      · exact h0V
    have hJV : JordanInterior γ = V := by
      have hF : Set.compl (JordanCurveImage γ) = V ∪ U := by
        simp [hUVunion, Set.union_comm]
      simpa [JordanInterior] using
        connectedComponentIn_eq_of_disjoint_open_cover_plan (F := Set.compl (JordanCurveImage γ))
          (U := V) (V := U) (x := (0 : ℂ)) hF hVopen hUopen hVconn hUVdisj.symm h0V hVsub
    simp [hJV, hfrontV]

/-- Derive local separation from the frontier characterization. -/
lemma jordan_curve_local_separation_of_frontier (γ : ℝ → ℂ) (_hγ : JordanCurve γ)
    (h_frontier_interior : frontier (JordanInterior γ) = JordanCurveImage γ)
    {z : ℂ} (hz : z ∈ JordanCurveImage γ) (U : Set ℂ)
    (hU : IsOpen U) (hzU : z ∈ U) :
    (U ∩ JordanInterior γ).Nonempty := by
  have hz_frontier : z ∈ frontier (JordanInterior γ) := by
    simpa [h_frontier_interior] using hz
  have hz_closure : z ∈ closure (JordanInterior γ) :=
    (frontier_subset_closure (s := JordanInterior γ)) hz_frontier
  exact (mem_closure_iff).1 hz_closure U hU hzU

/-- Abstract separation statement: the complement has exactly two connected components. -/
lemma jordan_curve_complement_has_two_components (γ : ℝ → ℂ) (_hγ : JordanCurve γ)
    (h0 : (0 : ℂ) ∈ Set.compl (JordanCurveImage γ))
    (h1 : (1 : ℂ) ∈ Set.compl (JordanCurveImage γ))
    (h_mem : ∀ {z : ℂ}, z ∈ Set.compl (JordanCurveImage γ) →
      z ∈ JordanInterior γ ∪ JordanExterior γ)
    (h01 : connectedComponentIn (Set.compl (JordanCurveImage γ)) 0 ≠
      connectedComponentIn (Set.compl (JordanCurveImage γ)) 1) :
    ∃ U V : Set ℂ,
      IsConnected U ∧ IsConnected V ∧
      U ⊆ Set.compl (JordanCurveImage γ) ∧
      V ⊆ Set.compl (JordanCurveImage γ) ∧
      Disjoint U V ∧ U ∪ V = Set.compl (JordanCurveImage γ) ∧
      (0 : ℂ) ∈ U ∧ (1 : ℂ) ∈ V := by
  have h1notJint : (1 : ℂ) ∉ JordanInterior γ :=
    one_not_mem_jordanInterior_of_component_ne γ h01
  have h_disj : Disjoint (JordanInterior γ) (JordanExterior γ) := by
    have hy : (1 : ℂ) ∉ connectedComponentIn (Set.compl (JordanCurveImage γ)) 0 := by
      simpa [JordanInterior] using h1notJint
    simpa [JordanInterior, JordanExterior] using
      (connectedComponentIn_disjoint_of_not_mem_plan
        (F := Set.compl (JordanCurveImage γ)) (x := (0 : ℂ)) (y := (1 : ℂ)) hy)
  refine ⟨JordanInterior γ, JordanExterior γ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [JordanInterior] using
      (isConnected_connectedComponentIn_iff (x := (0 : ℂ))
        (F := Set.compl (JordanCurveImage γ))).2 h0
  · simpa [JordanExterior] using
      (isConnected_connectedComponentIn_iff (x := (1 : ℂ))
        (F := Set.compl (JordanCurveImage γ))).2 h1
  · simpa [JordanInterior] using
      (connectedComponentIn_subset (Set.compl (JordanCurveImage γ)) (0 : ℂ))
  · simpa [JordanExterior] using
      (connectedComponentIn_subset (Set.compl (JordanCurveImage γ)) (1 : ℂ))
  · exact h_disj
  · apply subset_antisymm
    · intro z hz
      rcases hz with hz | hz
      · exact (connectedComponentIn_subset _ _) hz
      · exact (connectedComponentIn_subset _ _) hz
    · intro z hz
      exact h_mem hz
  · simpa [JordanInterior] using
      (mem_connectedComponentIn (F := Set.compl (JordanCurveImage γ)) (x := (0 : ℂ)) h0)
  · simpa [JordanExterior] using
      (mem_connectedComponentIn (F := Set.compl (JordanCurveImage γ)) (x := (1 : ℂ)) h1)

/-- Boundary formulation: each component has frontier equal to the curve image. -/
lemma jordan_curve_component_frontier (γ : ℝ → ℂ) (_hγ : JordanCurve γ)
    (h :
      ∃ U V : Set ℂ,
        IsConnected U ∧ IsConnected V ∧
        IsOpen U ∧ IsOpen V ∧
        Disjoint U V ∧
        U ∪ V = Set.compl (JordanCurveImage γ) ∧
        frontier U = JordanCurveImage γ ∧
        frontier V = JordanCurveImage γ) :
    ∃ U V : Set ℂ,
      IsConnected U ∧ IsConnected V ∧
      IsOpen U ∧ IsOpen V ∧
      Disjoint U V ∧
      U ∪ V = Set.compl (JordanCurveImage γ) ∧
      frontier U = JordanCurveImage γ ∧
      frontier V = JordanCurveImage γ := by
  exact h

/-- Boundary statement for the interior component. -/
lemma jordan_curve_frontier_interior_plan (γ : ℝ → ℂ) (_hγ : JordanCurve γ)
    (h : frontier (JordanInterior γ) = JordanCurveImage γ) :
    frontier (JordanInterior γ) = JordanCurveImage γ := by
  exact h

/-- Local separation at curve points: every neighborhood meets the interior. -/
lemma jordan_curve_local_separation_plan (γ : ℝ → ℂ) (_hγ : JordanCurve γ)
    {z : ℂ} (_hz : z ∈ JordanCurveImage γ) (U : Set ℂ)
    (_hU : IsOpen U) (_hzU : z ∈ U)
    (h : (U ∩ JordanInterior γ).Nonempty) :
    (U ∩ JordanInterior γ).Nonempty := by
  exact h

/-- The two components are disjoint (no third component). -/
lemma jordan_interior_exterior_disjoint_plan (γ : ℝ → ℂ) (_hγ : JordanCurve γ)
    (h : Disjoint (JordanInterior γ) (JordanExterior γ)) :
    Disjoint (JordanInterior γ) (JordanExterior γ) := by
  exact h

/-- Bundles the plan lemmas into a single package. -/
lemma jordan_separation_package_plan (γ : ℝ → ℂ) (hγ : JordanCurve γ)
    (h_interior_empty : interior (JordanCurveImage γ) = ∅)
    (h0 : (0 : ℂ) ∈ Set.compl (JordanCurveImage γ))
    (h1 : (1 : ℂ) ∈ Set.compl (JordanCurveImage γ))
    (h01 : connectedComponentIn (Set.compl (JordanCurveImage γ)) 0 ≠
      connectedComponentIn (Set.compl (JordanCurveImage γ)) 1)
    (h_frontier : ∃ U V : Set ℂ,
      IsConnected U ∧ IsConnected V ∧
      IsOpen U ∧ IsOpen V ∧
      Disjoint U V ∧
      U ∪ V = Set.compl (JordanCurveImage γ) ∧
      frontier U = JordanCurveImage γ ∧
      frontier V = JordanCurveImage γ) :
    JordanSeparationPackage γ := by
  have h1notJint : (1 : ℂ) ∉ JordanInterior γ :=
    one_not_mem_jordanInterior_of_component_ne γ h01
  have h_two :
      ∃ U V : Set ℂ,
        IsConnected U ∧ IsConnected V ∧
        U ⊆ Set.compl (JordanCurveImage γ) ∧
        V ⊆ Set.compl (JordanCurveImage γ) ∧
        Disjoint U V ∧ U ∪ V = Set.compl (JordanCurveImage γ) ∧
      (0 : ℂ) ∈ U ∧ (1 : ℂ) ∈ V :=
    jordan_curve_complement_has_two_components γ hγ h0 h1
      (fun {z} hz => jordan_compl_mem_interior_or_exterior_of_frontier γ hγ hz h0 h1 h01 h_frontier)
      h01
  have h_disj : Disjoint (JordanInterior γ) (JordanExterior γ) := by
    have hy : (1 : ℂ) ∉ connectedComponentIn (Set.compl (JordanCurveImage γ)) 0 := by
      simpa [JordanInterior] using h1notJint
    simpa [JordanInterior, JordanExterior] using
      (connectedComponentIn_disjoint_of_not_mem_plan
        (F := Set.compl (JordanCurveImage γ)) (x := (0 : ℂ)) (y := (1 : ℂ)) hy)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact jordan_curve_image_interior_empty_plan γ hγ h_interior_empty
  · exact jordan_curve_compl_locPathConnected_plan γ hγ
  · intro z hz
    have h_mem : z ∈ JordanInterior γ ∪ JordanExterior γ :=
      jordan_compl_mem_interior_or_exterior_of_frontier γ hγ hz h0 h1 h01 h_frontier
    exact jordan_compl_path_to_zero_or_one_plan γ hγ hz h_mem
  · intro z hz
    exact jordan_compl_mem_interior_or_exterior_plan γ hγ hz
      (jordan_compl_mem_interior_or_exterior_of_frontier γ hγ hz h0 h1 h01 h_frontier)
  · exact jordan_interior_exterior_disjoint_plan γ hγ h_disj
  · exact h_two
  · exact jordan_curve_component_frontier γ hγ h_frontier
  · exact jordan_curve_frontier_interior_of_frontier γ hγ h0 h_frontier
  · intro z hz U hU hzU
    have h_frontier_interior :
        frontier (JordanInterior γ) = JordanCurveImage γ :=
      jordan_curve_frontier_interior_of_frontier γ hγ h0 h_frontier
    exact jordan_curve_local_separation_of_frontier γ hγ h_frontier_interior hz U hU hzU

end

end MLC.Quadratic
