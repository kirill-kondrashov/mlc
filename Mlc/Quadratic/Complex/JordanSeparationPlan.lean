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
This file records the intended steps with `sorry` placeholders, without adding axioms.
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
lemma jordan_curve_image_interior_empty_plan (γ : ℝ → ℂ) (hγ : JordanCurve γ) :
    interior (JordanCurveImage γ) = ∅ := by
  sorry

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

/-- Any point in the complement can be connected by a path to one of the basepoints. -/
lemma jordan_compl_path_to_zero_or_one_plan (γ : ℝ → ℂ) (hγ : JordanCurve γ) {z : ℂ}
    (hz : z ∈ Set.compl (JordanCurveImage γ)) :
    (∃ p : Path z 0, ∀ t, p t ∈ Set.compl (JordanCurveImage γ)) ∨
      (∃ p : Path z 1, ∀ t, p t ∈ Set.compl (JordanCurveImage γ)) := by
  sorry

private lemma mem_connectedComponentIn_of_path_plan {F : Set ℂ} {x y : ℂ} (γ : Path x y)
    (hγ : ∀ t, γ t ∈ F) :
    x ∈ connectedComponentIn F y := by
  have hpre : IsPreconnected (Set.range γ) :=
    (isConnected_range γ.continuous).isPreconnected
  have hx : x ∈ Set.range γ := ⟨0, by simpa using γ.source⟩
  have hy : y ∈ Set.range γ := ⟨1, by simpa using γ.target⟩
  have hsubset : Set.range γ ⊆ F := by
    intro z hz
    rcases hz with ⟨t, rfl⟩
    exact hγ t
  have hsub := hpre.subset_connectedComponentIn hy hsubset
  exact hsub hx

private lemma mem_jordanInterior_of_path_plan (γ : ℝ → ℂ) {z : ℂ} (p : Path z 0)
    (hp : ∀ t, p t ∈ Set.compl (JordanCurveImage γ)) :
    z ∈ JordanInterior γ := by
  have hz : z ∈ connectedComponentIn (Set.compl (JordanCurveImage γ)) 0 :=
    mem_connectedComponentIn_of_path_plan p hp
  simpa [JordanInterior] using hz

private lemma mem_jordanExterior_of_path_plan (γ : ℝ → ℂ) {z : ℂ} (p : Path z 1)
    (hp : ∀ t, p t ∈ Set.compl (JordanCurveImage γ)) :
    z ∈ JordanExterior γ := by
  have hz : z ∈ connectedComponentIn (Set.compl (JordanCurveImage γ)) 1 :=
    mem_connectedComponentIn_of_path_plan p hp
  simpa [JordanExterior] using hz

/-- Core separation: the complement is the union of the two components based at `0` and `1`. -/
lemma jordan_compl_mem_interior_or_exterior_plan (γ : ℝ → ℂ) (hγ : JordanCurve γ) {z : ℂ}
    (hz : z ∈ Set.compl (JordanCurveImage γ)) :
    z ∈ JordanInterior γ ∪ JordanExterior γ := by
  rcases jordan_compl_path_to_zero_or_one_plan γ hγ hz with ⟨p, hp⟩ | ⟨p, hp⟩
  · exact Or.inl (mem_jordanInterior_of_path_plan γ p hp)
  · exact Or.inr (mem_jordanExterior_of_path_plan γ p hp)

/-- Abstract separation statement: the complement has exactly two connected components. -/
lemma jordan_curve_complement_has_two_components (γ : ℝ → ℂ) (hγ : JordanCurve γ) :
    ∃ U V : Set ℂ,
      IsConnected U ∧ IsConnected V ∧
      U ⊆ Set.compl (JordanCurveImage γ) ∧
      V ⊆ Set.compl (JordanCurveImage γ) ∧
      Disjoint U V ∧ U ∪ V = Set.compl (JordanCurveImage γ) ∧
      (0 : ℂ) ∈ U ∧ (1 : ℂ) ∈ V := by
  sorry

/-- Boundary formulation: each component has frontier equal to the curve image. -/
lemma jordan_curve_component_frontier (γ : ℝ → ℂ) (hγ : JordanCurve γ) :
    ∃ U V : Set ℂ,
      IsConnected U ∧ IsConnected V ∧
      IsOpen U ∧ IsOpen V ∧
      Disjoint U V ∧
      U ∪ V = Set.compl (JordanCurveImage γ) ∧
      frontier U = JordanCurveImage γ ∧
      frontier V = JordanCurveImage γ := by
  sorry

/-- Boundary statement for the interior component. -/
lemma jordan_curve_frontier_interior_plan (γ : ℝ → ℂ) (hγ : JordanCurve γ) :
    frontier (JordanInterior γ) = JordanCurveImage γ := by
  sorry

/-- Local separation at curve points: every neighborhood meets the interior. -/
lemma jordan_curve_local_separation_plan (γ : ℝ → ℂ) (hγ : JordanCurve γ)
    {z : ℂ} (hz : z ∈ JordanCurveImage γ) (U : Set ℂ)
    (hU : IsOpen U) (hzU : z ∈ U) :
    (U ∩ JordanInterior γ).Nonempty := by
  sorry

/-- The two components are disjoint (no third component). -/
lemma jordan_interior_exterior_disjoint_plan (γ : ℝ → ℂ) (hγ : JordanCurve γ) :
    Disjoint (JordanInterior γ) (JordanExterior γ) := by
  sorry

/-- Bundles the plan lemmas into a single package. -/
lemma jordan_separation_package_plan (γ : ℝ → ℂ) (hγ : JordanCurve γ) :
    JordanSeparationPackage γ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact jordan_curve_image_interior_empty_plan γ hγ
  · exact jordan_curve_compl_locPathConnected_plan γ hγ
  · intro z hz
    exact jordan_compl_path_to_zero_or_one_plan γ hγ hz
  · intro z hz
    exact jordan_compl_mem_interior_or_exterior_plan γ hγ hz
  · exact (jordan_interior_exterior_disjoint_plan γ hγ)
  · exact jordan_curve_complement_has_two_components γ hγ
  · exact jordan_curve_component_frontier γ hγ
  · exact jordan_curve_frontier_interior_plan γ hγ
  · intro z hz U hU hzU
    exact jordan_curve_local_separation_plan γ hγ hz U hU hzU

end

end MLC.Quadratic
