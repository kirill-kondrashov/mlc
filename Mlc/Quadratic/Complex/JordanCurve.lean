import Mlc.Quadratic.Complex.JordanBasics
import Mathlib.Topology.Connected.Basic

namespace MLC.Quadratic

open Complex Topology Set

noncomputable section

/-!
Jordan curve theorem development plan.

This file will host the core separation theorem for Jordan curves in `ℂ`.
It is currently a placeholder with a single consolidated statement.
-/

/-- The interior component lies in the complement of the curve image. -/
lemma jordan_interior_subset_compl (γ : ℝ → ℂ) :
    JordanInterior γ ⊆ Set.compl (JordanCurveImage γ) := by
  exact connectedComponentIn_subset _ _

/-- The exterior component lies in the complement of the curve image. -/
lemma jordan_exterior_subset_compl (γ : ℝ → ℂ) :
    JordanExterior γ ⊆ Set.compl (JordanCurveImage γ) := by
  exact connectedComponentIn_subset _ _

/-- Connected components are disjoint if the basepoint is not in the other component. -/
lemma connectedComponentIn_disjoint_of_not_mem {F : Set ℂ} {x y : ℂ}
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
      simpa [hxEmpty] using hz
    exact this
  have hy_mem : y ∈ connectedComponentIn F y := mem_connectedComponentIn hyF
  have : y ∈ connectedComponentIn F x := by
    simpa [hxy] using hy_mem
  exact hy this

lemma jordan_interior_eq_exterior_of_mem (γ : ℝ → ℂ)
    (h : (1 : ℂ) ∈ JordanInterior γ) :
    JordanExterior γ = JordanInterior γ := by
  have h' : (1 : ℂ) ∈
      connectedComponentIn (Set.compl (JordanCurveImage γ)) 0 := by
    simpa [JordanInterior] using h
  have h_eq :
      connectedComponentIn (Set.compl (JordanCurveImage γ)) 0 =
        connectedComponentIn (Set.compl (JordanCurveImage γ)) 1 :=
    connectedComponentIn_eq h'
  simpa [JordanInterior, JordanExterior] using h_eq.symm

lemma jordan_curve_interior_exterior_disjoint_of_not_mem (γ : ℝ → ℂ)
    (h : (1 : ℂ) ∉ JordanInterior γ) :
    Disjoint (JordanInterior γ) (JordanExterior γ) := by
  have h' : (1 : ℂ) ∉
      connectedComponentIn (Set.compl (JordanCurveImage γ)) 0 := by
    simpa [JordanInterior] using h
  simpa [JordanInterior, JordanExterior] using
    (connectedComponentIn_disjoint_of_not_mem (F := Set.compl (JordanCurveImage γ))
      (x := (0 : ℂ)) (y := (1 : ℂ)) h')

/-- Placeholder: every point in the complement is in the interior or exterior component. -/
lemma jordan_curve_compl_subset_union (γ : ℝ → ℂ) (hγ : JordanCurve γ) :
    Set.compl (JordanCurveImage γ) ⊆ JordanInterior γ ∪ JordanExterior γ := by
  -- TODO: core Jordan curve theorem separation.
  sorry

/-- Placeholder: the complement is exactly the union of interior/exterior. -/
lemma jordan_curve_compl_decomp (γ : ℝ → ℂ) (hγ : JordanCurve γ) :
    Set.compl (JordanCurveImage γ) =
        JordanInterior γ ∪ JordanExterior γ := by
  have h_union : JordanInterior γ ∪ JordanExterior γ ⊆ Set.compl (JordanCurveImage γ) := by
    intro z hz
    rcases hz with hz | hz
    · exact jordan_interior_subset_compl γ hz
    · exact jordan_exterior_subset_compl γ hz
  have h_compl : Set.compl (JordanCurveImage γ) ⊆ JordanInterior γ ∪ JordanExterior γ :=
    jordan_curve_compl_subset_union γ hγ
  exact subset_antisymm h_compl h_union

/-- Placeholder: interior and exterior components are disjoint. -/
lemma jordan_curve_interior_exterior_disjoint (γ : ℝ → ℂ) (hγ : JordanCurve γ) :
    Disjoint (JordanInterior γ) (JordanExterior γ) := by
  by_cases h0 : (0 : ℂ) ∈ JordanCurveImage γ
  · have h0' : (0 : ℂ) ∉ Set.compl (JordanCurveImage γ) := by
      intro h0compl
      exact h0compl h0
    have hempty : JordanInterior γ = ∅ := by
      simpa [JordanInterior] using (connectedComponentIn_eq_empty h0')
    simpa [hempty]
  by_cases h1 : (1 : ℂ) ∈ JordanCurveImage γ
  · have h1' : (1 : ℂ) ∉ Set.compl (JordanCurveImage γ) := by
      intro h1compl
      exact h1compl h1
    have hempty : JordanExterior γ = ∅ := by
      simpa [JordanExterior] using (connectedComponentIn_eq_empty h1')
    simpa [hempty]
  by_cases h : (1 : ℂ) ∈ JordanInterior γ
  · -- TODO: show the interior cannot contain `1` for a Jordan curve.
    -- This should be ruled out by Jordan separation.
    sorry
  · exact jordan_curve_interior_exterior_disjoint_of_not_mem γ h

/-- Placeholder: the curve image lies on the boundary of the interior component. -/
lemma jordan_curve_image_subset_frontier_interior (γ : ℝ → ℂ) (hγ : JordanCurve γ) :
    JordanCurveImage γ ⊆ frontier (JordanInterior γ) := by
  -- TODO: boundary characterization from separation.
  sorry

/-- Jordan curve theorem (placeholder): complement decomposition, disjointness, and boundary. -/
theorem jordan_curve_theorem (γ : ℝ → ℂ) (hγ : JordanCurve γ) :
    Set.compl (JordanCurveImage γ) =
        JordanInterior γ ∪ JordanExterior γ ∧
      Disjoint (JordanInterior γ) (JordanExterior γ) ∧
      JordanCurveImage γ ⊆ frontier (JordanInterior γ) := by
  refine ⟨jordan_curve_compl_decomp γ hγ, ?_, ?_⟩
  · exact jordan_curve_interior_exterior_disjoint γ hγ
  · exact jordan_curve_image_subset_frontier_interior γ hγ

end

end MLC.Quadratic
