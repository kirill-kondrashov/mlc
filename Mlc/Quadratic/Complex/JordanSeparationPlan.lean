import Mlc.Quadratic.Complex.JordanBasics
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Connected.LocPathConnected
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

/-- The curve image is compact and has empty interior. -/
lemma jordan_curve_image_interior_empty_plan (γ : ℝ → ℂ) (hγ : JordanCurve γ) :
    interior (JordanCurveImage γ) = ∅ := by
  sorry

/-- The complement of a Jordan curve image is open and locally path-connected. -/
lemma jordan_curve_compl_locPathConnected_plan (γ : ℝ → ℂ) (hγ : JordanCurve γ) :
    LocPathConnectedSpace (Set.compl (JordanCurveImage γ)) := by
  sorry

/-- Any point in the complement can be connected by a path to one of the basepoints. -/
lemma jordan_compl_path_to_zero_or_one_plan (γ : ℝ → ℂ) (hγ : JordanCurve γ) {z : ℂ}
    (hz : z ∈ Set.compl (JordanCurveImage γ)) :
    (∃ p : Path z 0, ∀ t, p t ∈ Set.compl (JordanCurveImage γ)) ∨
      (∃ p : Path z 1, ∀ t, p t ∈ Set.compl (JordanCurveImage γ)) := by
  sorry

/-- Core separation: the complement is the union of the two components based at `0` and `1`. -/
lemma jordan_compl_mem_interior_or_exterior_plan (γ : ℝ → ℂ) (hγ : JordanCurve γ) {z : ℂ}
    (hz : z ∈ Set.compl (JordanCurveImage γ)) :
    z ∈ JordanInterior γ ∪ JordanExterior γ := by
  sorry

/-- The two components are disjoint (no third component). -/
lemma jordan_interior_exterior_disjoint_plan (γ : ℝ → ℂ) (hγ : JordanCurve γ) :
    Disjoint (JordanInterior γ) (JordanExterior γ) := by
  sorry

end

end MLC.Quadratic
