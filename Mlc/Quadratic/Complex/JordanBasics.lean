import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Connected.Basic

namespace MLC.Quadratic

open Complex Topology Set

noncomputable section

/-- A minimal notion of a Jordan curve in `ℂ` (periodic, continuous, injective on `[0,1]`). -/
def JordanCurve (γ : ℝ → ℂ) : Prop :=
  Continuous γ ∧ (∀ t, γ (t + 1) = γ t) ∧ Set.InjOn γ (Set.Icc 0 1)

/-- The image of a Jordan curve. -/
def JordanCurveImage (γ : ℝ → ℂ) : Set ℂ :=
  γ '' Set.Icc 0 1

/-- The interior component of the curve, modeled as a component of the complement. -/
def JordanInterior (γ : ℝ → ℂ) : Set ℂ :=
  connectedComponentIn (Set.compl (JordanCurveImage γ)) 0

/-- The exterior component of the curve, modeled as a component of the complement. -/
def JordanExterior (γ : ℝ → ℂ) : Set ℂ :=
  connectedComponentIn (Set.compl (JordanCurveImage γ)) 1

end

end MLC.Quadratic
