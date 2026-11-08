import Mlc.ParameterComponentApproximation
import Mlc.Research.Programme
import Mathlib.Topology.Connected.LocallyConnected

namespace MLC

open Quadratic

noncomputable section

/-- The Mandelbrot set used by the categorical and compatibility roots. -/
abbrev mandelbrotSet : Set ℂ :=
  MLC.Quadratic.MandelbrotSet

/-- The active root exposes the research system, its analytic realization,
and the separate global coverage obligation. No Dudko conjecture is assumed. -/
structure RootInput where
  system : Research.CandidateSystem
  realization : system.Realization
  coverage : system.Coverage

theorem RootInput.locallyConnectedSpace (h : RootInput) :
    LocallyConnectedSpace mandelbrotSet :=
  h.system.locallyConnectedSpace_of_realization_coverage h.realization h.coverage

namespace Categorical

open CategoryTheory

/-- The Mandelbrot set as an object of `TopCat`. -/
abbrev mandelbrotObject : TopCat :=
  TopCat.of MLC.mandelbrotSet

/-- Local connectedness expressed as a property of a `TopCat` object. -/
def IsLocallyConnectedObject (X : TopCat) : Prop :=
  @LocallyConnectedSpace X X.str

/-- The categorical formulation of the Mandelbrot local-connectivity
    conjecture. -/
def MLCConjecture : Prop :=
  IsLocallyConnectedObject mandelbrotObject

/-- The categorical target is definitionally the usual subspace target. -/
theorem mlcConjecture_iff_set :
    MLCConjecture ↔ LocallyConnectedSpace MLC.mandelbrotSet :=
  Iff.rfl

/-- Main categorical root theorem for the repaired proof structure. -/
theorem categorical_mlc_conjecture
    (h : MLC.RootInput) :
    MLCConjecture := by
  change LocallyConnectedSpace MLC.mandelbrotSet
  exact h.locallyConnectedSpace

/-- Convenience form of the repaired categorical root theorem. -/
theorem categorical_mlc_conjecture_of_uniformOuterBuffer
    (hbuffer : ParameterComponent.MandelbrotUniformOuterBuffer) :
    MLCConjecture :=
  ParameterComponent.mandelbrot_locallyConnected_of_uniformOuterBuffer hbuffer

/-- The usual and categorical root propositions are equivalent. -/
theorem mlc_conjecture_iff_categorical :
    LocallyConnectedSpace MLC.mandelbrotSet ↔ MLCConjecture :=
  mlcConjecture_iff_set.symm

end Categorical

end

end MLC
