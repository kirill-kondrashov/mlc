import Mlc.ParameterComponentApproximation
import Mlc.CategoricalResidual
import Mathlib.Topology.Connected.LocallyConnected

namespace MLC

open Quadratic

noncomputable section

/-- The Mandelbrot set used by the categorical and compatibility roots. -/
abbrev mandelbrotSet : Set ℂ :=
  MLC.Quadratic.MandelbrotSet

/-- The active root exposes exactly the two open problems identified by Dudko:
    pseudo-Siegel a priori bounds and virtual-Molecule interpolation. -/
structure RootInput where
  problem43 : Problem43PseudoSiegelAPrioriBoundsData
  problem44 : Problem44VirtualMoleculeData problem43

theorem RootInput.locallyConnectedSpace (h : RootInput) :
    LocallyConnectedSpace mandelbrotSet :=
  Dudko.DudkoFrontierInput.locallyConnectedSpace
    { problem43 := h.problem43
      problem44 := h.problem44 }

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
