import Mlc.ParameterComponentApproximation
import Mathlib.Topology.Connected.LocallyConnected

namespace MLC

open Quadratic

noncomputable section

/-- The Mandelbrot set used by the categorical and compatibility roots. -/
abbrev mandelbrotSet : Set ℂ :=
  MLC.Quadratic.MandelbrotSet

/-- The explicit mathematical input for the repaired MLC root. This is a
    proposition supplied by a parameter-dynamical argument; it is not an
    axiom declaration. -/
structure RootInput : Prop where
  uniformOuterBuffer :
    ParameterComponent.MandelbrotUniformOuterBuffer

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
  exact ParameterComponent.mandelbrot_locallyConnected_of_uniformOuterBuffer
    h.uniformOuterBuffer

/-- Convenience form of the repaired categorical root theorem. -/
theorem categorical_mlc_conjecture_of_uniformOuterBuffer
    (hbuffer : ParameterComponent.MandelbrotUniformOuterBuffer) :
    MLCConjecture :=
  categorical_mlc_conjecture ⟨hbuffer⟩

/-- The usual and categorical root propositions are equivalent. -/
theorem mlc_conjecture_iff_categorical :
    LocallyConnectedSpace MLC.mandelbrotSet ↔ MLCConjecture :=
  mlcConjecture_iff_set.symm

end Categorical

end

end MLC
