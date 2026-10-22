import Mlc.CategoricalRoot

namespace MLC

noncomputable section

/-- Main compatibility root theorem for the repaired proof structure. -/
theorem mlc_conjecture
    (h : RootInput) :
    LocallyConnectedSpace mandelbrotSet :=
  Categorical.mlc_conjecture_iff_categorical.mpr
    (Categorical.categorical_mlc_conjecture h)

/-- Convenience form of the repaired compatibility root theorem. -/
theorem mlc_conjecture_of_uniformOuterBuffer
    (hbuffer : ParameterComponent.MandelbrotUniformOuterBuffer) :
    LocallyConnectedSpace mandelbrotSet :=
  mlc_conjecture ⟨hbuffer⟩

end

end MLC
