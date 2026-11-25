import Mlc.CategoricalRoot

namespace MLC

noncomputable section

/-- Main compatibility root theorem for the repaired proof structure. -/
theorem mlc_conjecture
    (h : RootInput) :
    LocallyConnectedSpace mandelbrotSet :=
  Categorical.mlc_conjecture_iff_categorical.mpr
    (Categorical.categorical_mlc_conjecture h)

end

end MLC
