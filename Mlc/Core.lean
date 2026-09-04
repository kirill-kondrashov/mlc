import Mlc.CategoricalRoot

namespace MLC

noncomputable section

/-- Compatibility form of the categorical root theorem. -/
theorem mlc_conjecture :
    LocallyConnectedSpace mandelbrotSet :=
  Categorical.mlc_conjecture_iff_categorical.mpr
    Categorical.categorical_mlc_conjecture

end

end MLC
