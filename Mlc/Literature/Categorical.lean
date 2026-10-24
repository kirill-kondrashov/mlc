import Mlc.Core
import Mlc.EfimovCategoricalBridge
import Mlc.FiniteComponentCriterion
import Mlc.GreenSublevelIntersectionCounterexample
import Mlc.Literature.Review
import Mlc.UniformGeometricRoot

/-!
# Literature-facing account of the categorical branch

The categorical development is a change of language for several set-level
arguments, plus explicit interfaces for a future parameter--dynamical
theorem.  This file names the proved implications and the refuted frozen
Green-sublevel proposal so that the review cannot conflate them.
-/

namespace MLC
namespace Literature

noncomputable section

abbrev CategoricalMLC : Prop :=
  MLC.Categorical.MLCConjecture

theorem categoricalMLC_iff_setMLC :
    CategoricalMLC ↔ GlobalMLC :=
  by
    change MLC.Categorical.MLCConjecture ↔
      LocallyConnectedSpace MLC.mandelbrotSet
    exact MLC.Categorical.mlcConjecture_iff_set

theorem categoricalMLC_of_rootInput
    (h : MLC.RootInput) :
    CategoricalMLC :=
  MLC.Categorical.categorical_mlc_conjecture h

theorem setMLC_of_rootInput
    (h : MLC.RootInput) :
    GlobalMLC :=
  by
    change LocallyConnectedSpace MLC.mandelbrotSet
    exact MLC.mlc_conjecture h

theorem categoricalMLC_of_finiteComponentCriterion
    (h : MLC.FiniteComponent.FiniteComponentCriterion) :
    CategoricalMLC :=
  categoricalMLC_of_rootInput
    (MLC.FiniteComponent.rootInput_of_finiteComponentCriterion h)

theorem categoricalMLC_of_squareRetractionTower
    (T : MLC.UniformGeometry.OrbitRetractionTower
      MLC.UniformGeometry.parameterSquare) :
    CategoricalMLC :=
  MLC.UniformGeometry.categorical_mlc_of_squareTower T

theorem frozenGreenSublevelCarving_is_refuted :
    ¬ MLC.GreenSublevelIntersectionCategoricalData :=
  MLC.not_greenSublevelIntersectionCategoricalData

theorem categoricalFrontier_of_spaceHolomorphicCarving
    (h :
      ∀ (c : ℂ) (_hc : c ∈ MLC.Quadratic.MandelbrotSet) (n : ℕ),
        ¬ MLC.Efimov.greenSublevelTranslateSet c n ⊆
          MLC.Quadratic.MandelbrotSet →
          Nonempty (MLC.Efimov.SpaceHolomorphicCarvingData c n)) :
    MLC.GreenSublevelIntersectionCategoricalData :=
  MLC.Efimov.greenSublevelIntersectionCategoricalData_of_spaceHolomorphicCarving h

end

end Literature
end MLC
