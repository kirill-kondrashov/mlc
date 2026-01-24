import Mlc.RenormalizationTypes
import Mlc.MoleculeRenormalizationTower

namespace MLC

open Molecule

noncomputable section

/-!
An *infinite* satellite renormalization tower in the Molecule framework.

Our current `SatelliteRenormalizable c` is a one-step predicate (`IsFastRenormalizable` of a
BMol object attached to `c`). For DLS-style principal nests we ultimately need infinitely many
renormalizations; this file introduces that stronger notion and packages it as a
`RenormalizationTower`.
-/

def IsInfinitelyFastRenormalizable (g : BMol) : Prop :=
  ∀ n : ℕ, IsFastRenormalizable ((Rfast^[n]) g)

noncomputable def renormalizationTower_of_infinitelyFast (g : BMol)
    (h : IsInfinitelyFastRenormalizable g) :
    RenormalizationTower g := by
  refine
    { gₙ := fun n => (Rfast^[n]) g
      g0 := by simp
      step := ?_ }
  intro n
  have hn : IsFastRenormalizable ((Rfast^[n]) g) := h n
  -- `Rfast_spec` gives a renormalization relation from a map to its `Rfast`.
  have : Nonempty (RenormalizationRelation ((Rfast^[n]) g) (Rfast ((Rfast^[n]) g))) :=
    Rfast_spec ((Rfast^[n]) g) hn
  -- Rewrite `Rfast ((Rfast^[n]) g)` as the next iterate.
  simpa [Function.iterate_succ_apply'] using this

def SatelliteRenormalizableTower (c : ℂ) : Prop :=
  IsInfinitelyFastRenormalizable (parameterToBMol c)

noncomputable def satelliteTower (c : ℂ) (h : SatelliteRenormalizableTower c) :
    RenormalizationTower (parameterToBMol c) :=
  renormalizationTower_of_infinitelyFast (parameterToBMol c) h

theorem satelliteTower_depths_cofinal (c : ℂ) (h : SatelliteRenormalizableTower c) :
    MLC.Quadratic.PrincipalNest.Cofinal (RenormalizationTower.cumulativePeriod (satelliteTower c h)) :=
  RenormalizationTower.cumulativePeriod_cofinal (satelliteTower c h)

theorem satelliteTower_depths_monotone (c : ℂ) (h : SatelliteRenormalizableTower c) :
    Monotone (RenormalizationTower.cumulativePeriod (satelliteTower c h)) :=
  RenormalizationTower.cumulativePeriod_monotone (satelliteTower c h)

end

end MLC
