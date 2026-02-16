import Mlc.RenormalizationTypes
import Mlc.MoleculeRenormalizationTower

namespace MLC

open Molecule

noncomputable section

/-!
An *infinite* satellite renormalization tower in the Molecule framework.

`SatelliteRenormalizable c` is defined in `Mlc/RenormalizationTypes.lean` as infinite fast
renormalizability (`∀ n, IsFastRenormalizable ((Rfast^[n]) (parameterToBMol c))`).
This file packages that hypothesis as a `RenormalizationTower` and extracts canonical depths.
-/

abbrev IsInfinitelyFastRenormalizable (g : BMol) : Prop :=
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

/-- Build a tower from the legacy satellite-renormalizable hypothesis. -/
noncomputable def satelliteTower_of_satelliteRenormalizable
    (c : ℂ) (h : SatelliteRenormalizable c) :
    RenormalizationTower (parameterToBMol c) :=
  renormalizationTower_of_infinitelyFast (parameterToBMol c) h

/-- Tower-style satellite bridge target used by the current main path. -/
abbrev SatelliteRenormalizableTower (c : ℂ) : Prop :=
  Nonempty (RenormalizationTower (parameterToBMol c))

/-- Legacy satellite data implies the tower-style target. -/
theorem satelliteRenormalizableTower_of_satelliteRenormalizable
    (c : ℂ) (h : SatelliteRenormalizable c) :
    SatelliteRenormalizableTower c :=
  ⟨satelliteTower_of_satelliteRenormalizable c h⟩

noncomputable def satelliteTower (c : ℂ) (h : SatelliteRenormalizableTower c) :
    RenormalizationTower (parameterToBMol c) :=
  Classical.choice h

theorem satelliteTower_depths_cofinal (c : ℂ) (h : SatelliteRenormalizableTower c) :
    MLC.Quadratic.PrincipalNest.Cofinal (RenormalizationTower.cumulativePeriod (satelliteTower c h)) :=
  RenormalizationTower.cumulativePeriod_cofinal (satelliteTower c h)

theorem satelliteTower_depths_monotone (c : ℂ) (h : SatelliteRenormalizableTower c) :
    Monotone (RenormalizationTower.cumulativePeriod (satelliteTower c h)) :=
  RenormalizationTower.cumulativePeriod_monotone (satelliteTower c h)

end

end MLC
