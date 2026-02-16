import Mlc.RenormalizationTypes

namespace MLC

open Molecule Complex

/-- Infinitely renormalizable parameters admit an infinite sequence of fast renormalizations.
    This links the Yoccoz definition (summable moduli) to the Molecule definition (fast renormalizability).
-/
axiom infinitely_renormalizable_implies_fast_tower (c : ℂ) (h : InfinitelyRenormalizable c) :
    ∀ n : ℕ, IsFastRenormalizable ((Rfast^[n]) (parameterToBMol c))

/-- Minimal replacement target for the IR bridge used by the main strategy:
    infinitely renormalizable parameters are satellite-renormalizable. -/
def InfinitelyRenormalizableImpliesSatelliteData : Prop :=
  ∀ c, InfinitelyRenormalizable c → SatelliteRenormalizable c

/-- Current axiom-backed construction of the IR replacement target. -/
def infinitely_renormalizable_implies_satellite_data_via_axiom :
    InfinitelyRenormalizableImpliesSatelliteData :=
  fun c h => infinitely_renormalizable_implies_fast_tower c h

end MLC
