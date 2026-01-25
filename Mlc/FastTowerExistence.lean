import Mlc.RenormalizationTypes

namespace MLC

open Molecule Complex

/-- Infinitely renormalizable parameters admit an infinite sequence of fast renormalizations.
    This links the Yoccoz definition (summable moduli) to the Molecule definition (fast renormalizability).
-/
axiom infinitely_renormalizable_implies_fast_tower (c : ℂ) (h : InfinitelyRenormalizable c) :
    ∀ n : ℕ, IsFastRenormalizable ((Rfast^[n]) (parameterToBMol c))

end MLC