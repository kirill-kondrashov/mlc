import Mlc.RenormalizationTypes

namespace MLC

open Molecule Complex

/-- Infinitely renormalizable parameters admit an infinite sequence of fast renormalizations.
    This links the Yoccoz definition (summable moduli) to the Molecule definition (fast renormalizability).
    
    Proof sketch:
    1. Yoccoz Theorem implies that if moduli are summable, the parameter is not finitely renormalizable.
    2. Therefore, it admits an infinite sequence of renormalizations.
    3. We need to show these correspond to the "Fast" renormalization operator `Rfast`.
    4. This requires aligning the combinatorial definitions of renormalization.
-/
theorem infinitely_renormalizable_implies_fast_tower (c : ℂ) (h : InfinitelyRenormalizable c) :
    ∀ n : ℕ, IsFastRenormalizable ((Rfast^[n]) (parameterToBMol c)) := by
  sorry

end MLC