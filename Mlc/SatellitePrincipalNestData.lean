import Mlc.Quadratic.Complex.PrincipalNestShrink

namespace MLC

open Quadratic Complex Topology Set Filter

noncomputable section

/-!
`SatellitePrincipalNestData` is the concrete target package we ultimately need to construct
from the Molecule Conjecture + satellite renormalizability:

* a cofinal, monotone depth selection (the principal nest),
* and a uniform lower bound on the moduli of the corresponding annuli.

Once this data exists, shrinkage of parameter pieces follows by Grötzsch's criterion.
-/

structure SatellitePrincipalNestData (c : ℂ) where
  depths : ℕ → ℕ
  monotone : Monotone depths
  cofinal : MLC.Quadratic.PrincipalNest.Cofinal depths
  modulus_lower :
    ∃ m : ℝ, 0 < m ∧ ∀ n : ℕ, m ≤ MLC.Quadratic.modulus (MLC.Quadratic.PrincipalNest.dynAnnulus c depths n)

theorem paraPuzzle_shrink_of_satellitePrincipalNestData (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet)
    (hdata : SatellitePrincipalNestData c) :
    (⋂ n, MLC.Quadratic.ParaPuzzlePieceAt c n) = {c} := by
  rcases hdata.modulus_lower with ⟨m, hm, hmod⟩
  exact
    MLC.Quadratic.PrincipalNest.para_iInter_eq_singleton_of_principal_modulus_lower_bound
      c hc hdata.depths hdata.monotone hdata.cofinal hm hmod

end

end MLC
