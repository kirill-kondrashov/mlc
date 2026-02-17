import Mlc.Quadratic.Complex.PrincipalNestShrink
import Mathlib.Topology.Algebra.InfiniteSum.Order

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
  have h_div : ¬ Summable (fun n =>
      MLC.Quadratic.modulus (MLC.Quadratic.PrincipalNest.dynAnnulus c hdata.depths n)) := by
    intro h_sum
    have h_lim : Filter.Tendsto
        (fun n => MLC.Quadratic.modulus (MLC.Quadratic.PrincipalNest.dynAnnulus c hdata.depths n))
        Filter.atTop (nhds 0) :=
      Summable.tendsto_atTop_zero h_sum
    rw [Metric.tendsto_atTop] at h_lim
    specialize h_lim (m / 2) (by positivity)
    rcases h_lim with ⟨N, hN⟩
    have h_dist : dist
        (MLC.Quadratic.modulus (MLC.Quadratic.PrincipalNest.dynAnnulus c hdata.depths N)) 0 < m / 2 :=
      hN N (le_refl N)
    have h_lbN : m ≤ MLC.Quadratic.modulus (MLC.Quadratic.PrincipalNest.dynAnnulus c hdata.depths N) :=
      hmod N
    have h_nonnegN : 0 ≤ MLC.Quadratic.modulus (MLC.Quadratic.PrincipalNest.dynAnnulus c hdata.depths N) :=
      le_trans (le_of_lt hm) h_lbN
    have h_ltN : MLC.Quadratic.modulus (MLC.Quadratic.PrincipalNest.dynAnnulus c hdata.depths N) < m / 2 := by
      simpa [Real.dist_eq, abs_of_nonneg h_nonnegN] using h_dist
    have hhalf_le : m / 2 ≤ m := by nlinarith [hm]
    exact (not_lt_of_ge h_lbN) (lt_of_lt_of_le h_ltN hhalf_le)
  exact
    MLC.Quadratic.PrincipalNest.para_iInter_eq_singleton_of_principal_modulus_not_summable
      c hc hdata.depths hdata.monotone hdata.cofinal h_div

end

end MLC
