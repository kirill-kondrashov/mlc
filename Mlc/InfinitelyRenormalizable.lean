import Mlc.Quadratic.Complex.Basic
import Mlc.Quadratic.Complex.Puzzle
import Mlc.LcAtOfShrink
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace MLC

open Quadratic Complex Topology Set Filter

/-- Infinitely renormalizable parameters.
    For the purpose of this plan, we define infinitely renormalizable parameters
    as those for which the Yoccoz puzzle moduli converge.
    In a full theory, this would be a theorem (Yoccoz). -/
def InfinitelyRenormalizable (c : ℂ) : Prop :=
  Summable (fun n => modulus (PuzzleAnnulus c n))

/-- MLC holds for infinitely renormalizable parameters (Lyubich). -/
theorem mlc_infinitely_renormalizable (c : ℂ) (hc : c ∈ MandelbrotSet) (h : InfinitelyRenormalizable c) :
    LocallyConnectedAt MandelbrotSet ⟨c, hc⟩ := sorry

end MLC
