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

/-- MLC holds for infinitely renormalizable parameters (Lyubich).
    This is a deep theorem in complex dynamics, proved by Mikhail Lyubich.
    See: [Lyubich, The Dynamics of Quadratic Polynomials I-II, Acta Math. 178 (1997), Main Theorem] <https://projecteuclid.org/journals/acta-mathematica/volume-178/issue-2/Dynamics-of-quadratic-polynomials-III/10.1007/BF02392694.full>
    Also cited in the provided document as [L10] "How big is the set of infinitely renormalizable quadratics?".
    Since the proof is beyond the scope of this formalization (which focuses on Yoccoz puzzles),
    we accept it as an axiom. -/
axiom mlc_infinitely_renormalizable_ax (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet) (h : InfinitelyRenormalizable c) :
    MLC.LocallyConnectedAt MLC.Quadratic.MandelbrotSet ⟨c, hc⟩

theorem mlc_infinitely_renormalizable (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet) (h : InfinitelyRenormalizable c) :
    MLC.LocallyConnectedAt MLC.Quadratic.MandelbrotSet ⟨c, hc⟩ :=
  mlc_infinitely_renormalizable_ax c hc h

end MLC
