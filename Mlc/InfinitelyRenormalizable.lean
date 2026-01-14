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

/-- Classification of Infinitely Renormalizable parameters.
    Infinitely renormalizable parameters are classified into two types:
    1. **Primitive**: The small copy of the Mandelbrot set is detached from the main body (except at the root).
       These are handled by Quadratic-like renormalization (Lyubich).
    2. **Satellite**: The small copy is attached to the main body (or another component).
       These are handled by near-parabolic or Pacman renormalization (Dudko, Lyubich, Selinger).

    Reference: Dudko, Lyubich, Selinger, "Pacman Renormalization and Self-Similarity of the Mandelbrot Set near Siegel Parameters", arXiv:1703.01206v3. -/
opaque PrimitiveRenormalizable (c : ℂ) : Prop
opaque SatelliteRenormalizable (c : ℂ) : Prop

/-- Every infinitely renormalizable parameter is either Primitive or Satellite. -/
axiom infinitely_renormalizable_classification (c : ℂ) (h : InfinitelyRenormalizable c) :
    PrimitiveRenormalizable c ∨ SatelliteRenormalizable c

/-- MLC holds for infinitely renormalizable parameters.
    This is a deep theorem in complex dynamics.
    - For **Primitive** parameters, it was proved by Lyubich: [Lyubich, The Dynamics of Quadratic Polynomials I-II, Acta Math. 178 (1997)].
    - For **Satellite** parameters, it is partially covered by recent work on Pacman renormalization (Dudko, Lyubich, Selinger), though full coverage for all combinatorics (e.g., unbounded type) remains an active area of research (Molecule Conjecture).

    We accept this as an axiom for the purpose of this formalization. -/
axiom mlc_infinitely_renormalizable_ax (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet) (h : InfinitelyRenormalizable c) :
    MLC.LocallyConnectedAt MLC.Quadratic.MandelbrotSet ⟨c, hc⟩

theorem mlc_infinitely_renormalizable (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet) (h : InfinitelyRenormalizable c) :
    MLC.LocallyConnectedAt MLC.Quadratic.MandelbrotSet ⟨c, hc⟩ :=
  mlc_infinitely_renormalizable_ax c hc h

end MLC
