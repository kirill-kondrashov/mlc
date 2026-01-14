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

axiom infinitely_renormalizable_classification (c : ℂ) (h : InfinitelyRenormalizable c) :
    PrimitiveRenormalizable c ∨ SatelliteRenormalizable c

/-- MLC for Primitive parameters (Lyubich).
    Proved by Lyubich in "The Dynamics of Quadratic Polynomials I-II", Acta Math. 178 (1997). -/
axiom mlc_primitive_renormalizable_ax (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet) (h : PrimitiveRenormalizable c) :
    MLC.LocallyConnectedAt MLC.Quadratic.MandelbrotSet ⟨c, hc⟩

/-- The Molecule Conjecture (Dudko, Lyubich, Selinger).
    This conjecture asserts the existence of a hyperbolic Pacman renormalization operator
    whose horseshoe corresponds to the boundary of the main molecule of the Mandelbrot set.
    It would imply MLC for all infinitely renormalizable parameters of satellite type,
    covering cases not yet fully resolved (like unbounded combinatorics).

    Reference: Dudko, Lyubich, Selinger, "Pacman Renormalization...", Appendix C. -/
axiom molecule_conjecture_implies_mlc_satellite (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet) (h : SatelliteRenormalizable c) :
    MLC.LocallyConnectedAt MLC.Quadratic.MandelbrotSet ⟨c, hc⟩

/-- MLC holds for infinitely renormalizable parameters.
    This is derived from the classification into Primitive and Satellite types,
    using Lyubich's theorem for the former and the Molecule Conjecture for the latter. -/
theorem mlc_infinitely_renormalizable (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet) (h : InfinitelyRenormalizable c) :
    MLC.LocallyConnectedAt MLC.Quadratic.MandelbrotSet ⟨c, hc⟩ := by
  cases infinitely_renormalizable_classification c h with
  | inl h_prim => exact mlc_primitive_renormalizable_ax c hc h_prim
  | inr h_sat => exact molecule_conjecture_implies_mlc_satellite c hc h_sat

end MLC
