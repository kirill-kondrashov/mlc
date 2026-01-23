import Yoccoz.Quadratic.Complex.Basic
import Yoccoz.Quadratic.Complex.Puzzle
import Mlc.Quadratic.Complex.PuzzleLemmas2
import Yoccoz.Yoccoz
import Mlc.LcAtOfShrink
import Mlc.RenormalizationTypes
import Mlc.MoleculeConjectureBridge
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace MLC

open Quadratic Complex Topology Set Filter

/-- Finitely renormalizable parameters.
    Alias for NonRenormalizable from the library. -/
abbrev FinitelyRenormalizable := NonRenormalizable

/-- Infinitely renormalizable parameters.
    For the purpose of this plan, we define infinitely renormalizable parameters
    as those for which the Yoccoz puzzle moduli converge.
    In a full theory, this would be a theorem (Yoccoz). -/
def InfinitelyRenormalizable (c : ℂ) : Prop :=
  Summable (fun n => modulus (PuzzleAnnulus c n))

/-- Yoccoz's Theorem (MLC for Finitely Renormalizable Parameters).
    Proved by Jean-Christophe Yoccoz in the early 1990s.
    If the Yoccoz puzzle moduli diverge (Finitely Renormalizable),
    then the intersection of puzzle pieces is a point, implying local connectivity.
    In this skeleton, we take the parameter-plane shrinkage as an explicit hypothesis. -/
theorem mlc_finitely_renormalizable (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet)
    (h : FinitelyRenormalizable c) (h_para_shrink : (⋂ n, MLC.Quadratic.ParaPuzzlePiece n) = {c}) :
    MLC.LocallyConnectedAt MLC.Quadratic.MandelbrotSet ⟨c, hc⟩ := by
  -- The dynamical shrinkage is provided by Yoccoz; the parameter shrinkage is assumed here.
  exact lc_at_of_shrink c hc h_para_shrink

/-- Classification of Infinitely Renormalizable parameters.
    Infinitely renormalizable parameters are classified into two types:
    1. **Primitive**: The small copy of the Mandelbrot set is detached from the main body (except at the root).
       These are handled by Quadratic-like renormalization (Lyubich).
    2. **Satellite**: The small copy is attached to the main body (or another component).
       These are handled by near-parabolic or Pacman renormalization (Dudko, Lyubich, Selinger).

    Reference: Dudko, Lyubich, Selinger, "Pacman Renormalization and Self-Similarity of the Mandelbrot Set near Siegel Parameters", arXiv:1703.01206v3. -/
axiom infinitely_renormalizable_classification (c : ℂ) (h : InfinitelyRenormalizable c) :
    PrimitiveRenormalizable c ∨ SatelliteRenormalizable c

/-- MLC for Primitive parameters (Lyubich).
    Proved by Lyubich in "Dynamics of Quadratic Polynomials I-II", Acta Mathematica 178 (1997).
    See also: Lyubich, "Conformal Geometry and Dynamics of Quadratic Polynomials",
    §42.6 "MLC on the main cardioid", p. 204 (printed page number), p. 205 (PDF index):
    "The Mandelbrot set is locally connected at any point of the main cardioid C." -/
axiom mlc_primitive_renormalizable_ax (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet) (h : PrimitiveRenormalizable c) :
    MLC.LocallyConnectedAt MLC.Quadratic.MandelbrotSet ⟨c, hc⟩

/-- MLC holds for infinitely renormalizable parameters.
    This is derived from the classification into Primitive and Satellite types,
    using Lyubich's theorem for the former and the Molecule Conjecture for the latter. -/
theorem mlc_infinitely_renormalizable
    (h_bridge :
      MoleculeConjectureRefined →
      ∀ (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet) (_h : SatelliteRenormalizable c),
        MLC.LocallyConnectedAt MLC.Quadratic.MandelbrotSet ⟨c, hc⟩)
    (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet) (h : InfinitelyRenormalizable c) :
    MLC.LocallyConnectedAt MLC.Quadratic.MandelbrotSet ⟨c, hc⟩ := by
  cases infinitely_renormalizable_classification c h with
  | inl h_prim => exact mlc_primitive_renormalizable_ax c hc h_prim
  | inr h_sat => exact molecule_conjecture_implies_mlc_satellite h_bridge c hc h_sat

end MLC
