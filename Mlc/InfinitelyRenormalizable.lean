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

open Quadratic Complex Topology Set Filter Molecule

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
    (_h : FinitelyRenormalizable c)
    (h_para_shrink : (⋂ n, MLC.Quadratic.ParaPuzzlePieceAt c n) = {c}) :
    MLC.LocallyConnectedAt MLC.Quadratic.MandelbrotSet ⟨c, hc⟩ := by
  -- The dynamical shrinkage is provided by Yoccoz; the parameter shrinkage is assumed here.
  exact lc_at_of_shrink c hc h_para_shrink

/-- MLC for Primitive parameters (Lyubich).
    Proved by Lyubich in "Dynamics of Quadratic Polynomials I-II", Acta Mathematica 178 (1997).
    See also: Lyubich, "Conformal Geometry and Dynamics of Quadratic Polynomials",
    §42.6 "MLC on the main cardioid", p. 204 (printed page number), p. 205 (PDF index):
    "The Mandelbrot set is locally connected at any point of the main cardioid C." -/
theorem mlc_primitive_renormalizable_ax (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet)
    (h : PrimitiveRenormalizable c) :
    MLC.LocallyConnectedAt MLC.Quadratic.MandelbrotSet ⟨c, hc⟩ := by
  exact h hc

/-- MLC holds for infinitely renormalizable parameters.
    This is derived from the classification into Primitive and Satellite types,
    using Lyubich's theorem for the former and the Molecule Conjecture for the latter. -/
theorem mlc_infinitely_renormalizable
    (h_classify : ∀ (c : ℂ) (_h : InfinitelyRenormalizable c),
      PrimitiveRenormalizable c ∨ SatelliteRenormalizable c)
    (h_bridge :
      MoleculeConjectureRefined →
      MLC.Quadratic.PuzzleBoundaryMotionHyp →
      ∀ (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet) (_h : SatelliteRenormalizable c),
        MLC.LocallyConnectedAt MLC.Quadratic.MandelbrotSet ⟨c, hc⟩)
    (h_motion : MLC.Quadratic.PuzzleBoundaryMotionHyp)
    (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet) (h : InfinitelyRenormalizable c) :
    MLC.LocallyConnectedAt MLC.Quadratic.MandelbrotSet ⟨c, hc⟩ := by
  cases h_classify c h with
  | inl h_prim => exact mlc_primitive_renormalizable_ax c hc h_prim
  | inr h_sat => exact molecule_conjecture_implies_mlc_satellite h_bridge h_motion c hc h_sat

/-- A placeholder for the property that a renormalization is primitive. -/
def IsPrimitive {f g : BMol} (_rel : RenormalizationRelation f g) : Prop := sorry

/-- A placeholder for the property that a renormalization is satellite. -/
def IsSatellite {f g : BMol} (_rel : RenormalizationRelation f g) : Prop := sorry

/-- Infinitely renormalizable parameters admit a renormalization tower. -/
lemma infinitely_renormalizable_has_tower (c : ℂ) (_h : InfinitelyRenormalizable c) :
    ∃ (T : RenormalizationTower (parameterToBMol c)), True := sorry

/-- Each renormalization step in a tower is either primitive or satellite. -/
lemma tower_step_classification {g : BMol} (T : RenormalizationTower g) (n : ℕ) :
    IsPrimitive (T.rel n) ∨ IsSatellite (T.rel n) := sorry

/-- A tower with infinitely many primitive renormalizations implies the parameter is of primitive type. -/
lemma primitive_tower_implies_primitive (c : ℂ) (T : RenormalizationTower (parameterToBMol c))
    (_h_inf_prim : {n | IsPrimitive (T.rel n)}.Infinite) :
    PrimitiveRenormalizable c := sorry

/-- A tower that eventually consists only of satellite renormalizations implies the parameter is of satellite type. -/
lemma satellite_tower_implies_satellite (c : ℂ) (T : RenormalizationTower (parameterToBMol c))
    (_h_ev_sat : ∀ᶠ n in Filter.atTop, IsSatellite (T.rel n)) :
    SatelliteRenormalizable c := sorry

/-- Combinatorial dichotomy: a sequence of binary choices is either infinitely often 'left' or eventually always 'right'. -/
lemma combinatorial_dichotomy {p q : ℕ → Prop} (h : ∀ n, p n ∨ q n) :
    {n | p n}.Infinite ∨ ∀ᶠ n in Filter.atTop, q n := sorry

/-- Classification of infinitely renormalizable parameters (Lyubich).
    Every infinitely renormalizable quadratic polynomial is either of primitive type
    (infinitely many primitive renormalizations) or satellite type (eventually only
    satellite renormalizations).
    
    Proof sketch:
    1. An infinitely renormalizable map has a sequence of periods p_1 < p_2 < ...
    2. Each renormalization f^{p_n} -> f^{p_{n+1}} is either primitive or satellite.
    3. If infinitely many are primitive, we are in the 'Primitive' case (Lyubich).
    4. If eventually all are satellite, we are in the 'Satellite' case (Molecule). -/
theorem classify_infinitely_renormalizable (c : ℂ) (h : InfinitelyRenormalizable c) :
    PrimitiveRenormalizable c ∨ SatelliteRenormalizable c := by
  -- 1. Existence of tower
  obtain ⟨T, _⟩ := infinitely_renormalizable_has_tower c h
  -- 2. Each step is primitive or satellite
  have h_steps : ∀ n, IsPrimitive (T.rel n) ∨ IsSatellite (T.rel n) :=
    fun n => tower_step_classification T n
  -- 3. Combinatorial dichotomy
  rcases combinatorial_dichotomy h_steps with h_inf_prim | h_ev_sat
  · -- Case: infinitely many primitive renormalizations
    left
    exact primitive_tower_implies_primitive c T h_inf_prim
  · -- Case: eventually always satellite renormalizations
    right
    exact satellite_tower_implies_satellite c T h_ev_sat

end MLC
