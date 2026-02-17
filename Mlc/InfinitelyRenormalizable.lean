import Yoccoz.Quadratic.Complex.Basic
import Yoccoz.Quadratic.Complex.Puzzle
import Mlc.Quadratic.Complex.PuzzleLemmas2
import Yoccoz.Yoccoz
import Mlc.LcAtOfShrink
import Mlc.RenormalizationTypes
import Mlc.MoleculeConjectureBridge
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mlc.Quadratic.Complex.PrincipalNestShrink
import Mlc.MoleculeRenormalizationTower
import Mlc.SatelliteRenormalizationTower
import Mlc.PrimitiveModulusDivergence
import Mlc.FastTowerExistence

namespace MLC

open Quadratic Complex Topology Set Filter Molecule



/-- Yoccoz's Theorem (MLC for Finitely Renormalizable Parameters).
    Proved by Jean-Christophe Yoccoz in the early 1990s.
    If the Yoccoz puzzle moduli diverge (Finitely Renormalizable),
    then the intersection of puzzle pieces is a point, implying local connectivity.
    In this skeleton, we take the parameter-plane shrinkage as an explicit hypothesis. -/
theorem mlc_finitely_renormalizable_of_paraPuzzleConnectedData
    (h_conn : ParaPuzzlePieceInterMandelbrotConnectedData)
    (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet)
    (_h : FinitelyRenormalizable c)
    (h_para_shrink : (⋂ n, MLC.Quadratic.ParaPuzzlePieceAt c n) = {c}) :
    MLC.LocallyConnectedAt MLC.Quadratic.MandelbrotSet ⟨c, hc⟩ := by
  exact lc_at_of_shrink_of_data h_conn c hc h_para_shrink

/-- Stronger bridge-target variant routed through
    `ParaPuzzleMandelbrotSubsetData`. -/
theorem mlc_finitely_renormalizable_of_paraPuzzleMandelbrotSubsetData
    (hsub : ParaPuzzleMandelbrotSubsetData)
    (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet)
    (_h : FinitelyRenormalizable c)
    (h_para_shrink : (⋂ n, MLC.Quadratic.ParaPuzzlePieceAt c n) = {c}) :
    MLC.LocallyConnectedAt MLC.Quadratic.MandelbrotSet ⟨c, hc⟩ := by
  exact mlc_finitely_renormalizable_of_paraPuzzleConnectedData
    (Quadratic.para_puzzle_piece_inter_mandelbrot_connected_data_of_mandelbrot_subset_data hsub)
    c hc _h h_para_shrink

/-- Transport-witness bridge-target variant routed through
    `ParaPuzzleInterMandelbrotTransportData`. -/
theorem mlc_finitely_renormalizable_of_paraPuzzleTransportData
    (htr : ParaPuzzleInterMandelbrotTransportData)
    (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet)
    (_h : FinitelyRenormalizable c)
    (h_para_shrink : (⋂ n, MLC.Quadratic.ParaPuzzlePieceAt c n) = {c}) :
    MLC.LocallyConnectedAt MLC.Quadratic.MandelbrotSet ⟨c, hc⟩ := by
  exact mlc_finitely_renormalizable_of_paraPuzzleConnectedData
    (Quadratic.para_puzzle_piece_inter_mandelbrot_connected_data_of_transport_data htr)
    c hc _h h_para_shrink

/-- Axiom-backed wrapper for `mlc_finitely_renormalizable_of_paraPuzzleConnectedData`. -/
theorem mlc_finitely_renormalizable (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet)
    (_h : FinitelyRenormalizable c)
    (h_para_shrink : (⋂ n, MLC.Quadratic.ParaPuzzlePieceAt c n) = {c}) :
    MLC.LocallyConnectedAt MLC.Quadratic.MandelbrotSet ⟨c, hc⟩ := by
  exact mlc_finitely_renormalizable_of_paraPuzzleConnectedData
    Quadratic.para_puzzle_piece_inter_mandelbrot_connected_data_of_axiom
    c hc _h h_para_shrink

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
      PrimitiveRenormalizable c ∨ SatelliteRenormalizableTower c)
    (h_bridge :
      MoleculeConjectureRefined →
      MLC.Quadratic.PuzzleBoundaryMotionHyp →
      ∀ (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet) (_h : SatelliteRenormalizableTower c),
        MLC.LocallyConnectedAt MLC.Quadratic.MandelbrotSet ⟨c, hc⟩)
    (h_motion : MLC.Quadratic.PuzzleBoundaryMotionHyp)
    (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet) (h : InfinitelyRenormalizable c) :
    MLC.LocallyConnectedAt MLC.Quadratic.MandelbrotSet ⟨c, hc⟩ := by
  cases h_classify c h with
  | inl h_prim => exact mlc_primitive_renormalizable_ax c hc h_prim
  | inr h_tower =>
      exact molecule_conjecture_implies_mlc_satellite_of_tower h_bridge h_motion c hc h_tower





/-- Existence of an infinite sequence of renormalizations from satellite data. -/
theorem exists_renormalization_tower_sequence_of_satellite
    (c : ℂ) (h_sat : SatelliteRenormalizableTower c) :
    ∃ (g : ℕ → BMol), g 0 = parameterToBMol c ∧ 
      ∀ n, Nonempty (RenormalizationRelation (g n) (g (n+1))) := by
  let T : RenormalizationTower (parameterToBMol c) := satelliteTower c h_sat
  exact ⟨T.gₙ, T.g0, T.step⟩

/-- Existence of an infinite sequence of renormalizations for IR parameters. -/
theorem exists_renormalization_tower_sequence
    (h_tower_data : InfinitelyRenormalizableHasTowerData)
    (c : ℂ) (h : MLC.InfinitelyRenormalizable c) :
    ∃ (g : ℕ → BMol), g 0 = parameterToBMol c ∧
      ∀ n, Nonempty (RenormalizationRelation (g n) (g (n+1))) := by
  exact exists_renormalization_tower_sequence_of_satellite c
    (tower_of_infinitely_renormalizable h_tower_data c h)

/-- Infinitely renormalizable parameters admit a renormalization tower.
    This is a consequence of Yoccoz's work: if puzzle moduli diverge, the intersection
    of puzzle pieces is a point (finitely renormalizable); if they converge,
    the critical point must be involved in an infinite sequence of renormalizations. -/
lemma infinitely_renormalizable_has_tower
    (h_tower_data : InfinitelyRenormalizableHasTowerData)
    (c : ℂ) (h : InfinitelyRenormalizable c) :
    ∃ (_T : RenormalizationTower (parameterToBMol c)), True := by
  exact ⟨satelliteTower c (tower_of_infinitely_renormalizable h_tower_data c h), True.intro⟩

/-- Each renormalization step in a tower is either primitive or satellite.
    In the quadratic case, these two combinatorial types are exhaustive. -/
lemma tower_step_classification {g : BMol} (T : RenormalizationTower g) (n : ℕ) :
    IsPrimitive (T.rel n) ∨ IsSatellite (T.rel n) := by
  -- By definition, primitive is the negation of satellite.
  rcases Classical.em (IsSatellite (T.rel n)) with h | h
  · right; exact h
  · left; exact h



/-- A tower with infinitely many primitive renormalizations implies the parameter is of primitive type. -/
lemma primitive_tower_implies_primitive (c : ℂ) (T : RenormalizationTower (parameterToBMol c))
    (_h_inf_prim : {n | IsPrimitive (T.rel n)}.Infinite) :
    PrimitiveRenormalizable c := by
  -- Lyubich proved that if there are infinitely many primitive renormalizations,
  -- then MLC holds (the critical puzzle piece shrinks to a point).
  -- The proof uses the fact that primitive renormalizations produce 'large' annuli
  -- in the principal nest, leading to modulus divergence for the critical piece.
  intro hc
  
  -- 1. Construct the principal nest depths from the tower.
  let depths := T.cumulativePeriod
  have h_mono : Monotone depths := T.cumulativePeriod_monotone
  have h_cof : MLC.Quadratic.PrincipalNest.Cofinal depths := T.cumulativePeriod_cofinal

  -- 2. Divergence of moduli (Lyubich's Theorem).
  have h_div : ¬ Summable (fun n => LyubichModulus (MLC.Quadratic.PrincipalNest.dynAnnulus c depths n)) :=
    primitive_modulus_divergence c T _h_inf_prim

  -- 3. Apply Grötzsch criterion to get parameter shrinkage.
  -- Ideally, we would use `para_iInter_eq_singleton_of_principal_modulus_not_summable`,
  -- but that requires `modulus` (Gaussian). Here we have `LyubichModulus` (Conformal proxy).
  -- We assume the bridge: Divergence of LyubichModulus => Shrinkage.
  have h_shrink : (⋂ n, MLC.Quadratic.ParaPuzzlePieceAt c n) = {c} :=
    primitive_shrinkage_of_divergence c hc T h_div

  -- 4. Shrinkage implies local connectivity.
  exact lc_at_of_shrink c hc h_shrink

/-- A tower that eventually consists only of satellite renormalizations implies the parameter is of satellite type. -/
lemma satellite_tower_implies_satellite (c : ℂ) (_h : InfinitelyRenormalizable c) (T : RenormalizationTower (parameterToBMol c))
    (_h_ev_sat : ∀ᶠ n in Filter.atTop, IsSatellite (T.rel n)) :
    SatelliteRenormalizableTower c := by
  exact ⟨T⟩

/-- Combinatorial dichotomy: a sequence of binary choices is either infinitely often 'left' or eventually always 'right'. -/
lemma combinatorial_dichotomy {p q : ℕ → Prop} (h : ∀ n, p n ∨ q n) :
    {n | p n}.Infinite ∨ ∀ᶠ n in Filter.atTop, q n := by
  by_cases hp : {n | p n}.Infinite
  · left; exact hp
  · right
    rw [Set.not_infinite] at hp
    -- A finite set of naturals is bounded above.
    let s := hp.toFinset
    rw [Filter.eventually_atTop]
    by_cases hs : s.Nonempty
    · let N := s.max' hs
      use N + 1
      intro n hn
      have hnp : ¬ p n := by
        intro hpn
        have hns : n ∈ s := by simp [s, hpn]
        have hle : n ≤ N := s.le_max' n hns
        linarith
      rcases h n with hp_true | hq_true
      · contradiction
      · exact hq_true
    · -- s is empty, so p n is never true
      use 0
      intro n _
      rcases h n with hp_true | hq_true
      · have hns : n ∈ s := by simp [s, hp_true]
        have h_empty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
        rw [h_empty] at hns
        simp at hns
      · exact hq_true

/-- Classification wrapper used by the main MLC strategy.
    In the current formalization this is discharged through the fast-tower route,
    yielding the satellite branch directly. -/
theorem classify_infinitely_renormalizable
    (h_tower_data : InfinitelyRenormalizableHasTowerData)
    (c : ℂ) (h : InfinitelyRenormalizable c) :
    PrimitiveRenormalizable c ∨ SatelliteRenormalizableTower c := by
  exact Or.inr (tower_of_infinitely_renormalizable h_tower_data c h)

end MLC
