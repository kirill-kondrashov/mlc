import Yoccoz.Quadratic.Complex.Basic
import Yoccoz.Quadratic.Complex.Puzzle
import Mlc.Quadratic.Complex.PuzzleLemmas2
import Mlc.Quadratic.Complex.PuzzleBoundaryMotion
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



/-- Generic finite-side endpoint: once a Mandelbrot parameter is equipped with a
    connected window family shrinking to the basepoint, the finitely
    renormalizable hypothesis is no longer used by the topological LC consumer.
    It is retained only as a theorem-facing compatibility parameter. -/
theorem mlc_finitely_renormalizable_of_connectednessWindowData
    (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet)
    (_h : FinitelyRenormalizable c)
    (W K : ℕ → Set ℂ)
    (hW : ConnectednessWindowParameterPieceData c W K) :
    MLC.LocallyConnectedAt MLC.Quadratic.MandelbrotSet ⟨c, hc⟩ := by
  exact lc_at_of_connectednessWindow_family_data c hc W K hW

/-- Generic finite-side endpoint specialized to a parameter-piece family. -/
theorem mlc_finitely_renormalizable_of_parameterPieceData
    (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet)
    (_h : FinitelyRenormalizable c)
    (P : ℕ → Set ℂ)
    (hP : ParameterPieceLcAtData c P) :
    MLC.LocallyConnectedAt MLC.Quadratic.MandelbrotSet ⟨c, hc⟩ := by
  exact lc_at_of_shrink_of_family_data c hc P hP

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
  exact mlc_finitely_renormalizable_of_parameterPieceData c hc _h
    (fun n => MLC.Quadratic.ParaPuzzlePieceAt c n)
    { piece_open := fun n => para_puzzle_piece_open c n
      base_mem := by
        intro n
        have hc_in_inter : c ∈ ⋂ k, MLC.Quadratic.ParaPuzzlePieceAt c k := by
          rw [h_para_shrink]
          exact Set.mem_singleton c
        exact Set.mem_iInter.mp hc_in_inter n
      basis := fun U hU => para_puzzle_piece_basis c h_para_shrink U hU
      inter_mandelbrot_connected := fun n => h_conn c hc n }

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

/-- Transport-witness bridge-target variant routed through the generic
    connected-window interface. -/
theorem mlc_finitely_renormalizable_of_paraPuzzleTransportData
    (htr : ParaPuzzleInterMandelbrotTransportData)
    (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet)
    (_h : FinitelyRenormalizable c)
    (h_para_shrink : (⋂ n, MLC.Quadratic.ParaPuzzlePieceAt c n) = {c}) :
    MLC.LocallyConnectedAt MLC.Quadratic.MandelbrotSet ⟨c, hc⟩ := by
  exact mlc_finitely_renormalizable_of_connectednessWindowData c hc _h
    (fun n => MLC.Quadratic.ParaPuzzlePieceAt c n)
    (fun n => htr.transportSet c n)
    (connectednessWindowData_of_paraPuzzleTransportData htr c hc h_para_shrink)

/-- Existential-transport bridge-target variant routed through
    `ParaPuzzleInterMandelbrotTransportExistsData`. -/
theorem mlc_finitely_renormalizable_of_paraPuzzleTransportExistsData
    (hex : ParaPuzzleInterMandelbrotTransportExistsData)
    (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet)
    (_h : FinitelyRenormalizable c)
    (h_para_shrink : (⋂ n, MLC.Quadratic.ParaPuzzlePieceAt c n) = {c}) :
    MLC.LocallyConnectedAt MLC.Quadratic.MandelbrotSet ⟨c, hc⟩ := by
  exact mlc_finitely_renormalizable_of_paraPuzzleConnectedData
    (Quadratic.para_puzzle_piece_inter_mandelbrot_connected_data_of_transport_exists_data hex)
    c hc _h h_para_shrink

/-- Axiom-backed wrapper for `mlc_finitely_renormalizable_of_paraPuzzleConnectedData`. -/
theorem mlc_finitely_renormalizable (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet)
    (_h : FinitelyRenormalizable c)
    (h_para_shrink : (⋂ n, MLC.Quadratic.ParaPuzzlePieceAt c n) = {c}) :
    MLC.LocallyConnectedAt MLC.Quadratic.MandelbrotSet ⟨c, hc⟩ := by
  exact mlc_finitely_renormalizable_of_paraPuzzleTransportExistsData
    Quadratic.para_puzzle_transport_exists_data_of_motion_default
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

/-- Primitive tower data imply the primitive local-connectivity endpoint. -/
lemma primitiveRenormalizable_of_data (c : ℂ)
    (h : PrimitiveRenormalizableData c) :
    PrimitiveRenormalizable c := by
  rcases h with ⟨T, h_inf_prim⟩
  intro hc
  have h_div :
      ¬ Summable (fun n => LyubichModulus (MLC.Quadratic.PrincipalNest.dynAnnulus c T.cumulativePeriod n)) :=
    primitive_modulus_divergence c T h_inf_prim
  have h_shrink : (⋂ n, MLC.Quadratic.ParaPuzzlePieceAt c n) = {c} :=
    primitive_shrinkage_of_divergence c hc T h_div
  exact lc_at_of_shrink c hc h_shrink

/-- Intended constructive primitive route: if the same tower carries genuine
    conformal-modulus lower bounds on infinitely many primitive levels, then the
    primitive local-connectivity endpoint follows without the Lyubich proxy
    bridge. -/
lemma primitiveRenormalizable_of_lowerBoundData
    (c : ℂ) (T : RenormalizationTower (parameterToBMol c))
    (h_inf_prim : {n | IsPrimitive (T.rel n)}.Infinite)
    (h_lb : PrimitiveModulusLowerBoundData c T) :
    PrimitiveRenormalizable c := by
  intro hc
  have h_shrink : (⋂ n, MLC.Quadratic.ParaPuzzlePieceAt c n) = {c} :=
    primitive_shrinkage_of_lower_bound c hc T h_lb h_inf_prim
  exact lc_at_of_shrink c hc h_shrink

/-- Eventual bounded primitive modulus control is already sufficient for the
    primitive local-connectivity endpoint. -/
lemma primitiveRenormalizable_of_eventualLowerBoundData
    (c : ℂ) (T : RenormalizationTower (parameterToBMol c))
    (h_inf_prim : {n | IsPrimitive (T.rel n)}.Infinite)
    (h_lb : EventualPrimitiveModulusLowerBoundData c T) :
    PrimitiveRenormalizable c := by
  intro hc
  have h_shrink : (⋂ n, MLC.Quadratic.ParaPuzzlePieceAt c n) = {c} :=
    primitive_shrinkage_of_eventual_lower_bound c hc T h_lb h_inf_prim
  exact lc_at_of_shrink c hc h_shrink

/-- MLC holds for infinitely renormalizable parameters.
    This is derived from the classification into Primitive and Satellite types,
    using Lyubich's theorem for the former and the Molecule Conjecture for the latter. -/
theorem mlc_infinitely_renormalizable
    (h_classify : ∀ (c : ℂ) (_hc : c ∈ MLC.Quadratic.MandelbrotSet)
      (_h : InfinitelyRenormalizable c),
      PrimitiveRenormalizable c ∨ SatelliteRenormalizableTower c)
    (h_bridge :
      MoleculeConjectureRefined →
      ∀ (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet) (_h : SatelliteRenormalizableTower c),
        MLC.LocallyConnectedAt MLC.Quadratic.MandelbrotSet ⟨c, hc⟩)
    (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet) (h : InfinitelyRenormalizable c) :
    MLC.LocallyConnectedAt MLC.Quadratic.MandelbrotSet ⟨c, hc⟩ := by
  cases h_classify c hc h with
  | inl h_prim => exact mlc_primitive_renormalizable_ax c hc h_prim
  | inr h_tower =>
      exact molecule_conjecture_implies_mlc_satellite_of_tower h_bridge c hc h_tower





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
  exact primitiveRenormalizable_of_data c ⟨T, _h_inf_prim⟩

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
theorem classify_infinitely_renormalizable_of_noTowerImpliesPrimitive
    (h_noTowerPrim :
      ∀ (c : ℂ) (_hc : c ∈ MLC.Quadratic.MandelbrotSet)
        (_h : InfinitelyRenormalizable c),
        ¬ SatelliteRenormalizableTower c → PrimitiveRenormalizable c)
    (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet) (h : InfinitelyRenormalizable c) :
    PrimitiveRenormalizable c ∨ SatelliteRenormalizableTower c := by
  by_cases hTower : SatelliteRenormalizableTower c
  · exact Or.inr hTower
  · exact Or.inl (h_noTowerPrim c hc h hTower)

/-- If satellite towers are excluded on `M`, Track-1 no-tower implication yields
    the IR classification through the primitive branch. -/
theorem classify_infinitely_renormalizable_of_noTowerImpliesPrimitive_of_noTowerOnM
    (h_noTowerPrim :
      ∀ (c : ℂ) (_hc : c ∈ MLC.Quadratic.MandelbrotSet)
        (_h : InfinitelyRenormalizable c),
        ¬ SatelliteRenormalizableTower c → PrimitiveRenormalizable c)
    (h_noTowerOnM :
      ∀ (c : ℂ), c ∈ MLC.Quadratic.MandelbrotSet → ¬ SatelliteRenormalizableTower c)
    (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet) (h : InfinitelyRenormalizable c) :
    PrimitiveRenormalizable c ∨ SatelliteRenormalizableTower c := by
  exact Or.inl (h_noTowerPrim c hc h (h_noTowerOnM c hc))

/-- Classification wrapper used by the main MLC strategy.
    In the current formalization this is discharged through the fast-tower route,
    yielding the satellite branch directly. -/
theorem classify_infinitely_renormalizable
    (h_tower_data : InfinitelyRenormalizableHasTowerData)
    (c : ℂ) (h : InfinitelyRenormalizable c) :
    PrimitiveRenormalizable c ∨ SatelliteRenormalizableTower c := by
  exact Or.inr (tower_of_infinitely_renormalizable h_tower_data c h)

end MLC
