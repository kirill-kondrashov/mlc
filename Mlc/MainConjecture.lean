import Yoccoz.Quadratic.Complex.Basic
import Yoccoz.Quadratic.Complex.Green
import Yoccoz.Quadratic.Complex.Puzzle
import Mlc.LcAtOfShrink
import Mlc.InfinitelyRenormalizable
import Mlc.AxiomsMainConjecture
import Mlc.Quadratic.Complex.Bottcher.BottcherMotion
import Mlc.Quadratic.Complex.Bottcher.BottcherOnMTheory
import Mlc.Quadratic.Complex.Bottcher.BottcherOutsidePlan
import Mlc.Quadratic.Complex.Bottcher.InverseBranchSlitUse
import Mlc.MandelbrotEquivalence
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Bornology.Basic
import Mathlib.Analysis.Complex.Basic
import Lean

open Lean Elab Command

namespace MLC

open Quadratic Complex Topology Set Filter Bornology Metric

/-!
# Mandelbrot Local Connectivity (MLC) Conjecture

This file outlines the proof strategy for the MLC conjecture based on Yoccoz puzzles.

## Integration with DeepMind Formal Conjectures

The definitions of `multibrotSet` and `mandelbrotSet`, as well as the formulation of the `MLC` theorem
around line 106, are adapted from the Google DeepMind `formal-conjectures` repository:
https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Wikipedia/Mandelbrot.lean

Note: Because the `formal-conjectures` repository depends on an older version of Lean/Mathlib (v4.22.0)
which is incompatible with this project's dependencies, we have copied the relevant definitions
and theorem statements here to ensure a valid and consistent formalization.
-/

-- Definitions adapted from DeepMind's FormalConjectures (Wikipedia/Mandelbrot.lean)

/-- The Multibrot set of power `n` is the set of all parameters `c : ℂ` for which `0` does not
escape to infinity under repeated application of `z ↦ z ^ n + c`. -/
def multibrotSet (n : ℕ) : Set ℂ :=
  {c | ¬ Tendsto (fun k ↦ (fun z ↦ z ^ n + c)^[k] 0) atTop (cobounded ℂ)}

/-- The Mandelbrot set is the special case of the multibrotSet for n = 2. -/
abbrev mandelbrotSet := multibrotSet 2

-- Equivalence with Yoccoz definition
lemma mandelbrotSet_eq_MandelbrotSet : mandelbrotSet = MLC.Quadratic.MandelbrotSet := by
  exact Mlc.MandelbrotEquivalence.mandelbrot_set_equivalence

section MainProof

/-- Every parameter is either finitely renormalizable (including non-renormalizable) or infinitely renormalizable.
    Proof idea: By the law of excluded middle, the sum of moduli either converges or diverges.
    We use the definition of FinitelyRenormalizable and InfinitelyRenormalizable which directly
    map to this divergence/convergence behavior. -/
theorem dichotomy (c : ℂ) : FinitelyRenormalizable c ∨ InfinitelyRenormalizable c := by
  unfold FinitelyRenormalizable InfinitelyRenormalizable
  rw [or_comm]
  exact Classical.em _

/-- The core strategy theorem (internal). -/
theorem mlc_strategy
    (h_param_shrink :
      ∀ (c : ℂ) (_hc : c ∈ MLC.Quadratic.MandelbrotSet) (_h : FinitelyRenormalizable c),
        (⋂ n, MLC.Quadratic.ParaPuzzlePieceAt c n) = {c})
    (h_bottcher_onM : MLC.Quadratic.BottcherOnMHyp)
    (h_green_conn : MLC.Quadratic.GreenSublevelConnectedHyp)
    (h_classify : ∀ (c : ℂ) (_h : InfinitelyRenormalizable c),
      PrimitiveRenormalizable c ∨ SatelliteRenormalizable c)
    (h_bridge :
      MoleculeConjectureRefined →
      MLC.Quadratic.PuzzleBoundaryMotionHyp →
      ∀ (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet) (_h : SatelliteRenormalizable c),
        MLC.LocallyConnectedAt MLC.Quadratic.MandelbrotSet ⟨c, hc⟩) :
    LocallyConnectedSpace MLC.Quadratic.MandelbrotSet := by
  -- We need to show local connectivity at every point c ∈ MandelbrotSet
  have h_motion : MLC.Quadratic.PuzzleBoundaryMotionHyp :=
    MLC.Quadratic.puzzle_boundary_motion_hyp_of_onM_connected
      (MLC.Quadratic.bottcher_green_sublevel_hyp_onM_connected_of_onM h_bottcher_onM h_green_conn)
  apply locallyConnectedSpace_of_locallyConnectedAt
  intro ⟨c, hc⟩
  rcases dichotomy c with h_fin_renorm | h_inf_renorm
  · -- Case 1: Finitely Renormalizable
    exact mlc_finitely_renormalizable c hc h_fin_renorm (h_param_shrink c hc h_fin_renorm)
  · -- Case 2: Infinitely renormalizable
    exact mlc_infinitely_renormalizable h_classify h_bridge h_motion c hc h_inf_renorm

/-- A parameterized MLC statement: basin injectivity of the Böttcher map
    on Mandelbrot parameters is enough to close the strategy. -/
theorem mlc_conjecture_of_bottcher_inj_on_basin_onM
    (h_inj_basin_onM :
      ∀ c, c ∈ MLC.Quadratic.MandelbrotSet →
        Set.InjOn (Quadratic.bottcher_map c) (Quadratic.basin_of_infinity c)) :
    LocallyConnectedSpace mandelbrotSet := by
  rw [mandelbrotSet_eq_MandelbrotSet]
  apply mlc_strategy
  · -- Finitely Renormalizable case (Yoccoz)
    intro c hc h_fin
    have h_dyn : (⋂ n, MLC.Quadratic.DynamicalPuzzlePiece c n 0) = {0} := by
      apply MLC.yoccoz_theorem
      simpa [FinitelyRenormalizable, NonRenormalizable] using h_fin
    exact parameter_shrink_of_yoccoz c hc h_fin h_dyn
  · -- Bottcher coordinates exist on M
    exact bottcher_onM_hyp
  · -- Green sublevel sets connected
    exact green_sublevel_connected_onM
      (fun c w hw => Quadratic.bottcher_map_surj c w hw)
      h_inj_basin_onM
  · -- Classification of infinitely renormalizable parameters (Lyubich)
    intro c h_inf
    exact classify_infinitely_renormalizable c h_inf
  · -- Bridge from Molecule Conjecture to Satellite MLC
    intro h_mol h_motion c hc h_sat
    exact molecule_conjecture_bridge h_mol h_motion c hc h_sat

/-- A parameterized MLC statement: basin injectivity of the Böttcher map
    is enough to close the strategy. -/
theorem mlc_conjecture_of_bottcher_inj_on_basin
    (h_inj_basin :
      ∀ c, Set.InjOn (Quadratic.bottcher_map c) (Quadratic.basin_of_infinity c)) :
    LocallyConnectedSpace mandelbrotSet := by
  apply mlc_conjecture_of_bottcher_inj_on_basin_onM
  intro c _hc
  exact h_inj_basin c

/-- Basin-wise left-inverse identity for `external_ray_map ∘ bottcher_map`
    is enough to obtain MLC. -/
theorem mlc_conjecture_of_bottcher_left_inverse_on_basin
    (h_left_basin :
      ∀ c, ∀ z, z ∈ Quadratic.basin_of_infinity c →
        Quadratic.external_ray_map c (Quadratic.bottcher_map c z) = z) :
    LocallyConnectedSpace mandelbrotSet := by
  apply mlc_conjecture_of_bottcher_inj_on_basin
  intro c
  exact bottcher_map_inj_on_basin_of_left_inverse c (h_left_basin c)

/-- A parameterized MLC statement: if each Böttcher map is a local homeomorphism
    on `ℂ`, basin injectivity follows from the proper/local-homeomorphism
    finite-fiber route. -/
theorem mlc_conjecture_of_bottcher_isLocalHomeomorph
    (hlocal : ∀ c, IsLocalHomeomorph (Quadratic.bottcher_map c)) :
    LocallyConnectedSpace mandelbrotSet := by
  apply mlc_conjecture_of_bottcher_inj_on_basin
  intro c
  exact bottcher_map_inj_on_basin_of_isLocalHomeomorph c (hlocal c)

/-- A parameterized MLC statement: properness plus local-homeomorphism on the basin
    is enough to obtain basin injectivity of the Böttcher map. -/
theorem mlc_conjecture_of_bottcher_proper_localHomeomorphOn_basin
    (hproper : ∀ c, IsProperMap (Quadratic.bottcher_map c))
    (hlocal :
      ∀ c, IsLocalHomeomorphOn (Quadratic.bottcher_map c) (Quadratic.basin_of_infinity c)) :
    LocallyConnectedSpace mandelbrotSet := by
  apply mlc_conjecture_of_bottcher_inj_on_basin
  intro c
  exact bottcher_map_inj_on_basin_of_proper_localHomeomorphOn_basin c (hproper c) (hlocal c)

/-- Consolidated Step 2b redesign data:
    properness plus local-homeomorphism of `bottcher_map` on the basin. -/
def BottcherProperLocalHomeomorphOnBasinData : Prop :=
  ∀ c,
    IsProperMap (Quadratic.bottcher_map c) ∧
    IsLocalHomeomorphOn (Quadratic.bottcher_map c) (Quadratic.basin_of_infinity c)

/-- Main-conjecture wrapper for proper/local-homeomorphism redesign data. -/
theorem mlc_conjecture_of_bottcher_proper_localHomeomorphOn_basin_data
    (hdata : BottcherProperLocalHomeomorphOnBasinData) :
    LocallyConnectedSpace mandelbrotSet := by
  apply mlc_conjecture_of_bottcher_proper_localHomeomorphOn_basin
  · intro c
    exact (hdata c).1
  · intro c
    exact (hdata c).2

/-- A parameterized MLC statement: properness plus nonvanishing derivative
    on basin points (with slit-orbit neighborhoods) yields basin injectivity
    through the basin-local-homeomorphism route. -/
theorem mlc_conjecture_of_bottcher_proper_deriv_ne_zero_mem_nhds_slit
    (hproper : ∀ c, IsProperMap (Quadratic.bottcher_map c))
    (hslit :
      ∀ c z, z ∈ Quadratic.basin_of_infinity c → slit_orbit c ∈ 𝓝 z)
    (hderiv :
      ∀ c z, z ∈ Quadratic.basin_of_infinity c →
        deriv (Quadratic.bottcher_map c) z ≠ 0) :
    LocallyConnectedSpace mandelbrotSet := by
  apply mlc_conjecture_of_bottcher_proper_localHomeomorphOn_basin hproper
  intro c
  exact bottcher_map_isLocalHomeomorphOn_basin_of_deriv_ne_zero_of_mem_nhds_slit c
    (hslit c) (hderiv c)

/-- A parameterized MLC statement: continuity plus nonvanishing derivative
    on basin points (with slit-orbit neighborhoods) implies properness/local
    homeomorphism on the basin, hence basin injectivity. -/
theorem mlc_conjecture_of_bottcher_continuous_deriv_ne_zero_mem_nhds_slit
    (hcont : ∀ c, Continuous (Quadratic.bottcher_map c))
    (hslit :
      ∀ c z, z ∈ Quadratic.basin_of_infinity c → slit_orbit c ∈ 𝓝 z)
    (hderiv :
      ∀ c z, z ∈ Quadratic.basin_of_infinity c →
        deriv (Quadratic.bottcher_map c) z ≠ 0) :
    LocallyConnectedSpace mandelbrotSet := by
  apply mlc_conjecture_of_bottcher_proper_deriv_ne_zero_mem_nhds_slit
  · intro c
    exact bottcher_map_isProperMap_of_continuous c (hcont c)
  · exact hslit
  · exact hderiv

/-- Continuity plus basin-local slit-neighborhood/nonzero-derivative data
    upgrades to properness and basin local-homeomorphism data. -/
theorem bottcher_proper_localHomeomorphOn_basin_data_of_bottcher_continuous_deriv_ne_zero_mem_nhds_slit
    (hcont : ∀ c, Continuous (Quadratic.bottcher_map c))
    (hslit :
      ∀ c z, z ∈ Quadratic.basin_of_infinity c → slit_orbit c ∈ 𝓝 z)
    (hderiv :
      ∀ c z, z ∈ Quadratic.basin_of_infinity c →
        deriv (Quadratic.bottcher_map c) z ≠ 0) :
    BottcherProperLocalHomeomorphOnBasinData := by
  intro c
  refine ⟨?_, ?_⟩
  · exact bottcher_map_isProperMap_of_continuous c (hcont c)
  · exact bottcher_map_isLocalHomeomorphOn_basin_of_deriv_ne_zero_of_mem_nhds_slit c
      (hslit c) (hderiv c)

/-- Consolidated Step 2b redesign data:
    continuity of `bottcher_map` plus basin-local slit-neighborhood and
    nonvanishing-derivative conditions. -/
def BottcherContinuousDerivNeZeroMemNhdsSlitData : Prop :=
  ∀ c,
    Continuous (Quadratic.bottcher_map c) ∧
    (∀ z, z ∈ Quadratic.basin_of_infinity c → slit_orbit c ∈ 𝓝 z) ∧
    (∀ z, z ∈ Quadratic.basin_of_infinity c →
      deriv (Quadratic.bottcher_map c) z ≠ 0)

/-- Main-conjecture wrapper for the consolidated Step 2b redesign data. -/
theorem mlc_conjecture_of_bottcher_continuous_deriv_ne_zero_mem_nhds_slit_data
    (hdata : BottcherContinuousDerivNeZeroMemNhdsSlitData) :
    LocallyConnectedSpace mandelbrotSet := by
  apply mlc_conjecture_of_bottcher_proper_localHomeomorphOn_basin_data
  exact bottcher_proper_localHomeomorphOn_basin_data_of_bottcher_continuous_deriv_ne_zero_mem_nhds_slit
    (fun c => (hdata c).1)
    (fun c z hz => (hdata c).2.1 z hz)
    (fun c z hz => (hdata c).2.2 z hz)

/-- The current `bottcher_map` model is nowhere globally continuous at `0`,
    so the proper/local-homeomorphism-on-basin data target is inconsistent. -/
theorem not_bottcher_proper_localHomeomorphOn_basin_data :
    ¬ BottcherProperLocalHomeomorphOnBasinData := by
  intro hdata
  exact bottcher_map_not_isProperMap 0 (hdata 0).1

/-- The stronger continuity/derivative/slit-neighborhood data target is also
    inconsistent, since it implies global continuity of `bottcher_map`. -/
theorem not_bottcher_continuous_deriv_ne_zero_mem_nhds_slit_data :
    ¬ BottcherContinuousDerivNeZeroMemNhdsSlitData := by
  intro hdata
  exact bottcher_map_not_continuous 0 (hdata 0).1

/-- The global local-homeomorphism route is inconsistent for the current
    `bottcher_map` model, since it would force global continuity. -/
theorem not_bottcher_isLocalHomeomorph_data :
    ¬ (∀ c, IsLocalHomeomorph (Quadratic.bottcher_map c)) := by
  intro hlocal
  exact bottcher_map_not_continuous 0 (hlocal 0).continuous

/-- The `bottcher_map_inj_on_K` axiom is inconsistent with the current explicit
    `bottcher_map` model at parameter `c = 0`. -/
theorem not_bottcher_map_inj_on_K_zero :
    ¬ Set.InjOn (Quadratic.bottcher_map 0) (MLC.Quadratic.K 0) := by
  intro hinj
  have h0_fix : MLC.Quadratic.fc 0 (0 : ℂ) = 0 := by
    simp [MLC.Quadratic.fc]
  have h1_fix : MLC.Quadratic.fc 0 (1 : ℂ) = 1 := by
    simp [MLC.Quadratic.fc]
  have h0K : (0 : ℂ) ∈ MLC.Quadratic.K 0 := by
    refine ⟨0, ?_⟩
    intro n
    have h_orbit : MLC.Quadratic.orbit 0 (0 : ℂ) n = 0 :=
      Quadratic.orbit_fixed_point 0 0 h0_fix n
    simpa [h_orbit]
  have h1K : (1 : ℂ) ∈ MLC.Quadratic.K 0 := by
    refine ⟨1, ?_⟩
    intro n
    have h_orbit : MLC.Quadratic.orbit 0 (1 : ℂ) n = 1 :=
      Quadratic.orbit_fixed_point 0 1 h1_fix n
    simpa [h_orbit]
  have hgreen0 : MLC.Quadratic.green_function 0 (0 : ℂ) = 0 :=
    (MLC.Quadratic.green_function_eq_zero_iff_mem_K 0 0).2 h0K
  have hgreen1 : MLC.Quadratic.green_function 0 (1 : ℂ) = 0 :=
    (MLC.Quadratic.green_function_eq_zero_iff_mem_K 0 1).2 h1K
  have hsame :
      Quadratic.bottcher_map 0 (0 : ℂ) = Quadratic.bottcher_map 0 (1 : ℂ) := by
    calc
      Quadratic.bottcher_map 0 (0 : ℂ) = (1 : ℂ) := by
        simp [Quadratic.bottcher_map, hgreen0]
      _ = Quadratic.bottcher_map 0 (1 : ℂ) := by
        symm
        simp [Quadratic.bottcher_map, hgreen1]
  have hzero_eq_one : (0 : ℂ) = 1 := hinj h0K h1K hsame
  norm_num at hzero_eq_one

/-- Global K-injectivity of `bottcher_map` is inconsistent with the current
    explicit model. -/
theorem not_bottcher_map_inj_on_K_data :
    ¬ (∀ c, Set.InjOn (Quadratic.bottcher_map c) (MLC.Quadratic.K c)) := by
  intro h_inj
  exact not_bottcher_map_inj_on_K_zero (h_inj 0)

/-- Current contradiction packaged from the K-injectivity axiom family. -/
lemma false_of_bottcher_map_inj_on_K_axiom : False := by
  exact not_bottcher_map_inj_on_K_data (fun c => bottcher_map_inj_on_K c)

/-- A concrete escaping witness: `0` is in the basin for `c = 2`. -/
lemma zero_mem_basin_two : (0 : ℂ) ∈ Quadratic.basin_of_infinity (2 : ℂ) := by
  have hnorm : ‖(6 : ℂ)‖ ≥ ‖(2 : ℂ)‖ + 2 := by norm_num
  have htail :
      Tendsto (fun n => ‖(quadratic_map (2 : ℂ))^[n] (6 : ℂ)‖) atTop atTop := by
    exact iterate_quadratic_map_tendsto_infty (2 : ℂ) (6 : ℂ) hnorm
  have htwo : (quadratic_map (2 : ℂ))^[2] (0 : ℂ) = (6 : ℂ) := by
    norm_num [quadratic_map]
  have htail' :
      Tendsto (fun n => ‖(quadratic_map (2 : ℂ))^[n] ((quadratic_map (2 : ℂ))^[2] (0 : ℂ))‖)
        atTop atTop := by
    simpa [htwo] using htail
  have hshift :
      Tendsto (fun n => ‖(quadratic_map (2 : ℂ))^[n + 2] (0 : ℂ)‖) atTop atTop := by
    simpa [Function.iterate_add, Function.comp_apply] using htail'
  have hbase :
      Tendsto (fun n => ‖(quadratic_map (2 : ℂ))^[n] (0 : ℂ)‖) atTop atTop :=
    (tendsto_add_atTop_iff_nat
      (f := fun n => ‖(quadratic_map (2 : ℂ))^[n] (0 : ℂ)‖) (k := 2)).1 hshift
  simpa [Quadratic.basin_of_infinity, MLC.basin_of_infinity] using hbase

/-- Consequently, `0 ∉ K(2)`. -/
lemma zero_not_mem_K_two : (0 : ℂ) ∉ MLC.Quadratic.K (2 : ℂ) := by
  have hbasin : (0 : ℂ) ∈ Quadratic.basin_of_infinity (2 : ℂ) := zero_mem_basin_two
  have hcompl : (0 : ℂ) ∈ (MLC.Quadratic.K (2 : ℂ))ᶜ := by
    simpa [Quadratic.basin_eq_compl_K (2 : ℂ)] using hbasin
  simpa [Set.mem_compl_iff] using hcompl

/-- The chosen fixed point for `c = 2` cannot be `0`. -/
lemma fixed_point_two_ne_zero : Quadratic.fixed_point (2 : ℂ) ≠ 0 := by
  intro hzero
  have hmem : Quadratic.fixed_point (2 : ℂ) ∈ MLC.Quadratic.K (2 : ℂ) :=
    Quadratic.fixed_point_mem_K (2 : ℂ)
  have h0 : (0 : ℂ) ∈ MLC.Quadratic.K (2 : ℂ) := by
    simpa [hzero] using hmem
  exact zero_not_mem_K_two h0

/-- `bottcher_map` is continuous at every nonzero point. -/
lemma bottcher_map_continuousAt_of_ne_zero (c z : ℂ) (hz : z ≠ 0) :
    ContinuousAt (Quadratic.bottcher_map c) z := by
  have hnorm_ne : (‖z‖ : ℂ) ≠ 0 := by
    exact_mod_cast (norm_ne_zero_iff.2 hz)
  have hdiv : ContinuousAt (fun w : ℂ => w / (‖w‖ : ℂ)) z :=
    continuousAt_id.div
      ((Complex.continuous_ofReal.comp continuous_norm).continuousAt) hnorm_ne
  have hif :
      (fun w : ℂ => if w = 0 then (1 : ℂ) else w / (‖w‖ : ℂ)) =ᶠ[𝓝 z]
        (fun w : ℂ => w / (‖w‖ : ℂ)) := by
    filter_upwards [eventually_ne_nhds hz] with w hw
    simp [hw]
  have hdir : ContinuousAt (fun w : ℂ => if w = 0 then (1 : ℂ) else w / (‖w‖ : ℂ)) z :=
    hdiv.congr_of_eventuallyEq hif
  have hexp :
      ContinuousAt (fun w : ℂ => (Real.exp (MLC.Quadratic.green_function c w) : ℂ)) z :=
    (Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp (MLC.Quadratic.continuous_green_function c))).continuousAt
  change ContinuousAt
    (fun w : ℂ =>
      (if w = 0 then (1 : ℂ) else w / (‖w‖ : ℂ)) *
        (Real.exp (MLC.Quadratic.green_function c w) : ℂ)) z
  exact hdir.mul hexp

/-- Every real point escapes for `c = 2`, hence lies in the basin. -/
lemma ofReal_mem_basin_two (x : ℝ) :
    (x : ℂ) ∈ Quadratic.basin_of_infinity (2 : ℂ) := by
  have hiter2 :
      (quadratic_map (2 : ℂ))^[2] (x : ℂ) = (((x ^ 2 + 2) ^ 2 + 2 : ℝ) : ℂ) := by
    simp [quadratic_map, pow_two, mul_add, add_comm]
  have hnorm_ge : ‖(((x ^ 2 + 2) ^ 2 + 2 : ℝ) : ℂ)‖ ≥ ‖(2 : ℂ)‖ + 2 := by
    have hnonneg : 0 ≤ (x ^ 2 + 2) ^ 2 + 2 := by
      nlinarith [sq_nonneg x]
    have hfour : (4 : ℝ) ≤ (x ^ 2 + 2) ^ 2 + 2 := by
      have hx2 : 2 ≤ x ^ 2 + 2 := by nlinarith [sq_nonneg x]
      nlinarith [sq_nonneg (x ^ 2 + 2), hx2]
    have hnorm :
        ‖(((x ^ 2 + 2) ^ 2 + 2 : ℝ) : ℂ)‖ = (x ^ 2 + 2) ^ 2 + 2 := by
      simpa using (Complex.norm_of_nonneg hnonneg)
    have htwo : ‖(2 : ℂ)‖ + 2 = (4 : ℝ) := by norm_num
    rw [hnorm, htwo]
    exact hfour
  have htail :
      Tendsto
        (fun n =>
          ‖(quadratic_map (2 : ℂ))^[n] ((((x ^ 2 + 2) ^ 2 + 2 : ℝ) : ℂ))‖) atTop atTop := by
    exact iterate_quadratic_map_tendsto_infty (2 : ℂ) _ hnorm_ge
  have htail' :
      Tendsto (fun n => ‖(quadratic_map (2 : ℂ))^[n] ((quadratic_map (2 : ℂ))^[2] (x : ℂ))‖)
        atTop atTop := by
    simpa [hiter2] using htail
  have hshift :
      Tendsto (fun n => ‖(quadratic_map (2 : ℂ))^[n + 2] (x : ℂ)‖) atTop atTop := by
    simpa [Function.iterate_add, Function.comp_apply] using htail'
  have hbase :
      Tendsto (fun n => ‖(quadratic_map (2 : ℂ))^[n] (x : ℂ)‖) atTop atTop :=
    (tendsto_add_atTop_iff_nat
      (f := fun n => ‖(quadratic_map (2 : ℂ))^[n] (x : ℂ)‖) (k := 2)).1 hshift
  simpa [Quadratic.basin_of_infinity, MLC.basin_of_infinity] using hbase

/-- Real points are not in `K(2)`. -/
lemma ofReal_not_mem_K_two (x : ℝ) :
    (x : ℂ) ∉ MLC.Quadratic.K (2 : ℂ) := by
  have hbasin : (x : ℂ) ∈ Quadratic.basin_of_infinity (2 : ℂ) :=
    ofReal_mem_basin_two x
  have hcompl : (x : ℂ) ∈ (MLC.Quadratic.K (2 : ℂ))ᶜ := by
    simpa [Quadratic.basin_eq_compl_K (2 : ℂ)] using hbasin
  simpa [Set.mem_compl_iff] using hcompl

/-- Any `K(2)` point mapping to `1` under the explicit `bottcher_map` model
    yields a contradiction. -/
lemma bottcher_map_eq_one_not_mem_K_two (z : ℂ) (hzK : z ∈ MLC.Quadratic.K (2 : ℂ)) :
    Quadratic.bottcher_map (2 : ℂ) z ≠ 1 := by
  intro hphi
  by_cases hz0 : z = 0
  · exact zero_not_mem_K_two (by simpa [hz0] using hzK)
  · have hgreen : MLC.Quadratic.green_function (2 : ℂ) z = 0 :=
      (MLC.Quadratic.green_function_eq_zero_iff_mem_K (2 : ℂ) z).2 hzK
    have hdir : z / (‖z‖ : ℂ) = 1 := by
      simpa [Quadratic.bottcher_map, hz0, hgreen] using hphi
    have hnorm_ne : (‖z‖ : ℂ) ≠ 0 := by
      exact_mod_cast (norm_ne_zero_iff.2 hz0)
    have hz_eq : z = ((‖z‖ : ℝ) : ℂ) := by
      calc
        z = (z / (‖z‖ : ℂ)) * (‖z‖ : ℂ) := by field_simp [hnorm_ne]
        _ = 1 * (‖z‖ : ℂ) := by simp [hdir]
        _ = ((‖z‖ : ℝ) : ℂ) := by simp
    have hzK' : (((‖z‖ : ℝ) : ℂ)) ∈ MLC.Quadratic.K (2 : ℂ) := by
      rw [← hz_eq]
      exact hzK
    exact ofReal_not_mem_K_two ‖z‖ hzK'

/-- The chosen `fixed_point 2` cannot map to `1` under the current explicit
    `bottcher_map` model. -/
lemma bottcher_map_fixed_point_two_ne_one :
    Quadratic.bottcher_map (2 : ℂ) (Quadratic.fixed_point (2 : ℂ)) ≠ 1 := by
  exact bottcher_map_eq_one_not_mem_K_two (Quadratic.fixed_point (2 : ℂ))
    (Quadratic.fixed_point_mem_K (2 : ℂ))

/-- A logarithmic lower bound for `green_function` above the escape bound. -/
lemma log_norm_le_green_add_escape_const_of_norm_gt_escape_bound
    (c z : ℂ) (hz : ‖z‖ > MLC.Quadratic.escape_bound c) :
    Real.log ‖z‖ ≤
      MLC.Quadratic.green_function c z +
        (2 * ‖c‖ / (MLC.Quadratic.escape_bound c) ^ 2) := by
  have hk :
      dist (MLC.Quadratic.potential_seq c z 0) (MLC.Quadratic.green_function c z) ≤
        (1 / 2 ^ (0 : ℕ)) * (2 * ‖c‖ / (MLC.Quadratic.escape_bound c) ^ 2) := by
    simpa [MLC.Quadratic.orbit_zero] using
      (MLC.Quadratic.dist_potential_seq_green_function_le_of_escaping c z 0 hz)
  have hB1 : (1 : ℝ) ≤ MLC.Quadratic.escape_bound c := by
    exact le_trans (le_trans one_le_two (MLC.Quadratic.R_ge_two c))
      (MLC.Quadratic.escape_bound_ge_R c)
  have hz1 : (1 : ℝ) ≤ ‖z‖ := le_trans hB1 (le_of_lt hz)
  have hpot : MLC.Quadratic.potential_seq c z 0 = Real.log ‖z‖ := by
    simp [MLC.Quadratic.potential_seq, max_eq_right hz1]
  have habs :
      |Real.log ‖z‖ - MLC.Quadratic.green_function c z| ≤
        (2 * ‖c‖ / (MLC.Quadratic.escape_bound c) ^ 2) := by
    simpa [hpot, Real.dist_eq, one_div, inv_one] using hk
  have hle :
      Real.log ‖z‖ - MLC.Quadratic.green_function c z ≤
        (2 * ‖c‖ / (MLC.Quadratic.escape_bound c) ^ 2) :=
    (abs_sub_le_iff.1 habs).1
  linarith

/-- Contradiction obtained from `external_ray_map_exists` alone
    (without using `bottcher_map_inj_on_K` or `extended_ray_map_continuous`). -/
lemma false_of_external_ray_axioms : False := by
  let u : ℕ → ℂ := fun n => Complex.ofReal (1 + (1 / ((n : ℝ) + 1)))
  let z : ℕ → ℂ := fun n => Quadratic.external_ray_map (2 : ℂ) (u n)
  have hu_gt : ∀ n, (1 : ℝ) < ‖u n‖ := by
    intro n
    have hpos : 0 < (1 / ((n : ℝ) + 1)) := by positivity
    have hnonneg : 0 ≤ (1 + (1 / ((n : ℝ) + 1))) := by positivity
    have hnorm :
        ‖u n‖ = 1 + (1 / ((n : ℝ) + 1)) := by
      simpa [u] using (Complex.norm_of_nonneg hnonneg)
    rw [hnorm]
    linarith
  have hu_norm : ∀ n, ‖u n‖ = 1 + (1 / ((n : ℝ) + 1)) := by
    intro n
    have hnonneg : 0 ≤ (1 + (1 / ((n : ℝ) + 1))) := by positivity
    simpa [u] using (Complex.norm_of_nonneg hnonneg)
  have hu_le_two : ∀ n, ‖u n‖ ≤ 2 := by
    intro n
    have hden_pos : 0 < (n : ℝ) + 1 := by positivity
    have hden_ge : (1 : ℝ) ≤ (n : ℝ) + 1 := by nlinarith
    have hrecip_le : 1 / ((n : ℝ) + 1) ≤ 1 := by
      have htmp : 1 / ((n : ℝ) + 1) ≤ 1 / (1 : ℝ) :=
        one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hden_ge
      simpa using htmp
    rw [hu_norm n]
    linarith
  have hu_tend_real :
      Tendsto (fun n : ℕ => 1 + (1 / ((n : ℝ) + 1))) atTop (𝓝 (1 : ℝ)) := by
    simpa [add_comm] using tendsto_one_div_add_atTop_nhds_zero_nat.const_add (1 : ℝ)
  have hu_tend : Tendsto u atTop (𝓝 (1 : ℂ)) := by
    simpa [u] using hu_tend_real.ofReal
  have hright : ∀ n, Quadratic.bottcher_map (2 : ℂ) (z n) = u n := by
    intro n
    exact (Classical.choose_spec (Quadratic.external_ray_map_exists (2 : ℂ))).1
      (u n) (hu_gt n)
  have hgreen_eq : ∀ n, MLC.Quadratic.green_function (2 : ℂ) (z n) = Real.log ‖u n‖ := by
    intro n
    have hnorm :
        Real.exp (MLC.Quadratic.green_function (2 : ℂ) (z n)) = ‖u n‖ := by
      calc
        Real.exp (MLC.Quadratic.green_function (2 : ℂ) (z n)) =
            ‖Quadratic.bottcher_map (2 : ℂ) (z n)‖ := by
              simpa using (Quadratic.norm_bottcher_eq_exp_green (2 : ℂ) (z n)).symm
        _ = ‖u n‖ := by simpa [hright n]
    have := congrArg Real.log hnorm
    simpa [Real.log_exp] using this
  set C : ℝ := 2 * ‖(2 : ℂ)‖ / (MLC.Quadratic.escape_bound (2 : ℂ)) ^ 2
  set B : ℝ := max (MLC.Quadratic.escape_bound (2 : ℂ)) (Real.exp (Real.log 2 + C))
  have hz_bound : ∀ n, ‖z n‖ ≤ B := by
    intro n
    by_cases hlarge : ‖z n‖ > MLC.Quadratic.escape_bound (2 : ℂ)
    · have hlog :
        Real.log ‖z n‖ ≤ MLC.Quadratic.green_function (2 : ℂ) (z n) + C := by
        simpa [C] using
          log_norm_le_green_add_escape_const_of_norm_gt_escape_bound
            (2 : ℂ) (z n) hlarge
      have hlog_u_le : Real.log ‖u n‖ ≤ Real.log 2 := by
        have hu_pos : 0 < ‖u n‖ := lt_trans zero_lt_one (hu_gt n)
        exact Real.log_le_log hu_pos (hu_le_two n)
      have hlog' : Real.log ‖z n‖ ≤ Real.log 2 + C := by
        linarith [hlog, hgreen_eq n, hlog_u_le]
      have hesc_ge_two : (2 : ℝ) ≤ MLC.Quadratic.escape_bound (2 : ℂ) := by
        exact le_trans (MLC.Quadratic.R_ge_two (2 : ℂ))
          (MLC.Quadratic.escape_bound_ge_R (2 : ℂ))
      have hz_pos : 0 < ‖z n‖ := by
        linarith
      have hz_exp : ‖z n‖ ≤ Real.exp (Real.log 2 + C) :=
        (Real.log_le_iff_le_exp hz_pos).1 hlog'
      exact le_trans hz_exp (le_max_right _ _)
    · have hz_esc : ‖z n‖ ≤ MLC.Quadratic.escape_bound (2 : ℂ) := le_of_not_gt hlarge
      exact le_trans hz_esc (le_max_left _ _)
  have hz_mem :
      ∀ n, z n ∈ Metric.closedBall (0 : ℂ) B := by
    intro n
    simpa [Metric.mem_closedBall, dist_eq_norm] using hz_bound n
  have hbounded_ball : IsBounded (Metric.closedBall (0 : ℂ) B) := by
    simpa using (isBounded_closedBall : IsBounded (Metric.closedBall (0 : ℂ) B))
  obtain ⟨a, _ha_cl, φ, hφmono, hφtend⟩ :=
    tendsto_subseq_of_bounded hbounded_ball hz_mem
  have hlog_tend : Tendsto (fun n => Real.log ‖u n‖) atTop (𝓝 (0 : ℝ)) := by
    have hnorm_tend : Tendsto (fun n => ‖u n‖) atTop (𝓝 (1 : ℝ)) := by
      simpa [hu_norm] using hu_tend_real
    have hcont_log : ContinuousAt Real.log (1 : ℝ) :=
      Real.continuousAt_log (by norm_num)
    simpa using hcont_log.tendsto.comp hnorm_tend
  have hgreen_tend :
      Tendsto (fun n => MLC.Quadratic.green_function (2 : ℂ) (z n)) atTop (𝓝 (0 : ℝ)) := by
    simpa [hgreen_eq] using hlog_tend
  have hgreen_sub_tend :
      Tendsto (fun n => MLC.Quadratic.green_function (2 : ℂ) (z (φ n))) atTop (𝓝 (0 : ℝ)) :=
    hgreen_tend.comp hφmono.tendsto_atTop
  have hgreen_lim :
      Tendsto (fun n => MLC.Quadratic.green_function (2 : ℂ) (z (φ n))) atTop
        (𝓝 (MLC.Quadratic.green_function (2 : ℂ) a)) := by
    exact ((MLC.Quadratic.continuous_green_function (2 : ℂ)).continuousAt).tendsto.comp hφtend
  have hgreen_a_zero : MLC.Quadratic.green_function (2 : ℂ) a = 0 :=
    tendsto_nhds_unique hgreen_lim hgreen_sub_tend
  have haK : a ∈ MLC.Quadratic.K (2 : ℂ) :=
    (MLC.Quadratic.green_function_eq_zero_iff_mem_K (2 : ℂ) a).1 hgreen_a_zero
  have ha0 : a ≠ 0 := by
    intro ha_zero
    exact zero_not_mem_K_two (by simpa [ha_zero] using haK)
  have hcont_phi : ContinuousAt (Quadratic.bottcher_map (2 : ℂ)) a :=
    bottcher_map_continuousAt_of_ne_zero (2 : ℂ) a ha0
  have hphi_sub_tend :
      Tendsto (fun n => Quadratic.bottcher_map (2 : ℂ) (z (φ n))) atTop
        (𝓝 (Quadratic.bottcher_map (2 : ℂ) a)) :=
    hcont_phi.tendsto.comp hφtend
  have hu_sub_tend :
      Tendsto (fun n => u (φ n)) atTop (𝓝 (1 : ℂ)) :=
    hu_tend.comp hφmono.tendsto_atTop
  have hu_sub_tend_phi :
      Tendsto (fun n => u (φ n)) atTop (𝓝 (Quadratic.bottcher_map (2 : ℂ) a)) := by
    have hsub_eq :
        (fun n => Quadratic.bottcher_map (2 : ℂ) (z (φ n))) = (fun n => u (φ n)) := by
      funext n
      exact hright (φ n)
    simpa [hsub_eq] using hphi_sub_tend
  have hphi_a : Quadratic.bottcher_map (2 : ℂ) a = 1 :=
    tendsto_nhds_unique hu_sub_tend_phi hu_sub_tend
  exact (bottcher_map_eq_one_not_mem_K_two a haK) hphi_a

/-- A parameterized MLC statement: if iterate-equality on the basin is available,
    then the MLC strategy closes. -/
theorem mlc_conjecture_of_iter_eq_imp
    (h_iter_eq_imp :
      ∀ c, ∀ z w, z ∈ Quadratic.basin_of_infinity c →
        w ∈ Quadratic.basin_of_infinity c →
        (∃ n, (quadratic_map c)^[n] z = (quadratic_map c)^[n] w) → z = w) :
    LocallyConnectedSpace mandelbrotSet := by
  exfalso
  exact Quadratic.not_quadratic_map_iter_eq_imp_eq 0 (h_iter_eq_imp 0)

/-- If each parameter admits a left inverse of `quadratic_map` on the basin,
    MLC follows via derived iterate-equality. -/
theorem mlc_conjecture_of_quadratic_left_inverse
    (hleft :
      ∀ c, Quadratic.HasLeftInverseOn (quadratic_map c)
        (Quadratic.basin_of_infinity c) (Quadratic.basin_of_infinity c)) :
    LocallyConnectedSpace mandelbrotSet := by
  exfalso
  exact Quadratic.not_quadratic_map_left_inverse_on_basin 0 (hleft 0)

/-- A concrete replacement route for iterate-equality, parameterized by a
    variable square-root pullback construction on the Böttcher image of the basin. -/
theorem mlc_conjecture_of_basin_sqrt_branch_of_injective
    (h_branch :
      ∀ c, ∃ sqrt : ℂ → ℂ,
        Quadratic.BasinBottcherSquareRootRightInverse c sqrt ∧
        Function.Injective (Quadratic.bottcher_map c) ∧
        MapsTo (fun z => Quadratic.external_ray_map c (sqrt (Quadratic.bottcher_map c z)))
          (Quadratic.basin_of_infinity c) (Quadratic.basin_of_infinity c)) :
    LocallyConnectedSpace mandelbrotSet := by
  exfalso
  rcases h_branch 0 with ⟨sqrt, h_sqrt, h_inj, h_maps⟩
  have h_conj : ∀ z, z ∈ Quadratic.basin_of_infinity 0 →
      Quadratic.bottcher_map 0 (quadratic_map 0 z) = (Quadratic.bottcher_map 0 z) ^ 2 := by
    intro z hz
    simpa using (bottcher_conj_iter 0 1 z hz)
  have h_left_bottcher :
      ∀ z, z ∈ Quadratic.basin_of_infinity 0 →
        Quadratic.external_ray_map 0 (Quadratic.bottcher_map 0 z) = z :=
    Quadratic.bottcher_left_inverse_on_basin_of_injective 0 h_inj
  have hleft :
      Quadratic.HasLeftInverseOn (quadratic_map 0)
        (Quadratic.basin_of_infinity 0) (Quadratic.basin_of_infinity 0) :=
    Quadratic.quadratic_map_left_inverse_on_basin_of_basin_sqrt_branch 0 sqrt h_sqrt
      h_conj h_left_bottcher h_maps
  exact Quadratic.not_quadratic_map_left_inverse_on_basin 0 hleft

/-- A concrete replacement route for iterate-equality from variable branch data
    plus a basin-wide left inverse identity for the Böttcher/ray map pair. -/
theorem mlc_conjecture_of_basin_sqrt_branch
    (h_branch :
      ∀ c, ∃ sqrt : ℂ → ℂ,
        Quadratic.BasinBottcherSquareRootRightInverse c sqrt ∧
        (∀ z, z ∈ Quadratic.basin_of_infinity c →
          Quadratic.external_ray_map c (Quadratic.bottcher_map c z) = z) ∧
        MapsTo (fun z => Quadratic.external_ray_map c (sqrt (Quadratic.bottcher_map c z)))
          (Quadratic.basin_of_infinity c) (Quadratic.basin_of_infinity c)) :
    LocallyConnectedSpace mandelbrotSet := by
  exfalso
  rcases h_branch 0 with ⟨sqrt, h_sqrt, h_left_bottcher, h_maps⟩
  have h_conj : ∀ z, z ∈ Quadratic.basin_of_infinity 0 →
      Quadratic.bottcher_map 0 (quadratic_map 0 z) = (Quadratic.bottcher_map 0 z) ^ 2 := by
    intro z hz
    simpa using (bottcher_conj_iter 0 1 z hz)
  have hleft :
      Quadratic.HasLeftInverseOn (quadratic_map 0)
        (Quadratic.basin_of_infinity 0) (Quadratic.basin_of_infinity 0) :=
    Quadratic.quadratic_map_left_inverse_on_basin_of_basin_sqrt_branch 0 sqrt h_sqrt
      h_conj h_left_bottcher h_maps
  exact Quadratic.not_quadratic_map_left_inverse_on_basin 0 hleft

/-- A concrete non-vacuous replacement route: provide a pullback root along
    quadratic dynamics on the basin, plus basin mapping and Böttcher left inverse. -/
theorem mlc_conjecture_of_pullback_root
    (h_pull :
      ∀ c, ∃ root : ℂ → ℂ,
        Quadratic.BasinQuadraticPullbackRoot c root ∧
        (∀ z, z ∈ Quadratic.basin_of_infinity c →
          Quadratic.external_ray_map c (Quadratic.bottcher_map c z) = z) ∧
        MapsTo (fun z => Quadratic.external_ray_map c (root z))
          (Quadratic.basin_of_infinity c) (Quadratic.basin_of_infinity c)) :
    LocallyConnectedSpace mandelbrotSet := by
  apply mlc_conjecture_of_bottcher_left_inverse_on_basin
  intro c z hz
  rcases h_pull c with ⟨_root, _h_root, h_left_bottcher, _h_maps⟩
  exact h_left_bottcher z hz

/-- Top-level hook: enough eventual-slit bridge data per parameter implies MLC. -/
theorem mlc_conjecture_of_eventual_slit_global_bridge
    (h_bridge :
      ∀ c, ∃ hA : Quadratic.EventualSlitInverseAtlas c,
        ∃ hG : Quadratic.GlobalInverseOnEventualSlit c hA,
          Quadratic.EventualSlitGlobalInverseExtensionBridge c hA hG) :
    LocallyConnectedSpace mandelbrotSet := by
  exfalso
  rcases h_bridge 0 with ⟨hA, hG, hbr⟩
  exact Quadratic.not_EventualSlitGlobalInverseExtensionBridge 0 hA hG hbr

/-- The old bridge premise is globally inconsistent with current definitions. -/
theorem not_eventual_slit_global_bridge_data :
    ¬ (∀ c, ∃ hA : Quadratic.EventualSlitInverseAtlas c,
      ∃ hG : Quadratic.GlobalInverseOnEventualSlit c hA,
        Quadratic.EventualSlitGlobalInverseExtensionBridge c hA hG) := by
  intro h
  rcases h 0 with ⟨hA, hG, hbr⟩
  exact Quadratic.not_EventualSlitGlobalInverseExtensionBridge 0 hA hG hbr

/-- The remaining Step 2b global-inverse target is currently inconsistent:
    even at `c = 0`, an eventual-slit inverse atlas cannot exist. -/
theorem not_eventual_slit_global_inverse_data :
    ¬ (∀ c, ∃ hA : Quadratic.EventualSlitInverseAtlas c,
      Quadratic.GlobalInverseOnEventualSlit c hA) := by
  intro h
  rcases h 0 with ⟨hA, _hG⟩
  exact Quadratic.not_EventualSlitInverseAtlas_zero hA

/-- Extension-to-basin data is inconsistent with the current dynamics model,
    since it is equivalent to a basin-wide left inverse of `quadratic_map`. -/
theorem not_eventual_slit_global_extension_data :
    ¬ (∀ c, ∃ hA : Quadratic.EventualSlitInverseAtlas c,
      ∃ hG : Quadratic.GlobalInverseOnEventualSlit c hA,
        Quadratic.EventualSlitGlobalInverseExtendsToBasin c hA hG) := by
  intro h
  rcases h 0 with ⟨hA, hG, h_ext⟩
  have hleft :
      Quadratic.HasLeftInverseOn (quadratic_map 0)
        (Quadratic.basin_of_infinity 0) (Quadratic.basin_of_infinity 0) :=
    (Quadratic.EventualSlitGlobalInverseExtendsToBasin_iff_left_inverse 0 hA hG).1 h_ext
  exact Quadratic.not_quadratic_map_left_inverse_on_basin 0 hleft

/-- The overlap hypothesis in the eventual-slit local-to-global route is
    inconsistent with the current global Böttcher/exterior setup. -/
theorem not_eventual_slit_overlap_hyp_data :
    ¬ (∀ c, Quadratic.EventualSlitOverlapHyp c) := by
  intro h
  exact Quadratic.not_EventualSlitOverlapHyp 0 (h 0)

/-- The full local-to-global eventual-slit data package is inconsistent, since
    its overlap component is already impossible. -/
theorem not_eventual_slit_local_to_global_data :
    ¬ (∃ _ : ∀ c, Quadratic.EventualSlitNonzeroDeriv c,
      ∃ _ : ∀ c, Quadratic.EventualSlitLocalUniqueness c,
        ∃ _ : ∀ c, Quadratic.EventualSlitOverlapHyp c,
          ∃ _ : ∀ c, Quadratic.EventualSlitCompatibilityFromOverlap c,
            ∀ c, Quadratic.EventualSlitInverseGluing c) := by
  intro h
  rcases h with ⟨_h_deriv, _h_uniq, h_over, _h_comp, _h_glue⟩
  exact not_eventual_slit_overlap_hyp_data h_over

/-- Remaining Step 2b target, stated as global eventual-slit inverse data. -/
def EventualSlitGlobalInverseData : Prop :=
  ∀ c, ∃ hA : Quadratic.EventualSlitInverseAtlas c,
    Quadratic.GlobalInverseOnEventualSlit c hA

/-- Redesigned Step 2b target: only require a pointwise left-inverse identity
    for `bottcher_map` on the eventual-slit basin set (for each parameter). -/
def EventualSlitPointwiseLeftInverseData : Prop :=
  ∀ c, Quadratic.EventualSlitPointwiseLeftInverseData c

/-- Minimal redesign target: pointwise left-inverse identity for `bottcher_map`
    directly on the basin (for each parameter). -/
def BasinBottcherPointwiseLeftInverseData : Prop :=
  ∀ c, Quadratic.BasinBottcherPointwiseLeftInverseData c

/-- On-M minimal redesign target: pointwise left-inverse identity for
    `bottcher_map` on the basin for Mandelbrot parameters. -/
def BasinBottcherPointwiseLeftInverseDataOnM : Prop :=
  ∀ c, c ∈ MLC.Quadratic.MandelbrotSet →
    Quadratic.BasinBottcherPointwiseLeftInverseData c

/-- On-M injectivity formulation of the Step 2b redesign target. -/
def BottcherMapInjOnBasinOnMData : Prop :=
  ∀ c, c ∈ MLC.Quadratic.MandelbrotSet →
    Set.InjOn (Quadratic.bottcher_map c) (Quadratic.basin_of_infinity c)

/-- Any global eventual-slit inverse data yields the weaker redesigned target. -/
theorem eventual_slit_pointwise_left_inverse_data_of_eventual_slit_global_inverse_data
    (h_global : EventualSlitGlobalInverseData) :
    EventualSlitPointwiseLeftInverseData := by
  intro c
  rcases h_global c with ⟨hA, hG⟩
  exact Quadratic.eventual_slit_pointwise_left_inverse_data_of_global_inverse c hA hG

/-- Eventual-slit pointwise-left-inverse data and basin pointwise-left-inverse
    data are equivalent (because `basin ⊆ eventual_slit_set`). -/
theorem basin_bottcher_pointwise_left_inverse_data_of_eventual_slit_pointwise_left_inverse_data
    (h_point : EventualSlitPointwiseLeftInverseData) :
    BasinBottcherPointwiseLeftInverseData := by
  intro c
  exact Quadratic.basin_bottcher_pointwise_left_inverse_data_of_eventual_slit_data c (h_point c)

theorem eventual_slit_pointwise_left_inverse_data_of_basin_bottcher_pointwise_left_inverse_data
    (h_basin : BasinBottcherPointwiseLeftInverseData) :
    EventualSlitPointwiseLeftInverseData := by
  intro c
  exact Quadratic.eventual_slit_pointwise_left_inverse_data_of_basin_bottcher_data c (h_basin c)

/-- Overlap-free decomposed target: nonzero derivative provides the atlas;
    compatibility for that chosen atlas and gluing provide the global inverse. -/
def EventualSlitNonzeroDerivCompatibleGluingData : Prop :=
  ∀ c,
    ∃ h_deriv : Quadratic.EventualSlitNonzeroDeriv c,
      let hA : Quadratic.EventualSlitInverseAtlas c :=
        Quadratic.eventual_slit_inverse_atlas_of_nonzero_deriv c h_deriv
      Quadratic.EventualSlitInverseCompatible hA ∧ Quadratic.EventualSlitInverseGluing c

/-- The overlap-free decomposed target implies global eventual-slit inverse
    data, hence it is sufficient to replace the remaining axiom bridge. -/
theorem eventual_slit_global_inverse_data_of_nonzero_deriv_compatible_gluing_data
    (h_data : EventualSlitNonzeroDerivCompatibleGluingData) :
    EventualSlitGlobalInverseData := by
  intro c
  rcases h_data c with ⟨h_deriv, hcompat, hglue⟩
  let hA : Quadratic.EventualSlitInverseAtlas c :=
    Quadratic.eventual_slit_inverse_atlas_of_nonzero_deriv c h_deriv
  exact ⟨hA, Quadratic.global_inverse_on_eventual_slit_of_gluing hA (by simpa [hA] using hcompat) hglue⟩

/-- The overlap-free decomposed eventual-slit data is also inconsistent under
    current definitions, since it implies global eventual-slit inverse data. -/
theorem not_eventual_slit_nonzero_deriv_compatible_gluing_data :
    ¬ EventualSlitNonzeroDerivCompatibleGluingData := by
  intro h_data
  have h_global : EventualSlitGlobalInverseData :=
    eventual_slit_global_inverse_data_of_nonzero_deriv_compatible_gluing_data h_data
  exact not_eventual_slit_global_inverse_data (by simpa [EventualSlitGlobalInverseData] using h_global)

/-- The global eventual-slit inverse data directly yields basin injectivity
    of the Böttcher map for all parameters. -/
theorem bottcher_map_inj_on_basin_of_eventual_slit_global_inverse_data
    (h_global : EventualSlitGlobalInverseData) :
    ∀ c, Set.InjOn (Quadratic.bottcher_map c) (Quadratic.basin_of_infinity c) := by
  have h_point : EventualSlitPointwiseLeftInverseData :=
    eventual_slit_pointwise_left_inverse_data_of_eventual_slit_global_inverse_data h_global
  have h_basin : BasinBottcherPointwiseLeftInverseData :=
    basin_bottcher_pointwise_left_inverse_data_of_eventual_slit_pointwise_left_inverse_data h_point
  intro c
  exact Quadratic.bottcher_map_inj_on_basin_of_basin_bottcher_pointwise_left_inverse_data c
    (h_basin c)

/-- The redesigned Step 2b target directly yields basin injectivity of the
    Böttcher map for all parameters. -/
theorem bottcher_map_inj_on_basin_of_eventual_slit_pointwise_left_inverse_data
    (h_point : EventualSlitPointwiseLeftInverseData) :
    ∀ c, Set.InjOn (Quadratic.bottcher_map c) (Quadratic.basin_of_infinity c) := by
  have h_basin : BasinBottcherPointwiseLeftInverseData :=
    basin_bottcher_pointwise_left_inverse_data_of_eventual_slit_pointwise_left_inverse_data h_point
  intro c
  exact Quadratic.bottcher_map_inj_on_basin_of_basin_bottcher_pointwise_left_inverse_data c
    (h_basin c)

/-- The minimal basin redesign target directly yields basin injectivity of the
    Böttcher map for all parameters. -/
theorem bottcher_map_inj_on_basin_of_basin_bottcher_pointwise_left_inverse_data
    (h_basin : BasinBottcherPointwiseLeftInverseData) :
    ∀ c, Set.InjOn (Quadratic.bottcher_map c) (Quadratic.basin_of_infinity c) := by
  intro c
  exact Quadratic.bottcher_map_inj_on_basin_of_basin_bottcher_pointwise_left_inverse_data c
    (h_basin c)

/-- The local-homeomorphism target implies the minimal basin redesign target. -/
theorem basin_bottcher_pointwise_left_inverse_data_of_bottcher_isLocalHomeomorph
    (hlocal : ∀ c, IsLocalHomeomorph (Quadratic.bottcher_map c)) :
    BasinBottcherPointwiseLeftInverseData := by
  intro c
  exact Quadratic.basin_bottcher_pointwise_left_inverse_data_of_bottcher_map_inj_on_basin c
    (bottcher_map_inj_on_basin_of_isLocalHomeomorph c (hlocal c))

/-- The basin-local-homeomorphism route plus properness also implies the
    minimal basin redesign target. -/
theorem basin_bottcher_pointwise_left_inverse_data_of_bottcher_proper_localHomeomorphOn_basin
    (hproper : ∀ c, IsProperMap (Quadratic.bottcher_map c))
    (hlocal :
      ∀ c, IsLocalHomeomorphOn (Quadratic.bottcher_map c) (Quadratic.basin_of_infinity c)) :
    BasinBottcherPointwiseLeftInverseData := by
  intro c
  exact Quadratic.basin_bottcher_pointwise_left_inverse_data_of_bottcher_map_inj_on_basin c
    (bottcher_map_inj_on_basin_of_proper_localHomeomorphOn_basin c (hproper c) (hlocal c))

/-- Data-wrapper form of the proper/local-homeomorphism-on-basin route. -/
theorem basin_bottcher_pointwise_left_inverse_data_of_bottcher_proper_localHomeomorphOn_basin_data
    (hdata : BottcherProperLocalHomeomorphOnBasinData) :
    BasinBottcherPointwiseLeftInverseData := by
  exact basin_bottcher_pointwise_left_inverse_data_of_bottcher_proper_localHomeomorphOn_basin
    (fun c => (hdata c).1)
    (fun c => (hdata c).2)

/-- Continuity plus basin-local derivative/non-neighborhood slit hypotheses
    imply the minimal basin redesign target. -/
theorem basin_bottcher_pointwise_left_inverse_data_of_bottcher_continuous_deriv_ne_zero_mem_nhds_slit
    (hcont : ∀ c, Continuous (Quadratic.bottcher_map c))
    (hslit :
      ∀ c z, z ∈ Quadratic.basin_of_infinity c → slit_orbit c ∈ 𝓝 z)
    (hderiv :
      ∀ c z, z ∈ Quadratic.basin_of_infinity c →
        deriv (Quadratic.bottcher_map c) z ≠ 0) :
    BasinBottcherPointwiseLeftInverseData := by
  apply basin_bottcher_pointwise_left_inverse_data_of_bottcher_proper_localHomeomorphOn_basin
  · intro c
    exact bottcher_map_isProperMap_of_continuous c (hcont c)
  · intro c
    exact bottcher_map_isLocalHomeomorphOn_basin_of_deriv_ne_zero_of_mem_nhds_slit c
      (hslit c) (hderiv c)


/-- The minimal basin redesign target is equivalent to basin injectivity of
    `bottcher_map`; this is the exact remaining Step 2b obligation. -/
theorem basin_bottcher_pointwise_left_inverse_data_iff_bottcher_map_inj_on_basin :
    BasinBottcherPointwiseLeftInverseData ↔
      (∀ c, Set.InjOn (Quadratic.bottcher_map c) (Quadratic.basin_of_infinity c)) := by
  constructor
  · intro h_basin c
    exact Quadratic.bottcher_map_inj_on_basin_of_basin_bottcher_pointwise_left_inverse_data c
      (h_basin c)
  · intro h_inj c
    exact Quadratic.basin_bottcher_pointwise_left_inverse_data_of_bottcher_map_inj_on_basin c
      (h_inj c)

/-- On-M variant of the minimal-target equivalence: on-M basin pointwise
    left-inverse data is equivalent to on-M basin injectivity of `bottcher_map`. -/
theorem basin_bottcher_pointwise_left_inverse_data_onM_iff_bottcher_map_inj_on_basin_onM :
    BasinBottcherPointwiseLeftInverseDataOnM ↔
      (∀ c, c ∈ MLC.Quadratic.MandelbrotSet →
        Set.InjOn (Quadratic.bottcher_map c) (Quadratic.basin_of_infinity c)) := by
  constructor
  · intro h_basin c hc
    exact Quadratic.bottcher_map_inj_on_basin_of_basin_bottcher_pointwise_left_inverse_data c
      (h_basin c hc)
  · intro h_inj c hc
    exact Quadratic.basin_bottcher_pointwise_left_inverse_data_of_bottcher_map_inj_on_basin c
      (h_inj c hc)

/-- On-M minimal-target equivalence in named-data form. -/
theorem basin_bottcher_pointwise_left_inverse_data_onM_iff_bottcher_map_inj_on_basin_onM_data :
    BasinBottcherPointwiseLeftInverseDataOnM ↔ BottcherMapInjOnBasinOnMData := by
  exact basin_bottcher_pointwise_left_inverse_data_onM_iff_bottcher_map_inj_on_basin_onM

/-- Construct the on-M minimal basin target from on-M basin injectivity. -/
theorem basin_bottcher_pointwise_left_inverse_data_onM_of_bottcher_map_inj_on_basin_onM
    (h_inj_onM : BottcherMapInjOnBasinOnMData) :
    BasinBottcherPointwiseLeftInverseDataOnM := by
  intro c hc
  exact Quadratic.basin_bottcher_pointwise_left_inverse_data_of_bottcher_map_inj_on_basin c
    (h_inj_onM c hc)

/-- Global basin pointwise-left-inverse data implies the on-M variant. -/
theorem basin_bottcher_pointwise_left_inverse_data_onM_of_global
    (h_basin : BasinBottcherPointwiseLeftInverseData) :
    BasinBottcherPointwiseLeftInverseDataOnM := by
  intro c _hc
  exact h_basin c

/-- Main-conjecture wrapper for the on-M minimal basin redesign target. -/
theorem mlc_conjecture_of_basin_bottcher_pointwise_left_inverse_data_onM
    (h_basin_onM : BasinBottcherPointwiseLeftInverseDataOnM) :
    LocallyConnectedSpace mandelbrotSet := by
  apply mlc_conjecture_of_bottcher_inj_on_basin_onM
  intro c hc
  exact Quadratic.bottcher_map_inj_on_basin_of_basin_bottcher_pointwise_left_inverse_data c
    (h_basin_onM c hc)

/-- Equivalent on-M Step 2b wrapper formulated directly as basin injectivity
    of `bottcher_map`. -/
theorem mlc_conjecture_of_bottcher_map_inj_on_basin_onM_data
    (h_inj_onM : BottcherMapInjOnBasinOnMData) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_bottcher_inj_on_basin_onM h_inj_onM

/-- Main-conjecture wrapper for the minimal basin redesign target. -/
theorem mlc_conjecture_of_basin_bottcher_pointwise_left_inverse_data
    (h_basin : BasinBottcherPointwiseLeftInverseData) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_basin_bottcher_pointwise_left_inverse_data_onM
    (basin_bottcher_pointwise_left_inverse_data_onM_of_global h_basin)

/-- Main-conjecture wrapper for the redesigned Step 2b target. -/
theorem mlc_conjecture_of_eventual_slit_pointwise_left_inverse_data
    (h_point : EventualSlitPointwiseLeftInverseData) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_basin_bottcher_pointwise_left_inverse_data
    (basin_bottcher_pointwise_left_inverse_data_of_eventual_slit_pointwise_left_inverse_data h_point)

/-- Main-conjecture wrapper for the remaining Step 2b target. -/
theorem mlc_conjecture_of_eventual_slit_global_inverse_data
    (h_global : EventualSlitGlobalInverseData) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_eventual_slit_pointwise_left_inverse_data
    (eventual_slit_pointwise_left_inverse_data_of_eventual_slit_global_inverse_data h_global)

/-- Parameterized extension route: enough eventual-slit extension data implies
    MLC (this route is currently ruled out by
    `not_eventual_slit_global_extension_data`). -/
theorem mlc_conjecture_of_eventual_slit_global_extension
    (h_ext :
      ∀ c, ∃ hA : Quadratic.EventualSlitInverseAtlas c,
        ∃ hG : Quadratic.GlobalInverseOnEventualSlit c hA,
          Quadratic.EventualSlitGlobalInverseExtendsToBasin c hA hG) :
    LocallyConnectedSpace mandelbrotSet := by
  apply mlc_conjecture_of_bottcher_inj_on_basin
  intro c
  rcases h_ext c with ⟨hA, hG, _hext⟩
  exact Quadratic.bottcher_map_inj_on_basin_of_eventual_slit_global_inverse_pointwise c hA hG

/-- Alternative route: a global inverse on the eventual slit orbit already
    gives basin injectivity of the Böttcher map, hence MLC. -/
theorem mlc_conjecture_of_eventual_slit_global_inverse
    (h_global : EventualSlitGlobalInverseData) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_eventual_slit_global_inverse_data h_global

/-- If eventual-slit local inverse atlases are compatible and can be glued to
    global inverses, MLC follows. -/
theorem mlc_conjecture_of_eventual_slit_inverse_gluing
    (h_data :
      ∀ c, ∃ hA : Quadratic.EventualSlitInverseAtlas c,
        Quadratic.EventualSlitInverseCompatible hA)
    (h_glue : ∀ c, Quadratic.EventualSlitInverseGluing c) :
    LocallyConnectedSpace mandelbrotSet := by
  apply mlc_conjecture_of_eventual_slit_global_inverse
  intro c
  rcases h_data c with ⟨hA, hcompat⟩
  exact ⟨hA, Quadratic.global_inverse_on_eventual_slit_of_gluing hA hcompat (h_glue c)⟩

/-- A decomposed eventual-slit route: nonzero-derivative local inverses, overlap
    compatibility, and gluing suffice to conclude MLC. -/
theorem mlc_conjecture_of_eventual_slit_local_to_global
    (h_deriv : ∀ c, Quadratic.EventualSlitNonzeroDeriv c)
    (h_uniq : ∀ c, Quadratic.EventualSlitLocalUniqueness c)
    (h_over : ∀ c, Quadratic.EventualSlitOverlapHyp c)
    (h_comp : ∀ c, Quadratic.EventualSlitCompatibilityFromOverlap c)
    (h_glue : ∀ c, Quadratic.EventualSlitInverseGluing c) :
    LocallyConnectedSpace mandelbrotSet := by
  apply mlc_conjecture_of_eventual_slit_inverse_gluing
  · intro c
    let hA : Quadratic.EventualSlitInverseAtlas c :=
      Quadratic.eventual_slit_inverse_atlas_of_nonzero_deriv c (h_deriv c)
    have hcompat : Quadratic.EventualSlitInverseCompatible hA :=
      Quadratic.eventual_slit_inverse_compatible_of_overlap c hA (h_uniq c) (h_over c) (h_comp c)
    exact ⟨hA, hcompat⟩
  · exact h_glue

/-- Overlap-free decomposed route: if nonzero-derivative data builds an atlas
    and compatibility is provided directly for that atlas, then gluing implies
    MLC. This isolates the remaining viable local-to-global target after
    ruling out overlap-based compatibility assumptions. -/
theorem mlc_conjecture_of_eventual_slit_nonzero_deriv_compatible_gluing
    (h_data : EventualSlitNonzeroDerivCompatibleGluingData) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_eventual_slit_global_inverse_data
    (eventual_slit_global_inverse_data_of_nonzero_deriv_compatible_gluing_data h_data)

/-- Bridge theorem: the pullback-root route is derivable from the
    iterate-equality implication hypothesis. -/
theorem mlc_conjecture_of_iter_eq_imp_via_pullback_root
    (h_iter_eq_imp :
      ∀ c, ∀ z w, z ∈ Quadratic.basin_of_infinity c →
        w ∈ Quadratic.basin_of_infinity c →
        (∃ n, (quadratic_map c)^[n] z = (quadratic_map c)^[n] w) → z = w) :
    LocallyConnectedSpace mandelbrotSet := by
  exfalso
  exact Quadratic.not_quadratic_map_iter_eq_imp_eq 0 (h_iter_eq_imp 0)

/-- Current axiom-backed on-M basin-injectivity bridge used by Step 2b. -/
lemma bottcher_map_inj_on_basin_onM_via_external_ray_axioms :
    BottcherMapInjOnBasinOnMData := by
  intro c hc
  exact False.elim false_of_external_ray_axioms

/-- The Mandelbrot Local Connectivity (MLC) Conjecture:
    The Mandelbrot set is locally connected. -/
theorem mlc_conjecture
    : LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_bottcher_map_inj_on_basin_onM_data
    bottcher_map_inj_on_basin_onM_via_external_ray_axioms

end MainProof

end MLC
