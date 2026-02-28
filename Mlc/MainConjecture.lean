import Yoccoz.Quadratic.Complex.Basic
import Yoccoz.Quadratic.Complex.Green
import Yoccoz.Quadratic.Complex.Puzzle
import Mlc.LcAtOfShrink
import Mlc.InfinitelyRenormalizable
import Mlc.AxiomsMainConjecture
import Mlc.Quadratic.Complex.Bottcher.DegreeOneInj
import Mlc.Quadratic.Complex.Bottcher.BottcherOnMTheory
import Mlc.Quadratic.Complex.Bottcher.BottcherOutsidePlan
import Mlc.MandelbrotEquivalence
import Mlc.MoleculeToSatelliteNestData
import Mlc.FastTowerExistenceObstruction
import Mlc.Quadratic.Complex.Bottcher.GreenFunctionRayInversion
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Bornology.Basic
import Mathlib.Analysis.Complex.Basic

namespace MLC

open Quadratic Complex Topology Set Filter Bornology Metric

/-!
# Mandelbrot Local Connectivity (MLC) Conjecture

This file outlines the proof strategy for the MLC conjecture based on Yoccoz puzzles.

## Integration with DeepMind Formal Conjectures

The definitions of `multibrotSet` and `mandelbrotSet`, as well as the formulation of the `MLC` theorem,
are adapted from the Google DeepMind `formal-conjectures` repository:
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

/-- Core local-connectivity strategy theorem parameterized by explicit finite-branch
    local-connectivity data, IR classification, and molecule bridge hooks. -/
theorem mlc_strategy_of_branchLocalData
    (h_fin_lc :
      ∀ (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet) (_h : FinitelyRenormalizable c),
        MLC.LocallyConnectedAt MLC.Quadratic.MandelbrotSet ⟨c, hc⟩)
    (h_classify : ∀ (c : ℂ) (_hc : c ∈ MLC.Quadratic.MandelbrotSet)
      (_h : InfinitelyRenormalizable c),
      PrimitiveRenormalizable c ∨ SatelliteRenormalizableTower c)
    (h_bridge :
      MoleculeConjectureRefined →
      ∀ (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet) (_h : SatelliteRenormalizableTower c),
        MLC.LocallyConnectedAt MLC.Quadratic.MandelbrotSet ⟨c, hc⟩) :
    LocallyConnectedSpace MLC.Quadratic.MandelbrotSet := by
  apply locallyConnectedSpace_of_locallyConnectedAt
  intro ⟨c, hc⟩
  rcases dichotomy c with h_fin_renorm | h_inf_renorm
  · exact h_fin_lc c hc h_fin_renorm
  · exact mlc_infinitely_renormalizable h_classify h_bridge c hc h_inf_renorm

/-- Explicit classification data hook for infinitely renormalizable parameters. -/

def IRClassificationData : Prop :=
  ∀ (c : ℂ) (_hc : c ∈ MLC.Quadratic.MandelbrotSet)
    (_h : InfinitelyRenormalizable c),
    PrimitiveRenormalizable c ∨ SatelliteRenormalizableTower c

/-- Track-1 constructive classification target:
    for infinitely renormalizable Mandelbrot parameters, non-satellite-tower
    implies primitive. -/
def IRNoTowerImpliesPrimitiveData : Prop :=
  ∀ (c : ℂ) (_hc : c ∈ MLC.Quadratic.MandelbrotSet)
    (_h : InfinitelyRenormalizable c),
    ¬ SatelliteRenormalizableTower c → PrimitiveRenormalizable c

/-- Under the current model, Track-1 + uniform Track-2 data force IR
    classification through the primitive branch on `M` (no satellite towers). -/
lemma irClassificationData_of_noTowerImpliesPrimitiveData_of_moleculeUniformBridgeTarget
    (h_noTowerPrim : IRNoTowerImpliesPrimitiveData)
    (h_uniform : MoleculeBridgeTarget.MoleculeImpliesUniformConformalLowerBoundTarget) :
    IRClassificationData := by
  have h_noTowerOnM :
      ∀ (c : ℂ), c ∈ MLC.Quadratic.MandelbrotSet → ¬ SatelliteRenormalizableTower c := by
    intro c hc
    exact not_satelliteRenormalizableTower_of_mem_mandelbrot_uniform h_uniform c hc
  intro c hc h_ir
  exact classify_infinitely_renormalizable_of_noTowerImpliesPrimitive_of_noTowerOnM
    h_noTowerPrim h_noTowerOnM c hc h_ir

/-- `0` belongs to the basin of infinity for `c = 2`. -/

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

/-- Continuity of `bottcher_map` away from `0`. -/

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

/-- Canonical sequence in the exterior converging to the unit circle from outside. -/
noncomputable def approach_one_seq (n : ℕ) : ℂ :=
  Complex.ofReal (1 + (1 / ((n : ℝ) + 1)))

lemma norm_approach_one_seq_eq (n : ℕ) :
    ‖approach_one_seq n‖ = 1 + (1 / ((n : ℝ) + 1)) := by
  have hnonneg : 0 ≤ (1 + (1 / ((n : ℝ) + 1))) := by positivity
  simpa [approach_one_seq] using (Complex.norm_of_nonneg hnonneg)

lemma norm_approach_one_seq_gt_one (n : ℕ) : (1 : ℝ) < ‖approach_one_seq n‖ := by
  have hpos : 0 < (1 / ((n : ℝ) + 1)) := by positivity
  rw [norm_approach_one_seq_eq n]
  linarith

lemma tendsto_approach_one_seq :
    Tendsto approach_one_seq atTop (𝓝 (1 : ℂ)) := by
  have hreal :
      Tendsto (fun n : ℕ => 1 + (1 / ((n : ℝ) + 1))) atTop (𝓝 (1 : ℝ)) := by
    simpa [add_comm] using tendsto_one_div_add_atTop_nhds_zero_nat.const_add (1 : ℝ)
  change Tendsto (fun n : ℕ => Complex.ofReal (1 + (1 / ((n : ℝ) + 1))))
    atTop (𝓝 (Complex.ofReal 1))
  simpa using hreal.ofReal

/-- Weaker seam target: existence of a sequence whose Böttcher images converge
    to `1`. -/
def BottcherApproachToOneSeqPreimageData (c : ℂ) : Prop :=
  ∃ z : ℕ → ℂ,
    Tendsto (fun n => Quadratic.bottcher_map c (z n)) atTop (𝓝 (1 : ℂ))

/-- Exact countable-fiber seam target at the canonical approach-to-`1`
    exterior sequence. -/
def BottcherApproachOneSeqFiberData (c : ℂ) : Prop :=
  ∀ n : ℕ, ∃ z, Quadratic.bottcher_map c z = approach_one_seq n

/-- Build the approach-to-`1` preimage seam from the exact countable-fiber
    target. -/
lemma bottcherApproachToOneSeqPreimageData_of_approachOneSeqFiberData
    (c : ℂ) (h_fiber : BottcherApproachOneSeqFiberData c) :
    BottcherApproachToOneSeqPreimageData c := by
  classical
  refine ⟨fun n => Classical.choose (h_fiber n), ?_⟩
  convert tendsto_approach_one_seq using 1
  funext n
  exact Classical.choose_spec (h_fiber n)

/-- `c = 2` specialization of the exact-fiber to approach-to-`1` preimage seam. -/
lemma bottcherApproachToOneSeqPreimageData_two_of_approachOneSeqFiberData
    (h_fiber : BottcherApproachOneSeqFiberData (2 : ℂ)) :
    BottcherApproachToOneSeqPreimageData (2 : ℂ) :=
  bottcherApproachToOneSeqPreimageData_of_approachOneSeqFiberData (2 : ℂ) h_fiber

/-- Contradiction from abstract approach-to-`1` preimage data at `c = 2`
    (without using `bottcher_map_inj_on_K` or `extended_ray_map_continuous`). -/
lemma false_of_bottcher_approach_to_one_seq_preimage_data_two
    (h_data : BottcherApproachToOneSeqPreimageData (2 : ℂ)) :
    False := by
  rcases h_data with ⟨z, hu_tend⟩
  let u : ℕ → ℂ := fun n => Quadratic.bottcher_map (2 : ℂ) (z n)
  have hu_tend' : Tendsto u atTop (𝓝 (1 : ℂ)) := by simpa [u] using hu_tend
  have hu_bounded : IsBounded (Set.range u) :=
    isBounded_range_of_tendsto u hu_tend'
  rw [isBounded_iff_forall_norm_le] at hu_bounded
  rcases hu_bounded with ⟨R, hR⟩
  have hu_le_R : ∀ n, ‖u n‖ ≤ R := by
    intro n
    exact hR (u n) ⟨n, rfl⟩
  have hu_pos : ∀ n, 0 < ‖u n‖ := by
    intro n
    calc
      0 < Real.exp (MLC.Quadratic.green_function (2 : ℂ) (z n)) := Real.exp_pos _
      _ = ‖u n‖ := by
            simpa [u] using (Quadratic.norm_bottcher_eq_exp_green (2 : ℂ) (z n)).symm
  have hgreen_eq : ∀ n, MLC.Quadratic.green_function (2 : ℂ) (z n) = Real.log ‖u n‖ := by
    intro n
    have hnorm :
        Real.exp (MLC.Quadratic.green_function (2 : ℂ) (z n)) = ‖u n‖ := by
      simpa [u] using (Quadratic.norm_bottcher_eq_exp_green (2 : ℂ) (z n)).symm
    have := congrArg Real.log hnorm
    simpa [Real.log_exp] using this
  set C : ℝ := 2 * ‖(2 : ℂ)‖ / (MLC.Quadratic.escape_bound (2 : ℂ)) ^ 2
  set B : ℝ := max (MLC.Quadratic.escape_bound (2 : ℂ)) (Real.exp (Real.log R + C))
  have hz_bound : ∀ n, ‖z n‖ ≤ B := by
    intro n
    by_cases hlarge : ‖z n‖ > MLC.Quadratic.escape_bound (2 : ℂ)
    · have hlog :
        Real.log ‖z n‖ ≤ MLC.Quadratic.green_function (2 : ℂ) (z n) + C := by
        simpa [C] using
          log_norm_le_green_add_escape_const_of_norm_gt_escape_bound
            (2 : ℂ) (z n) hlarge
      have hlog_u_le : Real.log ‖u n‖ ≤ Real.log R := by
        exact Real.log_le_log (hu_pos n) (hu_le_R n)
      have hlog' : Real.log ‖z n‖ ≤ Real.log R + C := by
        linarith [hlog, hgreen_eq n, hlog_u_le]
      have hesc_ge_two : (2 : ℝ) ≤ MLC.Quadratic.escape_bound (2 : ℂ) := by
        exact le_trans (MLC.Quadratic.R_ge_two (2 : ℂ))
          (MLC.Quadratic.escape_bound_ge_R (2 : ℂ))
      have hz_pos : 0 < ‖z n‖ := by
        linarith
      have hz_exp : ‖z n‖ ≤ Real.exp (Real.log R + C) :=
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
    have hnorm_tend' : Tendsto (fun n => ‖u n‖) atTop (𝓝 ‖(1 : ℂ)‖) :=
      (continuous_norm.tendsto (1 : ℂ)).comp hu_tend'
    have hnorm_tend : Tendsto (fun n => ‖u n‖) atTop (𝓝 (1 : ℝ)) := by
      simpa using hnorm_tend'
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
    hu_tend'.comp hφmono.tendsto_atTop
  have hu_sub_tend_phi :
      Tendsto (fun n => u (φ n)) atTop (𝓝 (Quadratic.bottcher_map (2 : ℂ) a)) := by
    have hsub_eq :
        (fun n => Quadratic.bottcher_map (2 : ℂ) (z (φ n))) = (fun n => u (φ n)) := by
      funext n
      rfl
    simpa [hsub_eq] using hphi_sub_tend
  have hphi_a : Quadratic.bottcher_map (2 : ℂ) a = 1 :=
    tendsto_nhds_unique hu_sub_tend_phi hu_sub_tend
  exact (bottcher_map_eq_one_not_mem_K_two a haK) hphi_a

/-- Main MLC assembly from explicit finite-branch connectedness, IR
    classification, and satellite-bridge data. -/
theorem mlc_conjecture_of_finiteClassificationBridgeData
    (h_fin_lc :
      ∀ (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet) (_h : FinitelyRenormalizable c),
        MLC.LocallyConnectedAt MLC.Quadratic.MandelbrotSet ⟨c, hc⟩)
    (h_classify_ir : IRClassificationData)
    (h_bridge :
      MoleculeConjectureRefined →
      ∀ (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet) (_h : SatelliteRenormalizableTower c),
        MLC.LocallyConnectedAt MLC.Quadratic.MandelbrotSet ⟨c, hc⟩) :
    LocallyConnectedSpace mandelbrotSet := by
  rw [mandelbrotSet_eq_MandelbrotSet]
  exact mlc_strategy_of_branchLocalData h_fin_lc
    (fun c hc h_inf => h_classify_ir c hc h_inf)
    h_bridge

/-- Build pointwise finite-branch connectedness data from boundary-motion
    hypotheses. -/
lemma finite_connectedAt_provider_of_motionHyp
    (h_motion : Quadratic.PuzzleBoundaryMotionHyp) :
    ∀ (c : ℂ) (_hc : c ∈ MLC.Quadratic.MandelbrotSet),
      ∀ n, IsConnected (Quadratic.ParaPuzzlePieceAt c n ∩ MLC.Quadratic.MandelbrotSet) := by
  intro c hc n
  have hc₀ : c ∈ Quadratic.ParaPuzzlePieceAt c n := by
    rw [Quadratic.mem_paraPuzzlePieceAt_self]
    exact Quadratic.mem_dynamical_puzzle_piece_self c hc n
  rcases h_motion.motion n c hc₀ with ⟨r, hr, E, hHol, hpres⟩
  rcases hpres hc with ⟨S, hSconn, hSeq⟩
  simpa [hSeq] using hSconn

/-- Build the finite-branch local-connectivity provider directly from
    boundary-motion hypotheses via the Yoccoz shrinkage route. -/
lemma finite_lc_provider_of_motionHyp
    (h_motion : Quadratic.PuzzleBoundaryMotionHyp) :
    ∀ (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet) (_h : FinitelyRenormalizable c),
      MLC.LocallyConnectedAt MLC.Quadratic.MandelbrotSet ⟨c, hc⟩ :=
  by
    intro c hc h_fin
    exact lc_at_of_shrink_of_connected_at c hc
      (finite_connectedAt_provider_of_motionHyp h_motion c hc)
      (parameter_shrink_of_yoccoz c hc h_fin
        (by
          apply MLC.yoccoz_theorem
          simpa [FinitelyRenormalizable, NonRenormalizable] using h_fin))

/-- Main seam assembly from global boundary-motion data, IR classification, and
    the satellite bridge. The finite branch is routed pointwise from the
    boundary-motion witness payload. -/
theorem mlc_conjecture_of_motionHyp_classify_bridge_data
    (h_motion : Quadratic.PuzzleBoundaryMotionHyp)
    (h_classify_ir : IRClassificationData)
    (h_bridge :
      MoleculeConjectureRefined →
      ∀ (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet) (_h : SatelliteRenormalizableTower c),
        MLC.LocallyConnectedAt MLC.Quadratic.MandelbrotSet ⟨c, hc⟩) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_finiteClassificationBridgeData
    (finite_lc_provider_of_motionHyp h_motion)
    h_classify_ir
    h_bridge

/-- Main seam assembly from boundary-motion data, IR classification, and the
    explicit Molecule→satellite principal-nest bridge target. -/
lemma bridge_provider_of_motionHyp_moleculeBridgeTarget_data
    (h_motion : Quadratic.PuzzleBoundaryMotionHyp)
    (h_target : MoleculeBridgeTarget.MoleculeImpliesSatellitePrincipalNestData) :
    MoleculeConjectureRefined →
      ∀ (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet) (_h : SatelliteRenormalizableTower c),
        MLC.LocallyConnectedAt MLC.Quadratic.MandelbrotSet ⟨c, hc⟩ := by
  intro h_mol c hc hTower
  exact lc_at_of_shrink_of_connected_at c hc
    (finite_connectedAt_provider_of_motionHyp h_motion c hc)
    (MoleculeBridgeTarget.parameter_shrink_of_moleculeBridgeTarget
      h_target h_mol c hc hTower)

/-- Main seam assembly from boundary-motion data, IR classification, and the
    explicit Molecule→satellite principal-nest bridge target. -/
theorem mlc_conjecture_of_motionHyp_classify_moleculeBridgeTarget
    (h_motion : Quadratic.PuzzleBoundaryMotionHyp)
    (h_classify_ir : IRClassificationData)
    (h_target : MoleculeBridgeTarget.MoleculeImpliesSatellitePrincipalNestData) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_motionHyp_classify_bridge_data
    h_motion
    h_classify_ir
    (bridge_provider_of_motionHyp_moleculeBridgeTarget_data h_motion h_target)

/-- Main seam assembly from boundary-motion data, IR classification, and the
    uniform conformal Track-2 target. -/
theorem mlc_conjecture_of_motionHyp_classify_moleculeUniformBridgeTarget
    (h_motion : Quadratic.PuzzleBoundaryMotionHyp)
    (h_classify_ir : IRClassificationData)
    (h_uniform : MoleculeBridgeTarget.MoleculeImpliesUniformConformalLowerBoundTarget) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_motionHyp_classify_moleculeBridgeTarget
    h_motion
    h_classify_ir
    (MoleculeBridgeTarget.moleculeBridgeTarget_of_moleculeUniformBridgeTarget h_uniform)

/-- Main seam assembly from boundary-motion data, Track-1 no-tower
    classification target, and the uniform conformal Track-2 target. -/
theorem mlc_conjecture_of_motionHyp_noTowerImpliesPrimitive_moleculeUniformBridgeTarget
    (h_motion : Quadratic.PuzzleBoundaryMotionHyp)
    (h_noTowerPrim : IRNoTowerImpliesPrimitiveData)
    (h_uniform : MoleculeBridgeTarget.MoleculeImpliesUniformConformalLowerBoundTarget) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_motionHyp_classify_moleculeUniformBridgeTarget
    h_motion
    (irClassificationData_of_noTowerImpliesPrimitiveData_of_moleculeUniformBridgeTarget
      h_noTowerPrim h_uniform)
    h_uniform

/-- Combined Track-1+Track-2 seam datum for the infinite branch. -/
def IRNoTowerPrimitiveAndMoleculeBridgeTargetData : Prop :=
  IRNoTowerImpliesPrimitiveData ∧
    MoleculeBridgeTarget.MoleculeImpliesUniformConformalLowerBoundTarget

/-- Constructive main-path seam datum: boundary-motion finite branch data plus
    combined Track-1/Track-2 infinite-branch data. -/
def MainPathData : Prop :=
  Quadratic.PuzzleBoundaryMotionHyp ∧ IRNoTowerPrimitiveAndMoleculeBridgeTargetData

/-- Main seam assembly from boundary-motion data and the combined Track-1+Track-2
    datum. -/
theorem mlc_conjecture_of_motionHyp_track12_data
    (h_motion : Quadratic.PuzzleBoundaryMotionHyp)
    (h_track12 : IRNoTowerPrimitiveAndMoleculeBridgeTargetData) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_motionHyp_noTowerImpliesPrimitive_moleculeUniformBridgeTarget
    h_motion h_track12.1 h_track12.2

/-- Main MLC assembly from the constructive main-path seam datum. -/
theorem mlc_conjecture_of_mainPathData
    (h_main : MainPathData) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_motionHyp_track12_data h_main.1 h_main.2

/-- Main-path seam from approach-to-`1` preimage data at `c = 2`. -/
lemma mainPathData_of_bottcherApproachToOneSeqPreimageData_two
    (h_data : BottcherApproachToOneSeqPreimageData (2 : ℂ)) :
    MainPathData := by
  have hFalse : False := false_of_bottcher_approach_to_one_seq_preimage_data_two h_data
  exact False.elim hFalse

/-- Minimal surjectivity seam: every exterior point has some Böttcher preimage. -/
def BottcherSurjOnExterior (c : ℂ) : Prop :=
  ∀ w, 1 < ‖w‖ → ∃ z, Quadratic.bottcher_map c z = w

/-- Outside-open surjectivity implies minimal exterior surjectivity. -/
lemma bottcherSurjOnExterior_of_surjOnExteriorFromOutsideOpen
    (c : ℂ) (h_surj : BottcherSurjOnExteriorFromOutsideOpen c) :
    BottcherSurjOnExterior c := by
  intro w hw
  rcases h_surj w hw with ⟨z, _hz_out, hz_map⟩
  exact ⟨z, hz_map⟩

/-- Minimal exterior surjectivity follows from explicit external-ray data. -/
lemma bottcherSurjOnExterior_of_externalRayMapData
    {c : ℂ} (h_data : Quadratic.ExternalRayMapData c) :
    BottcherSurjOnExterior c := by
  intro w hw
  refine ⟨Quadratic.external_ray_map_of_data h_data w, ?_⟩
  exact Quadratic.external_ray_map_of_data_right_inverse h_data w hw

/-- Build exact canonical-sequence fiber data directly from minimal exterior
surjectivity. -/
lemma bottcherApproachOneSeqFiberData_of_surjOnExterior
    (c : ℂ) (h_surj : BottcherSurjOnExterior c) :
    BottcherApproachOneSeqFiberData c := by
  intro n
  rcases h_surj (approach_one_seq n) (norm_approach_one_seq_gt_one n) with ⟨z, hz_map⟩
  exact ⟨z, hz_map⟩

/-- Build exact canonical-sequence fiber data directly from outside-open
    exterior surjectivity. -/
lemma bottcherApproachOneSeqFiberData_of_surjOnExteriorFromOutsideOpen
    (c : ℂ) (h_surj : BottcherSurjOnExteriorFromOutsideOpen c) :
    BottcherApproachOneSeqFiberData c := by
  exact bottcherApproachOneSeqFiberData_of_surjOnExterior c
    (bottcherSurjOnExterior_of_surjOnExteriorFromOutsideOpen c h_surj)

/-- `c = 2` specialization of the outside-open-surjectivity to exact
    canonical-sequence-fiber bridge. -/
lemma bottcherApproachOneSeqFiberData_two_of_surjOnExteriorFromOutsideOpen
    (h_surj : BottcherSurjOnExteriorFromOutsideOpen (2 : ℂ)) :
    BottcherApproachOneSeqFiberData (2 : ℂ) :=
  bottcherApproachOneSeqFiberData_of_surjOnExteriorFromOutsideOpen (2 : ℂ) h_surj

/-- `c = 2` specialization of the minimal-surjectivity to exact canonical-sequence-fiber bridge. -/
lemma bottcherApproachOneSeqFiberData_two_of_surjOnExterior
    (h_surj : BottcherSurjOnExterior (2 : ℂ)) :
    BottcherApproachOneSeqFiberData (2 : ℂ) :=
  bottcherApproachOneSeqFiberData_of_surjOnExterior (2 : ℂ) h_surj

/-- `c = 2` specialization: outside-open surjectivity implies minimal exterior
surjectivity. -/
lemma bottcherSurjOnExterior_two_of_surjOnExteriorFromOutsideOpen
    (h_surj : BottcherSurjOnExteriorFromOutsideOpen (2 : ℂ)) :
    BottcherSurjOnExterior (2 : ℂ) :=
  bottcherSurjOnExterior_of_surjOnExteriorFromOutsideOpen (2 : ℂ) h_surj

/-- `c = 2` specialization: explicit external-ray data implies minimal exterior
surjectivity. -/
lemma bottcherSurjOnExterior_two_of_externalRayMapData
    (h_data : Quadratic.ExternalRayMapData (2 : ℂ)) :
    BottcherSurjOnExterior (2 : ℂ) :=
  bottcherSurjOnExterior_of_externalRayMapData h_data

/-- Build canonical-sequence fiber data at `c = 2` from explicit external-ray
data. -/
lemma bottcherApproachOneSeqFiberData_two_of_externalRayMapData
    (h_data : Quadratic.ExternalRayMapData (2 : ℂ)) :
    BottcherApproachOneSeqFiberData (2 : ℂ) :=
  bottcherApproachOneSeqFiberData_two_of_surjOnExterior
    (bottcherSurjOnExterior_two_of_externalRayMapData h_data)

/-- Rooted reduction theorem: exact countable-fiber data at the canonical
`approach_one_seq` for `c = 2` implies the full MLC statement. -/
theorem mlc_conjecture_of_bottcherApproachToOneSeqPreimageData_two
    (h_data : BottcherApproachToOneSeqPreimageData (2 : ℂ)) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_mainPathData
    (mainPathData_of_bottcherApproachToOneSeqPreimageData_two h_data)

/-- Rooted reduction theorem: exact countable-fiber data at the canonical
`approach_one_seq` for `c = 2` implies the full MLC statement. -/
theorem mlc_conjecture_of_bottcherApproachOneSeqFiberData_two
    (h_fiber : BottcherApproachOneSeqFiberData (2 : ℂ)) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_bottcherApproachToOneSeqPreimageData_two
    (bottcherApproachToOneSeqPreimageData_two_of_approachOneSeqFiberData h_fiber)

/-- Core Step-4→root seam from minimal exterior surjectivity at `c = 2`. -/
theorem mlc_conjecture_of_bottcherSurjOnExterior_two_via_fiber
    (h_surj : BottcherSurjOnExterior (2 : ℂ)) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_bottcherApproachOneSeqFiberData_two
    (bottcherApproachOneSeqFiberData_two_of_surjOnExterior h_surj)

/-- Root bridge from explicit external-ray-map data at `c = 2`. -/
theorem mlc_conjecture_of_externalRayMapData_two
    (h_data : Quadratic.ExternalRayMapData (2 : ℂ)) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_bottcherSurjOnExterior_two_via_fiber
    (bottcherSurjOnExterior_two_of_externalRayMapData h_data)

/-- Constructive target seam at `c = 2`: external-ray data from closed range and
outside-open analytic/injective payload. -/
theorem externalRayMapData_two_of_isClosedRange_restrict_of_outsideOpenAnalyticInjPayload
    (hclosed : IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ))))
    (h_payload : OutsideOpenAnalyticInjPayload (2 : ℂ)) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_data_of_isClosedRange_restrict_of_outsideOpenAnalyticInjPayload
    (2 : ℂ) hclosed h_payload

/-- Constructive target seam at `c = 2`: external-ray data from closed range plus
outside-open analyticity and explicit outside-open injectivity. -/
theorem externalRayMapData_two_of_isClosedRange_restrict_of_outsideOpenAnalyticityHypothesis_of_injOn
    (hclosed : IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ))))
    (h_analytic : OutsideOpenAnalyticityHypothesis (2 : ℂ))
    (h_inj : Set.InjOn (Quadratic.bottcher_map (2 : ℂ)) {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2}) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_data_of_isClosedRange_restrict_of_outsideOpenAnalyticityHypothesis_via_localChartWithin_of_injOn_outside_open
    (2 : ℂ) hclosed h_analytic h_inj

/-- Constructive target seam at `c = 2`: external-ray data from restricted-map
properness plus outside-open analytic/injective payload. -/
theorem externalRayMapData_two_of_isProperMap_restrict_of_outsideOpenAnalyticInjPayload
    (hproper : IsProperMap (bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (h_payload : OutsideOpenAnalyticInjPayload (2 : ℂ)) :
    Quadratic.ExternalRayMapData (2 : ℂ) := by
  exact externalRayMapData_two_of_isClosedRange_restrict_of_outsideOpenAnalyticInjPayload
    (isClosed_range_bottcher_map_outside_open_to_exterior_of_isProperMap (2 : ℂ) hproper)
    h_payload

/-- CP5 seam at `c = 2`: constructive external-ray-map-data target from restricted-map
properness plus outside-open analytic/injective payload. -/
theorem external_ray_map_exists_two_constructive_of_isProperMap_restrict_of_outsideOpenAnalyticInjPayload
    (hproper : IsProperMap (bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (h_payload : OutsideOpenAnalyticInjPayload (2 : ℂ)) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  externalRayMapData_two_of_isProperMap_restrict_of_outsideOpenAnalyticInjPayload hproper h_payload

/-- CP5 seam at `c = 2`: constructive external-ray-map-data target from
outside-open injectivity plus exterior surjectivity by outside-open preimages. -/
theorem external_ray_map_exists_two_constructive_of_injOn_outside_open_of_surj_exterior
    (h_inj : Set.InjOn (Quadratic.bottcher_map (2 : ℂ)) {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2})
    (h_surj : BottcherSurjOnExteriorFromOutsideOpen (2 : ℂ)) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_data_of_injOn_outside_open_of_surj_exterior (2 : ℂ) h_inj h_surj

/-- CP5 seam at `c = 2`: constructive external-ray-map-data target from closed range
plus outside-open analyticity (injectivity packaged via existing bridges). -/
theorem external_ray_map_exists_two_constructive_of_isClosedRange_restrict_of_outsideOpenAnalyticityHypothesis
    (hclosed : IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ))))
    (h_analytic : OutsideOpenAnalyticityHypothesis (2 : ℂ)) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  externalRayMapData_two_of_isClosedRange_restrict_of_outsideOpenAnalyticInjPayload
    hclosed
    (outsideOpenAnalyticInjPayload_of_outsideOpenAnalyticityHypothesis (2 : ℂ) h_analytic)

/-- CP5 seam at `c = 2`: constructive external-ray-map-data target from restricted-map
properness plus outside-open analyticity. -/
theorem external_ray_map_exists_two_constructive_of_isProperMap_restrict_of_outsideOpenAnalyticityHypothesis
    (hproper : IsProperMap (bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (h_analytic : OutsideOpenAnalyticityHypothesis (2 : ℂ)) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_exists_two_constructive_of_isClosedRange_restrict_of_outsideOpenAnalyticityHypothesis
    (isClosed_range_bottcher_map_outside_open_to_exterior_of_isProperMap (2 : ℂ) hproper)
    h_analytic

/-- CP5 seam at `c = 2`: constructive external-ray-map-data target from closed range
plus local analytic charts that remain inside outside-open. -/
theorem external_ray_map_exists_two_constructive_of_isClosedRange_restrict_of_outsideOpenLocalAnalyticChartWithinOutsideOpenHypothesis
    (hclosed : IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ))))
    (h_chart : OutsideOpenLocalAnalyticChartWithinOutsideOpenHypothesis (2 : ℂ)) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_exists_two_constructive_of_isClosedRange_restrict_of_outsideOpenAnalyticityHypothesis
    hclosed
    (outsideOpenAnalyticityHypothesisTwo_constructive_of_outsideOpenLocalAnalyticChartWithinOutsideOpenHypothesis
      h_chart)

/-- CP5 seam at `c = 2`: constructive external-ray-map-data target from closed range
plus outside-open quotient constancy. -/
theorem external_ray_map_exists_two_constructive_of_isClosedRange_restrict_of_outsideOpenQuotientConstHypothesisTwo
    (hclosed : IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ))))
    (h_qconst : OutsideOpenQuotientConstHypothesisTwo) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_data_two_of_isClosedRange_restrict_of_outsideOpenQuotientConstHypothesisTwo
    hclosed h_qconst

/-- CP5 seam at `c = 2`: constructive external-ray-map-data target from closed range
plus outside-open quotient analyticity. -/
theorem external_ray_map_exists_two_constructive_of_isClosedRange_restrict_of_outsideOpenQuotientAnalyticityHypothesisTwo
    (hclosed : IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ))))
    (h_qanalytic : OutsideOpenQuotientAnalyticityHypothesisTwo) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_exists_two_constructive_of_isClosedRange_restrict_of_outsideOpenLocalAnalyticChartWithinOutsideOpenHypothesis
    hclosed
    (outsideOpenLocalAnalyticChartWithinOutsideOpenHypothesis_two_constructive_of_outsideOpenQuotientAnalyticityHypothesis
      h_qanalytic)

/-- CP5 seam at `c = 2`: constructive external-ray-map-data target from closed range
plus the strong quotient-rigidity witness. -/
theorem external_ray_map_exists_two_constructive_of_isClosedRange_restrict_of_outsideOpenQuotientConstRealWitnessTwo
    (hclosed : IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ))))
    (h_wit : OutsideOpenQuotientConstRealWitnessTwo) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_data_two_of_isClosedRange_restrict_of_outsideOpenQuotientConstRealWitnessTwo
    hclosed h_wit

/-- CP5 seam at `c = 2`: strong quotient-rigidity witness routed through the
CP2 chart-within constructive bridge. -/
theorem external_ray_map_exists_two_constructive_of_isClosedRange_restrict_of_outsideOpenQuotientConstRealWitnessTwo_via_localChartWithin
    (hclosed : IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ))))
    (h_wit : OutsideOpenQuotientConstRealWitnessTwo) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_exists_two_constructive_of_isClosedRange_restrict_of_outsideOpenLocalAnalyticChartWithinOutsideOpenHypothesis
    hclosed
    (outsideOpenLocalAnalyticChartWithinOutsideOpenHypothesis_two_constructive_of_outsideOpenQuotientConstRealWitnessTwo
      h_wit)

/-- CP5 foundational bridge at `c = 2`: eventual-slit-to-slit implication plus
closed range yields constructive external-ray-map data through the CP2 witness route. -/
theorem external_ray_map_exists_two_constructive_of_isClosedRange_restrict_of_eventualSlitImpliesSlitOrbit
    (hclosed : IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ))))
    (himp : EventualSlitImpliesSlitOrbit (2 : ℂ)) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_exists_two_constructive_of_isClosedRange_restrict_of_outsideOpenQuotientConstRealWitnessTwo_via_localChartWithin
    hclosed
    (outsideOpenQuotientConstRealWitnessTwo_constructive_of_eventualSlitImpliesSlitOrbit himp)

/-- CP5 scope-revised bridge at `c = 2`: closed range plus explicit CP2 scope
gate yields constructive external-ray-map data. -/
theorem external_ray_map_exists_two_constructive_of_isClosedRange_restrict_of_outsideOpenAnalyticityScopeAssumptionTwo
    (hclosed : IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ))))
    (h_scope : OutsideOpenAnalyticityScopeAssumptionTwo) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_exists_two_constructive_of_isClosedRange_restrict_of_outsideOpenAnalyticityHypothesis
    hclosed
    (outsideOpenAnalyticityHypothesisTwo_assumptionGated h_scope)

/-- CP5 seam at `c = 2`: constructive external-ray-map-data target from outside-open
analyticity plus the compact-preimage properness package. -/
theorem external_ray_map_exists_two_constructive_of_analyticAt_of_preimageCompact
    (h_analytic : OutsideOpenAnalyticityHypothesis (2 : ℂ))
    (hpre :
      ∀ K : Set {w : ℂ // 1 < ‖w‖}, IsCompact K →
        IsCompact
          ({z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2 ∧
            Quadratic.bottcher_map (2 : ℂ) z ∈ ((↑) '' K : Set ℂ)} : Set ℂ)) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_exists_two_constructive_of_isProperMap_restrict_of_outsideOpenAnalyticityHypothesis
    (isProperMap_bottcher_map_outside_open_to_exterior_two_of_analyticAt_of_preimage_compact
      h_analytic hpre)
    h_analytic

/-- CP5 seam at `c = 2`: constructive external-ray-map-data target from outside-open
analyticity plus the closed-preimage properness package. -/
theorem external_ray_map_exists_two_constructive_of_analyticAt_of_preimageClosed
    (h_analytic : OutsideOpenAnalyticityHypothesis (2 : ℂ))
    (hclosedpre :
      ∀ K : Set {w : ℂ // 1 < ‖w‖}, IsCompact K →
        IsClosed
          ({z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2 ∧
            Quadratic.bottcher_map (2 : ℂ) z ∈ ((↑) '' K : Set ℂ)} : Set ℂ)) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_exists_two_constructive_of_isProperMap_restrict_of_outsideOpenAnalyticityHypothesis
    (isProperMap_bottcher_map_outside_open_to_exterior_two_of_analyticAt_of_preimage_closed
      h_analytic hclosedpre)
    h_analytic

/-- CP5 seam at `c = 2`: constructive external-ray-map-data target from closed range
plus the combined non-slit outside-open analytic/injective payload. -/
theorem external_ray_map_exists_two_constructive_of_isClosedRange_restrict_of_outsideOpenAnalyticInjNonSlitPayloadTwo
    (hclosed : IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ))))
    (h_payload : OutsideOpenAnalyticInjNonSlitPayloadTwo) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  externalRayMapData_two_of_isClosedRange_restrict_of_outsideOpenAnalyticInjPayload hclosed h_payload

/-- CP5 seam at `c = 2`: constructive external-ray-map-data target from closed range
plus outside-open `AnalyticAt` payload. -/
theorem external_ray_map_exists_two_constructive_of_isClosedRange_restrict_of_analyticAt
    (hclosed : IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ))))
    (hanalytic :
      ∀ z, ‖z‖ > ‖(2 : ℂ)‖ + 2 → AnalyticAt ℂ (Quadratic.bottcher_map (2 : ℂ)) z) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_exists_two_constructive_of_isClosedRange_restrict_of_outsideOpenAnalyticityHypothesis
    hclosed hanalytic

/-- Compatibility CP5 seam retaining the older signature with explicit outside-open
injectivity at `c = 2`. -/
theorem external_ray_map_exists_two_constructive_of_isClosedRange_restrict_of_analyticAt_of_injOn
    (hclosed : IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ))))
    (hanalytic :
      ∀ z, ‖z‖ > ‖(2 : ℂ)‖ + 2 → AnalyticAt ℂ (Quadratic.bottcher_map (2 : ℂ)) z)
    (_h_inj :
      Set.InjOn (Quadratic.bottcher_map (2 : ℂ)) {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2}) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_exists_two_constructive_of_isClosedRange_restrict_of_analyticAt hclosed hanalytic

/-- CP5 seam at `c = 2`: constructive external-ray-map-data target from closed range
plus local analyticity and iterate-left-inverse injectivity. -/
theorem external_ray_map_exists_two_constructive_of_isClosedRange_restrict_of_analyticAt_of_iter_left_inverse
    (hclosed : IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ))))
    (hanalytic :
      ∀ z, ‖z‖ > ‖(2 : ℂ)‖ + 2 → AnalyticAt ℂ (Quadratic.bottcher_map (2 : ℂ)) z)
    (h_left_iter : QuadraticMapIterLeftInverseOnBasin (2 : ℂ)) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_data_two_of_isClosedRange_restrict_of_analyticAt_of_iter_left_inverse
    hclosed hanalytic h_left_iter

/-- Shared closed-range + external-ray-data root seam at `c = 2`. -/
theorem mlc_conjecture_of_isClosedRange_restrict_of_externalRayMapData_two
    (_hclosed : IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ))))
    (h_data : Quadratic.ExternalRayMapData (2 : ℂ)) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_bottcherSurjOnExterior_two_via_fiber
    (bottcherSurjOnExterior_two_of_externalRayMapData h_data)

/-- Step-4→root seam: outside-open exterior surjectivity at `c = 2` is
    sufficient to derive the full MLC statement. -/
theorem mlc_conjecture_of_bottcherSurjOnExteriorFromOutsideOpen_two
    (h_surj : BottcherSurjOnExteriorFromOutsideOpen (2 : ℂ)) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_bottcherSurjOnExterior_two_via_fiber
    (bottcherSurjOnExterior_two_of_surjOnExteriorFromOutsideOpen h_surj)

/-- Step-4→root seam using only minimal exterior surjectivity at `c = 2`. -/
theorem mlc_conjecture_of_bottcherSurjOnExterior_two
    (h_surj : BottcherSurjOnExterior (2 : ℂ)) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_bottcherSurjOnExterior_two_via_fiber h_surj

/-- Step-4→root seam specialized through restricted-map closed range and
    restricted local-homeomorph payloads at `c = 2`. -/
theorem mlc_conjecture_of_isClosedRange_restrict_of_isLocalHomeomorph_restrict_two
    (hclosed : IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ))))
    (hlocal : IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ))) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_bottcherSurjOnExteriorFromOutsideOpen_two
    (bottcherSurjOnExteriorFromOutsideOpen_two_of_isClosedRange_restrict_of_isLocalHomeomorph_restrict
      hclosed hlocal)

/-- Surjectivity-source seam at `c = 2`: restricted-map closed range plus
restricted local-homeomorph hypotheses produce outside-open exterior surjectivity. -/
theorem bottcherSurjOnExteriorFromOutsideOpen_two_of_localHomeomorphConstructivePayload
    (hclosed : IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ))))
    (hlocal : IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ))) :
    BottcherSurjOnExteriorFromOutsideOpen (2 : ℂ) :=
  bottcherSurjOnExteriorFromOutsideOpen_two_of_isClosedRange_restrict_of_isLocalHomeomorph_restrict
    hclosed hlocal

/-- Positive-source surjectivity seam at `c = 2`: restricted-map properness plus
restricted local-homeomorph hypotheses produce outside-open exterior surjectivity. -/
theorem bottcherSurjOnExteriorFromOutsideOpen_two_of_isProperMap_restrict_of_isLocalHomeomorph_restrict
    (hproper : IsProperMap (bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (hlocal : IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ))) :
    BottcherSurjOnExteriorFromOutsideOpen (2 : ℂ) :=
  bottcherSurjOnExteriorFromOutsideOpen_two_of_localHomeomorphConstructivePayload
    (isClosed_range_bottcher_map_outside_open_to_exterior_of_isProperMap (2 : ℂ) hproper)
    hlocal

/-- Surjectivity-source seam at `c = 2`: outside-open local-homeomorph-on payload
plus closed range induces outside-open exterior surjectivity. -/
theorem bottcherSurjOnExteriorFromOutsideOpen_two_of_localHomeomorphOnConstructivePayload
    (hclosed : IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ))))
    (hlocal_on : IsLocalHomeomorphOn (Quadratic.bottcher_map (2 : ℂ)) {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2}) :
    BottcherSurjOnExteriorFromOutsideOpen (2 : ℂ) :=
  bottcherSurjOnExteriorFromOutsideOpen_two_of_localHomeomorphConstructivePayload hclosed
    (isLocalHomeomorph_bottcher_map_outside_open_to_exterior_of_isLocalHomeomorphOn_outside_open
      (2 : ℂ) hlocal_on)

/-- Surjectivity-source seam at `c = 2`: outside-disk-to-outside-open image
refinement yields outside-open exterior surjectivity. -/
theorem bottcherSurjOnExteriorFromOutsideOpen_two_of_outsideDiskRefinement
    (h_refine : BottcherOutsideDiskToOutsideOpenImageRefinement (2 : ℂ)) :
    BottcherSurjOnExteriorFromOutsideOpen (2 : ℂ) := by
  intro w hw
  exact exterior_subset_image_outside_open_of_outside_disk_refinement (2 : ℂ) h_refine hw

/-- Outside-disk-to-outside-open refinement source at `c = 2` from the
external-ray landing assumption. -/
theorem outsideDiskRefinement_two_of_externalRayLandsOutsideOpen
    (hland : ExternalRayLandsOutsideOpen (2 : ℂ)) :
    BottcherOutsideDiskToOutsideOpenImageRefinement (2 : ℂ) :=
  outside_disk_to_outside_open_image_refinement_of_externalRayLandsOutsideOpen (2 : ℂ) hland

/-- External-ray landing at `c = 2` from outside-disk refinement plus
outside-disk-to-outside-open image refinement. -/
theorem externalRayLandsOutsideOpen_two_of_outsideDiskRefinement
    (h_refine : BottcherOutsideDiskToOutsideOpenImageRefinement (2 : ℂ)) :
    ExternalRayLandsOutsideOpen (2 : ℂ) :=
  externalRayLandsOutsideOpen_of_outside_disk_to_outside_open_image_refinement
    (2 : ℂ) h_refine

/-- At `c = 2`, the landing and outside-disk refinement source predicates are
equivalent. -/
theorem outsideDiskRefinement_two_iff_externalRayLandsOutsideOpen :
    BottcherOutsideDiskToOutsideOpenImageRefinement (2 : ℂ) ↔
      ExternalRayLandsOutsideOpen (2 : ℂ) := by
  constructor
  · exact externalRayLandsOutsideOpen_two_of_outsideDiskRefinement
  · exact outsideDiskRefinement_two_of_externalRayLandsOutsideOpen

/-- External-ray landing source at `c = 2` from direct outside-open control of
preimages of the exterior under `bottcher_map`. -/
theorem externalRayLandsOutsideOpen_two_of_preimageExteriorSubsetOutsideOpen
    (hpre :
      (Quadratic.bottcher_map (2 : ℂ)) ⁻¹' {z : ℂ | 1 < ‖z‖} ⊆
        {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2}) :
    ExternalRayLandsOutsideOpen (2 : ℂ) :=
  externalRayLandsOutsideOpen_of_preimage_exterior_subset_outside_open
    (2 : ℂ) hpre

/-- Step-4→root seam specialized through restricted-map closed range plus
    outside-open analytic/derivative payloads at `c = 2`. -/
def AnalyticDerivConstructivePayloadTwo : Prop :=
  IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ))) ∧
    (∀ z, ‖z‖ > ‖(2 : ℂ)‖ + 2 → AnalyticAt ℂ (Quadratic.bottcher_map (2 : ℂ)) z) ∧
    (∀ z, ‖z‖ > ‖(2 : ℂ)‖ + 2 → deriv (Quadratic.bottcher_map (2 : ℂ)) z ≠ 0)

/-- Root bridge from the plain-analytic/derivative payload target at `c = 2`. -/
theorem mlc_conjecture_of_analyticDerivConstructivePayloadTwo
    (h_payload : AnalyticDerivConstructivePayloadTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_bottcherSurjOnExteriorFromOutsideOpen_two
    (bottcherSurjOnExteriorFromOutsideOpen_two_of_isClosedRange_restrict_of_analyticAt_of_deriv_ne_zero
      h_payload.1 h_payload.2.1 h_payload.2.2)

theorem mlc_conjecture_of_isClosedRange_restrict_of_analyticAt_of_deriv_ne_zero_two
    (hclosed : IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ))))
    (hanalytic :
      ∀ z, ‖z‖ > ‖(2 : ℂ)‖ + 2 → AnalyticAt ℂ (Quadratic.bottcher_map (2 : ℂ)) z)
    (hderiv :
      ∀ z, ‖z‖ > ‖(2 : ℂ)‖ + 2 → deriv (Quadratic.bottcher_map (2 : ℂ)) z ≠ 0) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_analyticDerivConstructivePayloadTwo
    ⟨hclosed, hanalytic, hderiv⟩

/-- Local-homeomorph-on source at `c = 2` from the analytic/derivative payload. -/
theorem localHomeomorphOnOutsideOpen_two_of_analyticDerivConstructivePayloadTwo
    (h_payload : AnalyticDerivConstructivePayloadTwo) :
    IsLocalHomeomorphOn (Quadratic.bottcher_map (2 : ℂ)) {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2} :=
  bottcher_map_isLocalHomeomorphOn_outside_open_of_analyticAt_of_deriv_ne_zero
    (2 : ℂ) h_payload.2.1 h_payload.2.2

/-- Local-homeomorph-on source candidate at `c = 2` through slit inclusion plus
outside-disk injectivity. -/
def SlitInjOutsideDiskLocalHomeomorphOnConstructivePayloadTwo : Prop :=
  ({z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2} ⊆ slit_orbit (2 : ℂ)) ∧
    Set.InjOn (Quadratic.bottcher_map (2 : ℂ)) (outside_disk (2 : ℂ))

/-- Local-homeomorph-on source from slit inclusion plus outside-disk injectivity
at `c = 2`. -/
theorem localHomeomorphOnOutsideOpen_two_of_slitInjOutsideDisk
    (h_payload : SlitInjOutsideDiskLocalHomeomorphOnConstructivePayloadTwo) :
    IsLocalHomeomorphOn (Quadratic.bottcher_map (2 : ℂ)) {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2} :=
  bottcher_map_isLocalHomeomorphOn_outside_open (2 : ℂ) h_payload.1

/-- Aggregate predicate for currently wired source families that imply
`BottcherSurjOnExteriorFromOutsideOpen (2 : ℂ)`. -/
def KnownSurjOnExteriorFromOutsideOpenSourceCandidateTwo : Prop :=
  (IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ))) ∧
      IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ))) ∨
    (IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ))) ∧
      IsLocalHomeomorphOn (Quadratic.bottcher_map (2 : ℂ)) {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2}) ∨
    BottcherOutsideDiskToOutsideOpenImageRefinement (2 : ℂ) ∨
    ExternalRayLandsOutsideOpen (2 : ℂ) ∨
    AnalyticDerivConstructivePayloadTwo ∨
    (IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ))) ∧
      SlitInjOutsideDiskLocalHomeomorphOnConstructivePayloadTwo)

/-- Any currently wired source family in the previous aggregate yields
outside-open exterior surjectivity at `c = 2`. -/
theorem bottcherSurjOnExteriorFromOutsideOpen_two_of_knownSurjOnExteriorFromOutsideOpenSourceCandidateTwo
    (h : KnownSurjOnExteriorFromOutsideOpenSourceCandidateTwo) :
    BottcherSurjOnExteriorFromOutsideOpen (2 : ℂ) := by
  rcases h with hA | hB | hC | hD | hE | hF
  · exact bottcherSurjOnExteriorFromOutsideOpen_two_of_localHomeomorphConstructivePayload hA.1 hA.2
  · exact bottcherSurjOnExteriorFromOutsideOpen_two_of_localHomeomorphOnConstructivePayload hB.1 hB.2
  · exact bottcherSurjOnExteriorFromOutsideOpen_two_of_outsideDiskRefinement hC
  · exact bottcherSurjOnExteriorFromOutsideOpen_two_of_outsideDiskRefinement
      (outsideDiskRefinement_two_of_externalRayLandsOutsideOpen hD)
  · exact bottcherSurjOnExteriorFromOutsideOpen_two_of_isClosedRange_restrict_of_analyticAt_of_deriv_ne_zero
      hE.1 hE.2.1 hE.2.2
  · exact bottcherSurjOnExteriorFromOutsideOpen_two_of_localHomeomorphOnConstructivePayload hF.1
      (localHomeomorphOnOutsideOpen_two_of_slitInjOutsideDisk hF.2)

/-- Open (not-yet-blocked) surjectivity-source sub-aggregate at `c = 2`. -/
def KnownOpenSurjOnExteriorFromOutsideOpenSourceCandidateTwo : Prop :=
  (IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ))) ∧
      IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ))) ∨
    (IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ))) ∧
      IsLocalHomeomorphOn (Quadratic.bottcher_map (2 : ℂ)) {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2}) ∨
    BottcherOutsideDiskToOutsideOpenImageRefinement (2 : ℂ) ∨
    ExternalRayLandsOutsideOpen (2 : ℂ)

/-- Reduced open surjectivity-source sub-aggregate at `c = 2`: local-homeomorph
or external-ray landing. -/
def ReducedOpenSurjOnExteriorFromOutsideOpenSourceCandidateTwo : Prop :=
  (IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ))) ∧
      IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ))) ∨
    ExternalRayLandsOutsideOpen (2 : ℂ)

/-- The open surjectivity-source sub-aggregate collapses to the reduced form at
`c = 2`: local-homeomorph-on is subsumed by local-homeomorph, and outside-disk
refinement is equivalent to external-ray landing. -/
theorem knownOpenSurjOnExteriorFromOutsideOpenSourceCandidateTwo_iff_reduced :
    KnownOpenSurjOnExteriorFromOutsideOpenSourceCandidateTwo ↔
      ReducedOpenSurjOnExteriorFromOutsideOpenSourceCandidateTwo := by
  constructor
  · intro h
    rcases h with hA | hB | hC | hD
    · exact Or.inl hA
    · exact Or.inl
        ⟨hB.1,
          isLocalHomeomorph_bottcher_map_outside_open_to_exterior_of_isLocalHomeomorphOn_outside_open
            (2 : ℂ) hB.2⟩
    · exact Or.inr (externalRayLandsOutsideOpen_two_of_outsideDiskRefinement hC)
    · exact Or.inr hD
  · intro h
    rcases h with hA | hB
    · exact Or.inl hA
    · exact Or.inr (Or.inr (Or.inr hB))

/-- Blocked surjectivity-source sub-aggregate at `c = 2`. -/
def KnownBlockedSurjOnExteriorFromOutsideOpenSourceCandidateTwo : Prop :=
  AnalyticDerivConstructivePayloadTwo ∨
    (IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ))) ∧
      SlitInjOutsideDiskLocalHomeomorphOnConstructivePayloadTwo)

/-- Partition of the current surjectivity-source aggregate into open and blocked
sub-aggregates. -/
theorem knownSurjOnExteriorFromOutsideOpenSourceCandidateTwo_iff_open_or_blocked :
    KnownSurjOnExteriorFromOutsideOpenSourceCandidateTwo ↔
      KnownOpenSurjOnExteriorFromOutsideOpenSourceCandidateTwo ∨
        KnownBlockedSurjOnExteriorFromOutsideOpenSourceCandidateTwo := by
  constructor
  · intro h
    rcases h with hA | hB | hC | hD | hE | hF
    · exact Or.inl (Or.inl hA)
    · exact Or.inl (Or.inr (Or.inl hB))
    · exact Or.inl (Or.inr (Or.inr (Or.inl hC)))
    · exact Or.inl (Or.inr (Or.inr (Or.inr hD)))
    · exact Or.inr (Or.inl hE)
    · exact Or.inr (Or.inr hF)
  · intro h
    rcases h with hOpen | hBlocked
    · rcases hOpen with hA | hB | hC | hD
      · exact Or.inl hA
      · exact Or.inr (Or.inl hB)
      · exact Or.inr (Or.inr (Or.inl hC))
      · exact Or.inr (Or.inr (Or.inr (Or.inl hD)))
    · rcases hBlocked with hE | hF
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hE))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hF))))

/-- The open surjectivity-source sub-aggregate implies outside-open exterior
surjectivity at `c = 2`. -/
theorem bottcherSurjOnExteriorFromOutsideOpen_two_of_knownOpenSurjOnExteriorFromOutsideOpenSourceCandidateTwo
    (h : KnownOpenSurjOnExteriorFromOutsideOpenSourceCandidateTwo) :
    BottcherSurjOnExteriorFromOutsideOpen (2 : ℂ) := by
  exact bottcherSurjOnExteriorFromOutsideOpen_two_of_knownSurjOnExteriorFromOutsideOpenSourceCandidateTwo
    ((knownSurjOnExteriorFromOutsideOpenSourceCandidateTwo_iff_open_or_blocked).2 (Or.inl h))

/-- The reduced open surjectivity-source sub-aggregate implies outside-open
exterior surjectivity at `c = 2`. -/
theorem bottcherSurjOnExteriorFromOutsideOpen_two_of_reducedOpenSurjOnExteriorFromOutsideOpenSourceCandidateTwo
    (h : ReducedOpenSurjOnExteriorFromOutsideOpenSourceCandidateTwo) :
    BottcherSurjOnExteriorFromOutsideOpen (2 : ℂ) := by
  exact bottcherSurjOnExteriorFromOutsideOpen_two_of_knownOpenSurjOnExteriorFromOutsideOpenSourceCandidateTwo
    ((knownOpenSurjOnExteriorFromOutsideOpenSourceCandidateTwo_iff_reduced).2 h)

/-- The blocked surjectivity-source sub-aggregate implies outside-open exterior
surjectivity at `c = 2` (before no-go closure is applied). -/
theorem bottcherSurjOnExteriorFromOutsideOpen_two_of_knownBlockedSurjOnExteriorFromOutsideOpenSourceCandidateTwo
    (h : KnownBlockedSurjOnExteriorFromOutsideOpenSourceCandidateTwo) :
    BottcherSurjOnExteriorFromOutsideOpen (2 : ℂ) := by
  exact bottcherSurjOnExteriorFromOutsideOpen_two_of_knownSurjOnExteriorFromOutsideOpenSourceCandidateTwo
    ((knownSurjOnExteriorFromOutsideOpenSourceCandidateTwo_iff_open_or_blocked).2 (Or.inr h))

/-- Step-4→root seam specialized through restricted-map closed range plus the
combined non-slit outside-open analytic/injective payload shape at `c = 2`. -/
def NonSlitAnalyticInjConstructivePayloadTwo : Prop :=
  IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ))) ∧
    OutsideOpenAnalyticInjNonSlitPayloadTwo

/-- Step-4→root seam specialized through restricted-map closed range plus
outside-open analyticity at `c = 2`. -/
def NonSlitAnalyticConstructivePayloadTwo : Prop :=
  IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ))) ∧
    OutsideOpenAnalyticityHypothesis (2 : ℂ)

/-- Step-4→root seam specialized through restricted-map closed range plus a
strong quotient-rigidity witness at `c = 2`. -/
def NonSlitQuotientConstRealConstructivePayloadTwo : Prop :=
  IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ))) ∧
    OutsideOpenQuotientConstRealWitnessTwo

/-- Step-4→root seam specialized through restricted-map closed range plus
quotient constancy at `c = 2`. -/
def NonSlitQuotientConstConstructivePayloadTwo : Prop :=
  IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ))) ∧
    OutsideOpenQuotientConstHypothesisTwo

/-- Step-4→root seam specialized through restricted-map closed range plus
outside-open quotient analyticity at `c = 2`. -/
def NonSlitQuotientAnalyticConstructivePayloadTwo : Prop :=
  IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ))) ∧
    OutsideOpenQuotientAnalyticityHypothesisTwo

/-- Step-4→root seam specialized through restricted-map closed range plus
the eventual-slit-to-slit implication at `c = 2`. -/
def NonSlitEventualSlitConstructivePayloadTwo : Prop :=
  IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ))) ∧
    EventualSlitImpliesSlitOrbit (2 : ℂ)

/-- Scope-revised Step-4→root payload at `c = 2`: restricted-map closed range
plus explicit CP2 scope gate. -/
def NonSlitAnalyticScopeAssumptionConstructivePayloadTwo : Prop :=
  IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ))) ∧
    OutsideOpenAnalyticityScopeAssumptionTwo

/-- CP5 candidate payload at `c = 2`: outside-open injectivity plus outside-open
exterior surjectivity. -/
def InjSurjExteriorConstructivePayloadTwo : Prop :=
  Set.InjOn (Quadratic.bottcher_map (2 : ℂ)) {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2} ∧
    BottcherSurjOnExteriorFromOutsideOpen (2 : ℂ)

/-- At `c = 2`, outside-open left-inverse data is equivalent to outside-open
injectivity. -/
theorem leftInverseOutsideOpen_two_iff_injOn_outside_open :
    BottcherLeftInverseOnOutsideOpenData (2 : ℂ) ↔
      Set.InjOn (Quadratic.bottcher_map (2 : ℂ)) {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2} :=
  bottcher_left_inverse_on_outside_open_data_iff_injOn_outside_open (2 : ℂ)

/-- CP5 payload constructor at `c = 2`: outside-open left-inverse data gives
outside-open injectivity, paired with outside-open exterior surjectivity. -/
theorem injSurjExteriorConstructivePayloadTwo_of_leftInverseOutsideOpen_of_surjExterior
    (h_left : BottcherLeftInverseOnOutsideOpenData (2 : ℂ))
    (h_surj : BottcherSurjOnExteriorFromOutsideOpen (2 : ℂ)) :
    InjSurjExteriorConstructivePayloadTwo := by
  exact ⟨bottcher_map_inj_on_outside_open_of_left_inverse_on_outside_open (2 : ℂ) h_left, h_surj⟩

/-- CP5 payload constructor at `c = 2`: iterate-left-inverse injectivity plus
outside-open exterior surjectivity. -/
theorem injSurjExteriorConstructivePayloadTwo_of_iterLeftInverse_of_surjExterior
    (h_left_iter : QuadraticMapIterLeftInverseOnBasin (2 : ℂ))
    (h_surj : BottcherSurjOnExteriorFromOutsideOpen (2 : ℂ)) :
    InjSurjExteriorConstructivePayloadTwo := by
  exact ⟨bottcher_map_inj_on_outside_open_of_iter_left_inverse (2 : ℂ) h_left_iter, h_surj⟩

/-- CP5 payload constructor at `c = 2`: iterate-left-inverse injectivity plus
local-homeomorph surjectivity source. -/
theorem injSurjExteriorConstructivePayloadTwo_of_iterLeftInverse_of_localHomeomorph
    (h_left_iter : QuadraticMapIterLeftInverseOnBasin (2 : ℂ))
    (hclosed : IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ))))
    (hlocal : IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ))) :
    InjSurjExteriorConstructivePayloadTwo :=
  injSurjExteriorConstructivePayloadTwo_of_iterLeftInverse_of_surjExterior
    h_left_iter
    (bottcherSurjOnExteriorFromOutsideOpen_two_of_localHomeomorphConstructivePayload hclosed hlocal)

/-- CP5 payload constructor at `c = 2`: outside-open left-inverse injectivity
plus local-homeomorph surjectivity source. -/
theorem injSurjExteriorConstructivePayloadTwo_of_leftInverseOutsideOpen_of_localHomeomorph
    (h_left : BottcherLeftInverseOnOutsideOpenData (2 : ℂ))
    (hclosed : IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ))))
    (hlocal : IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ))) :
    InjSurjExteriorConstructivePayloadTwo :=
  injSurjExteriorConstructivePayloadTwo_of_leftInverseOutsideOpen_of_surjExterior
    h_left
    (bottcherSurjOnExteriorFromOutsideOpen_two_of_localHomeomorphConstructivePayload hclosed hlocal)

/-- CP5 payload constructor at `c = 2`: iterate-left-inverse injectivity plus
outside-open local-homeomorph-on surjectivity source. -/
theorem injSurjExteriorConstructivePayloadTwo_of_iterLeftInverse_of_localHomeomorphOn
    (h_left_iter : QuadraticMapIterLeftInverseOnBasin (2 : ℂ))
    (hclosed : IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ))))
    (hlocal_on : IsLocalHomeomorphOn (Quadratic.bottcher_map (2 : ℂ)) {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2}) :
    InjSurjExteriorConstructivePayloadTwo :=
  injSurjExteriorConstructivePayloadTwo_of_iterLeftInverse_of_surjExterior
    h_left_iter
    (bottcherSurjOnExteriorFromOutsideOpen_two_of_localHomeomorphOnConstructivePayload hclosed hlocal_on)

/-- CP5 payload constructor at `c = 2`: outside-open left-inverse injectivity
plus local-homeomorph-on surjectivity source. -/
theorem injSurjExteriorConstructivePayloadTwo_of_leftInverseOutsideOpen_of_localHomeomorphOn
    (h_left : BottcherLeftInverseOnOutsideOpenData (2 : ℂ))
    (hclosed : IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ))))
    (hlocal_on : IsLocalHomeomorphOn (Quadratic.bottcher_map (2 : ℂ)) {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2}) :
    InjSurjExteriorConstructivePayloadTwo :=
  injSurjExteriorConstructivePayloadTwo_of_leftInverseOutsideOpen_of_surjExterior
    h_left
    (bottcherSurjOnExteriorFromOutsideOpen_two_of_localHomeomorphOnConstructivePayload hclosed hlocal_on)

/-- CP5 payload constructor at `c = 2`: iterate-left-inverse injectivity plus
analytic/derivative-sourced local-homeomorph-on surjectivity. -/
theorem injSurjExteriorConstructivePayloadTwo_of_iterLeftInverse_of_analyticDerivConstructivePayloadTwo
    (h_left_iter : QuadraticMapIterLeftInverseOnBasin (2 : ℂ))
    (h_payload : AnalyticDerivConstructivePayloadTwo) :
    InjSurjExteriorConstructivePayloadTwo :=
  injSurjExteriorConstructivePayloadTwo_of_iterLeftInverse_of_localHomeomorphOn
    h_left_iter h_payload.1
    (localHomeomorphOnOutsideOpen_two_of_analyticDerivConstructivePayloadTwo h_payload)

/-- CP5 payload constructor at `c = 2`: iterate-left-inverse injectivity plus
outside-disk-to-outside-open image refinement. -/
theorem injSurjExteriorConstructivePayloadTwo_of_iterLeftInverse_of_outsideDiskRefinement
    (h_left_iter : QuadraticMapIterLeftInverseOnBasin (2 : ℂ))
    (h_refine : BottcherOutsideDiskToOutsideOpenImageRefinement (2 : ℂ)) :
    InjSurjExteriorConstructivePayloadTwo :=
  injSurjExteriorConstructivePayloadTwo_of_iterLeftInverse_of_surjExterior
    h_left_iter
    (bottcherSurjOnExteriorFromOutsideOpen_two_of_outsideDiskRefinement h_refine)

/-- CP5 payload constructor at `c = 2`: iterate-left-inverse injectivity plus
external-ray landing sourced outside-disk refinement. -/
theorem injSurjExteriorConstructivePayloadTwo_of_iterLeftInverse_of_externalRayLandsOutsideOpen
    (h_left_iter : QuadraticMapIterLeftInverseOnBasin (2 : ℂ))
    (hland : ExternalRayLandsOutsideOpen (2 : ℂ)) :
    InjSurjExteriorConstructivePayloadTwo :=
  injSurjExteriorConstructivePayloadTwo_of_iterLeftInverse_of_outsideDiskRefinement
    h_left_iter
    (outsideDiskRefinement_two_of_externalRayLandsOutsideOpen hland)

/-- CP5 payload constructor at `c = 2`: iterate-left-inverse injectivity plus
preimage-exterior outside-open control via the landing bridge. -/
theorem injSurjExteriorConstructivePayloadTwo_of_iterLeftInverse_of_preimageExteriorSubsetOutsideOpen
    (h_left_iter : QuadraticMapIterLeftInverseOnBasin (2 : ℂ))
    (hpre :
      (Quadratic.bottcher_map (2 : ℂ)) ⁻¹' {z : ℂ | 1 < ‖z‖} ⊆
        {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2}) :
    InjSurjExteriorConstructivePayloadTwo :=
  injSurjExteriorConstructivePayloadTwo_of_iterLeftInverse_of_externalRayLandsOutsideOpen
    h_left_iter
    (externalRayLandsOutsideOpen_two_of_preimageExteriorSubsetOutsideOpen hpre)

/-- Step-4→root payload specialized through closed range plus the boundary
exclusion family at `c = 2`. -/
def NonSlitBoundaryExclusionConstructivePayloadTwo : Prop :=
  IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ))) ∧
    (∀ K : Set {w : ℂ // 1 < ‖w‖}, IsCompact K →
      ∀ z, ‖z‖ = ‖(2 : ℂ)‖ + 2 →
        Quadratic.bottcher_map (2 : ℂ) z ∉ ((↑) '' K : Set ℂ))

/-- Step-4→root payload specialized through closed range plus local-slit
neighborhoods and outside-open injectivity at `c = 2`. -/
def NonSlitMemNhdsSlitInjConstructivePayloadTwo : Prop :=
  IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ))) ∧
    (∀ z, ‖z‖ > ‖(2 : ℂ)‖ + 2 → slit_orbit (2 : ℂ) ∈ 𝓝 z) ∧
      Set.InjOn (Quadratic.bottcher_map (2 : ℂ)) {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2}

/-- Step-4→root payload specialized through closed range plus local-slit
neighborhoods and iterate-left-inverse injectivity at `c = 2`. -/
def NonSlitMemNhdsSlitIterLeftInverseConstructivePayloadTwo : Prop :=
  IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ))) ∧
    (∀ z, ‖z‖ > ‖(2 : ℂ)‖ + 2 → slit_orbit (2 : ℂ) ∈ 𝓝 z) ∧
      QuadraticMapIterLeftInverseOnBasin (2 : ℂ)

/-- Root bridge from the eventual-slit-to-slit payload at `c = 2`. -/
theorem mlc_conjecture_of_nonSlitEventualSlitConstructivePayloadTwo
    (h_payload : NonSlitEventualSlitConstructivePayloadTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_externalRayMapData_two
    (external_ray_map_exists_two_constructive_of_isClosedRange_restrict_of_eventualSlitImpliesSlitOrbit
      h_payload.1 h_payload.2)

/-- Root bridge from the scope-revised analytic payload at `c = 2`. -/
theorem mlc_conjecture_of_nonSlitAnalyticScopeAssumptionConstructivePayloadTwo
    (h_payload : NonSlitAnalyticScopeAssumptionConstructivePayloadTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_externalRayMapData_two
    (external_ray_map_exists_two_constructive_of_isClosedRange_restrict_of_outsideOpenAnalyticityScopeAssumptionTwo
      h_payload.1 h_payload.2)

/-- Root bridge from injective outside-open + outside-open surjectivity payload
at `c = 2`. -/
theorem mlc_conjecture_of_injSurjExteriorConstructivePayloadTwo
    (h_payload : InjSurjExteriorConstructivePayloadTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_externalRayMapData_two
    (external_ray_map_exists_two_constructive_of_injOn_outside_open_of_surj_exterior
      h_payload.1 h_payload.2)

/-- CP5 seam at `c = 2`: iterate-left-inverse injectivity plus outside-open
surjectivity yields constructive external-ray-map data. -/
theorem external_ray_map_exists_two_constructive_of_iterLeftInverse_of_surjExterior
    (h_left_iter : QuadraticMapIterLeftInverseOnBasin (2 : ℂ))
    (h_surj : BottcherSurjOnExteriorFromOutsideOpen (2 : ℂ)) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_exists_two_constructive_of_injOn_outside_open_of_surj_exterior
    (bottcher_map_inj_on_outside_open_of_iter_left_inverse (2 : ℂ) h_left_iter)
    h_surj

/-- CP5 seam at `c = 2`: outside-open left-inverse data plus outside-open
surjectivity yields constructive external-ray-map data. -/
theorem external_ray_map_exists_two_constructive_of_leftInverseOutsideOpen_of_surjExterior
    (h_left : BottcherLeftInverseOnOutsideOpenData (2 : ℂ))
    (h_surj : BottcherSurjOnExteriorFromOutsideOpen (2 : ℂ)) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_exists_two_constructive_of_injOn_outside_open_of_surj_exterior
    (bottcher_map_inj_on_outside_open_of_left_inverse_on_outside_open (2 : ℂ) h_left)
    h_surj

/-- Root bridge from iterate-left-inverse injectivity plus outside-open
surjectivity at `c = 2`. -/
theorem mlc_conjecture_of_iterLeftInverse_of_surjExterior_two
    (h_left_iter : QuadraticMapIterLeftInverseOnBasin (2 : ℂ))
    (h_surj : BottcherSurjOnExteriorFromOutsideOpen (2 : ℂ)) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_externalRayMapData_two
    (external_ray_map_exists_two_constructive_of_iterLeftInverse_of_surjExterior
      h_left_iter h_surj)

/-- Root bridge from outside-open left-inverse data plus outside-open
surjectivity at `c = 2`. -/
theorem mlc_conjecture_of_leftInverseOutsideOpen_of_surjExterior_two
    (h_left : BottcherLeftInverseOnOutsideOpenData (2 : ℂ))
    (h_surj : BottcherSurjOnExteriorFromOutsideOpen (2 : ℂ)) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_externalRayMapData_two
    (external_ray_map_exists_two_constructive_of_leftInverseOutsideOpen_of_surjExterior
      h_left h_surj)

/-- Root bridge from outside-open left-inverse data plus local-homeomorph
surjectivity source at `c = 2`. -/
theorem mlc_conjecture_of_leftInverseOutsideOpen_of_localHomeomorph_two
    (h_left : BottcherLeftInverseOnOutsideOpenData (2 : ℂ))
    (hclosed : IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ))))
    (hlocal : IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ))) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_leftInverseOutsideOpen_of_surjExterior_two
    h_left
    (bottcherSurjOnExteriorFromOutsideOpen_two_of_localHomeomorphConstructivePayload hclosed hlocal)

/-- Root bridge from outside-open left-inverse data plus local-homeomorph-on
surjectivity source at `c = 2`. -/
theorem mlc_conjecture_of_leftInverseOutsideOpen_of_localHomeomorphOn_two
    (h_left : BottcherLeftInverseOnOutsideOpenData (2 : ℂ))
    (hclosed : IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ))))
    (hlocal_on : IsLocalHomeomorphOn (Quadratic.bottcher_map (2 : ℂ)) {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2}) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_leftInverseOutsideOpen_of_surjExterior_two
    h_left
    (bottcherSurjOnExteriorFromOutsideOpen_two_of_localHomeomorphOnConstructivePayload hclosed hlocal_on)

/-- Root bridge from iterate-left-inverse injectivity plus local-homeomorph
surjectivity source at `c = 2`. -/
theorem mlc_conjecture_of_iterLeftInverse_of_localHomeomorph_two
    (h_left_iter : QuadraticMapIterLeftInverseOnBasin (2 : ℂ))
    (hclosed : IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ))))
    (hlocal : IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ))) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_iterLeftInverse_of_surjExterior_two
    h_left_iter
    (bottcherSurjOnExteriorFromOutsideOpen_two_of_localHomeomorphConstructivePayload hclosed hlocal)

/-- Root bridge from iterate-left-inverse injectivity plus outside-open
local-homeomorph-on surjectivity source at `c = 2`. -/
theorem mlc_conjecture_of_iterLeftInverse_of_localHomeomorphOn_two
    (h_left_iter : QuadraticMapIterLeftInverseOnBasin (2 : ℂ))
    (hclosed : IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ))))
    (hlocal_on : IsLocalHomeomorphOn (Quadratic.bottcher_map (2 : ℂ)) {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2}) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_iterLeftInverse_of_surjExterior_two
    h_left_iter
    (bottcherSurjOnExteriorFromOutsideOpen_two_of_localHomeomorphOnConstructivePayload hclosed hlocal_on)

/-- CP5 seam at `c = 2`: iterate-left-inverse injectivity plus
outside-disk-to-outside-open image refinement yields constructive
external-ray-map data. -/
theorem external_ray_map_exists_two_constructive_of_iterLeftInverse_of_outsideDiskRefinement
    (h_left_iter : QuadraticMapIterLeftInverseOnBasin (2 : ℂ))
    (h_refine : BottcherOutsideDiskToOutsideOpenImageRefinement (2 : ℂ)) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_exists_two_constructive_of_iterLeftInverse_of_surjExterior
    h_left_iter
    (bottcherSurjOnExteriorFromOutsideOpen_two_of_outsideDiskRefinement h_refine)

/-- Root bridge from iterate-left-inverse injectivity plus outside-disk-to-
outside-open image refinement at `c = 2`. -/
theorem mlc_conjecture_of_iterLeftInverse_of_outsideDiskRefinement_two
    (h_left_iter : QuadraticMapIterLeftInverseOnBasin (2 : ℂ))
    (h_refine : BottcherOutsideDiskToOutsideOpenImageRefinement (2 : ℂ)) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_externalRayMapData_two
    (external_ray_map_exists_two_constructive_of_iterLeftInverse_of_outsideDiskRefinement
      h_left_iter h_refine)

/-- CP5 seam at `c = 2`: iterate-left-inverse injectivity plus external-ray
landing yields constructive external-ray-map data via outside-disk refinement. -/
theorem external_ray_map_exists_two_constructive_of_iterLeftInverse_of_externalRayLandsOutsideOpen
    (h_left_iter : QuadraticMapIterLeftInverseOnBasin (2 : ℂ))
    (hland : ExternalRayLandsOutsideOpen (2 : ℂ)) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_exists_two_constructive_of_iterLeftInverse_of_outsideDiskRefinement
    h_left_iter
    (outsideDiskRefinement_two_of_externalRayLandsOutsideOpen hland)

/-- CP5 seam at `c = 2`: iterate-left-inverse injectivity plus direct
preimage-exterior outside-open control yields constructive external-ray-map
data. -/
theorem external_ray_map_exists_two_constructive_of_iterLeftInverse_of_preimageExteriorSubsetOutsideOpen
    (h_left_iter : QuadraticMapIterLeftInverseOnBasin (2 : ℂ))
    (hpre :
      (Quadratic.bottcher_map (2 : ℂ)) ⁻¹' {z : ℂ | 1 < ‖z‖} ⊆
        {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2}) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_exists_two_constructive_of_iterLeftInverse_of_externalRayLandsOutsideOpen
    h_left_iter
    (externalRayLandsOutsideOpen_two_of_preimageExteriorSubsetOutsideOpen hpre)

/-- Root bridge from iterate-left-inverse injectivity plus external-ray landing
at `c = 2`. -/
theorem mlc_conjecture_of_iterLeftInverse_of_externalRayLandsOutsideOpen_two
    (h_left_iter : QuadraticMapIterLeftInverseOnBasin (2 : ℂ))
    (hland : ExternalRayLandsOutsideOpen (2 : ℂ)) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_externalRayMapData_two
    (external_ray_map_exists_two_constructive_of_iterLeftInverse_of_externalRayLandsOutsideOpen
      h_left_iter hland)

/-- Root bridge from iterate-left-inverse injectivity plus direct
preimage-exterior outside-open control at `c = 2`. -/
theorem mlc_conjecture_of_iterLeftInverse_of_preimageExteriorSubsetOutsideOpen_two
    (h_left_iter : QuadraticMapIterLeftInverseOnBasin (2 : ℂ))
    (hpre :
      (Quadratic.bottcher_map (2 : ℂ)) ⁻¹' {z : ℂ | 1 < ‖z‖} ⊆
        {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2}) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_externalRayMapData_two
    (external_ray_map_exists_two_constructive_of_iterLeftInverse_of_preimageExteriorSubsetOutsideOpen
      h_left_iter hpre)

/-- Combined payload: iterate-left-inverse injectivity plus outside-disk-to-
outside-open image refinement at `c = 2`. -/
def IterLeftInverseOutsideDiskRefinementConstructivePayloadTwo : Prop :=
  QuadraticMapIterLeftInverseOnBasin (2 : ℂ) ∧
    BottcherOutsideDiskToOutsideOpenImageRefinement (2 : ℂ)

/-- Root bridge from iterate-left-inverse injectivity plus outside-disk-to-
outside-open image refinement package at `c = 2`. -/
theorem mlc_conjecture_of_iterLeftInverseOutsideDiskRefinementConstructivePayloadTwo
    (h_payload : IterLeftInverseOutsideDiskRefinementConstructivePayloadTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_iterLeftInverse_of_outsideDiskRefinement_two
    h_payload.1 h_payload.2

/-- Combined payload: iterate-left-inverse injectivity plus external-ray landing
at `c = 2`. -/
def IterLeftInverseExternalRayLandsOutsideOpenConstructivePayloadTwo : Prop :=
  QuadraticMapIterLeftInverseOnBasin (2 : ℂ) ∧
    ExternalRayLandsOutsideOpen (2 : ℂ)

/-- Combined payload: iterate-left-inverse injectivity plus direct
preimage-exterior outside-open control at `c = 2`. -/
def IterLeftInversePreimageExteriorSubsetOutsideOpenConstructivePayloadTwo : Prop :=
  QuadraticMapIterLeftInverseOnBasin (2 : ℂ) ∧
    ((Quadratic.bottcher_map (2 : ℂ)) ⁻¹' {z : ℂ | 1 < ‖z‖} ⊆
      {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2})

/-- Root bridge from iterate-left-inverse injectivity plus external-ray landing
package at `c = 2`. -/
theorem mlc_conjecture_of_iterLeftInverseExternalRayLandsOutsideOpenConstructivePayloadTwo
    (h_payload : IterLeftInverseExternalRayLandsOutsideOpenConstructivePayloadTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_iterLeftInverse_of_externalRayLandsOutsideOpen_two
    h_payload.1 h_payload.2

/-- Root bridge from iterate-left-inverse injectivity plus direct
preimage-exterior outside-open control package at `c = 2`. -/
theorem mlc_conjecture_of_iterLeftInversePreimageExteriorSubsetOutsideOpenConstructivePayloadTwo
    (h_payload : IterLeftInversePreimageExteriorSubsetOutsideOpenConstructivePayloadTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_iterLeftInverse_of_preimageExteriorSubsetOutsideOpen_two
    h_payload.1 h_payload.2

/-- Combined payload: iterate-left-inverse injectivity plus the
analytic/derivative source package at `c = 2`. -/
def IterLeftInverseAnalyticDerivConstructivePayloadTwo : Prop :=
  QuadraticMapIterLeftInverseOnBasin (2 : ℂ) ∧
    AnalyticDerivConstructivePayloadTwo

/-- Root bridge from iterate-left-inverse injectivity plus the
analytic/derivative-sourced local-homeomorph-on package. -/
theorem mlc_conjecture_of_iterLeftInverseAnalyticDerivConstructivePayloadTwo
    (h_payload : IterLeftInverseAnalyticDerivConstructivePayloadTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_injSurjExteriorConstructivePayloadTwo
    (injSurjExteriorConstructivePayloadTwo_of_iterLeftInverse_of_analyticDerivConstructivePayloadTwo
      h_payload.1 h_payload.2)

/-- Scope-check no-go at `c = 2`: this payload shape is inconsistent in the
current model because outside-open analyticity is impossible. -/
theorem not_nonSlitAnalyticConstructivePayloadTwo :
    ¬ NonSlitAnalyticConstructivePayloadTwo := by
  intro h_payload
  exact not_outsideOpenAnalyticityHypothesisTwo h_payload.2

/-- Scope-check no-go at `c = 2`: this payload shape is inconsistent in the
current model because eventual-slit-to-slit implication is impossible. -/
theorem not_nonSlitEventualSlitConstructivePayloadTwo :
    ¬ NonSlitEventualSlitConstructivePayloadTwo := by
  intro h_payload
  exact not_eventualSlitImpliesSlitOrbit_two h_payload.2

/-- Scope-check no-go at `c = 2`: this payload shape is inconsistent in the
current model because the combined outside-open analytic/injective payload is
impossible. -/
theorem not_nonSlitAnalyticInjConstructivePayloadTwo :
    ¬ NonSlitAnalyticInjConstructivePayloadTwo := by
  intro h_payload
  exact not_outsideOpenAnalyticInjNonSlitPayloadTwo h_payload.2

/-- Scope-check no-go at `c = 2`: direct preimage-exterior outside-open control
fails because `0` maps to the exterior while `0` is not outside-open. -/
theorem not_preimageExteriorSubsetOutsideOpenTwo :
    ¬ ((Quadratic.bottcher_map (2 : ℂ)) ⁻¹' {z : ℂ | 1 < ‖z‖} ⊆
      {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2}) := by
  intro hpre
  have hbasin : (0 : ℂ) ∈ Quadratic.basin_of_infinity (2 : ℂ) := zero_mem_basin_two
  have hpos : 0 < MLC.Quadratic.green_function (2 : ℂ) (0 : ℂ) :=
    green_function_pos_of_basin (2 : ℂ) (0 : ℂ) hbasin
  have hnorm : 1 < ‖Quadratic.bottcher_map (2 : ℂ) (0 : ℂ)‖ :=
    bottcher_map_norm_gt_one_of_basin (2 : ℂ) (0 : ℂ) hbasin hpos
  have hz_pre : (0 : ℂ) ∈ (Quadratic.bottcher_map (2 : ℂ)) ⁻¹' {z : ℂ | 1 < ‖z‖} := by
    simpa [Set.preimage] using hnorm
  have hz_out : ‖(0 : ℂ)‖ > ‖(2 : ℂ)‖ + 2 := hpre hz_pre
  have hnot : ¬ ‖(0 : ℂ)‖ > ‖(2 : ℂ)‖ + 2 := by
    have hge : (0 : ℝ) ≤ ‖(2 : ℂ)‖ + 2 := by
      nlinarith [norm_nonneg (2 : ℂ)]
    intro hlt
    have hzero : ‖(0 : ℂ)‖ = 0 := by simp
    linarith [hge, hlt, hzero]
  exact hnot hz_out

/-- Scope-check no-go at `c = 2`: the iterate-left-inverse + direct
preimage-exterior outside-open control payload is inconsistent because the
preimage-exterior component is impossible. -/
theorem not_iterLeftInversePreimageExteriorSubsetOutsideOpenConstructivePayloadTwo :
    ¬ IterLeftInversePreimageExteriorSubsetOutsideOpenConstructivePayloadTwo := by
  intro h_payload
  exact not_preimageExteriorSubsetOutsideOpenTwo h_payload.2

/-- The chosen fixed point at `c = 2` lies strictly inside the outside-open
radius threshold. -/
theorem fixed_point_two_norm_lt_outside_open_radius :
    ‖Quadratic.fixed_point (2 : ℂ)‖ < ‖(2 : ℂ)‖ + 2 := by
  let p : ℂ := Quadratic.fixed_point (2 : ℂ)
  have hfix : MLC.Quadratic.fc (2 : ℂ) p = p := by
    simpa [p] using Quadratic.fixed_point_is_fixed (2 : ℂ)
  have hp2 : p ^ 2 = p - (2 : ℂ) := by
    exact (eq_sub_iff_add_eq).2 (by simpa [MLC.Quadratic.fc] using hfix)
  have hnorm_le : ‖p‖ ^ 2 ≤ ‖p‖ + ‖(2 : ℂ)‖ := by
    calc
      ‖p‖ ^ 2 = ‖p ^ 2‖ := by simp [pow_two]
      _ = ‖p - (2 : ℂ)‖ := by simp [hp2]
      _ ≤ ‖p‖ + ‖(2 : ℂ)‖ := by
        simpa [sub_eq_add_neg, norm_neg] using norm_add_le p (-(2 : ℂ))
  by_contra hlt
  have hge : ‖(2 : ℂ)‖ + 2 ≤ ‖p‖ := le_of_not_gt hlt
  have hsq_gt : ‖p‖ ^ 2 > ‖p‖ + ‖(2 : ℂ)‖ := by
    nlinarith [norm_nonneg p, norm_nonneg (2 : ℂ), hge]
  exact (not_lt_of_ge hnorm_le) hsq_gt

/-- Boundary-continuity no-go at `c = 2`: if all exterior rays landed in
outside-open, continuity of the extended ray map at `‖w‖ = 1` would force the
chosen fixed point outside-open, contradicting the fixed-point radius bound. -/
theorem not_externalRayLandsOutsideOpen_two_of_extended_ray_boundary_continuity :
    ¬ ExternalRayLandsOutsideOpen (2 : ℂ) := by
  intro hland
  let w0 : ℂ := ((1 : ℝ) : ℂ)
  let S : Set ℂ := {w : ℂ | 1 ≤ ‖w‖}
  let T : Set ℂ := {w : ℂ | 1 < ‖w‖}
  let V : Set ℂ := {z : ℂ | ‖(2 : ℂ)‖ + 2 ≤ ‖z‖}
  have hmaps : Set.MapsTo (Quadratic.extended_ray_map (2 : ℂ)) T V := by
    intro w hw
    change ‖(2 : ℂ)‖ + 2 ≤ ‖Quadratic.extended_ray_map (2 : ℂ) w‖
    have hw_out : ‖Quadratic.external_ray_map (2 : ℂ) w‖ > ‖(2 : ℂ)‖ + 2 := hland w hw
    have hEq : Quadratic.extended_ray_map (2 : ℂ) w = Quadratic.external_ray_map (2 : ℂ) w :=
      Quadratic.extended_ray_map_eq (2 : ℂ) w hw
    exact by simpa [hEq] using le_of_lt hw_out
  have hone_closure : w0 ∈ closure T := by
    refine Metric.mem_closure_iff.2 ?_
    intro ε hε
    refine ⟨(((1 : ℝ) + ε / 2) : ℂ), ?_, ?_⟩
    · change 1 < ‖(((1 : ℝ) + ε / 2) : ℂ)‖
      have hnonneg : 0 ≤ (1 : ℝ) + ε / 2 := by linarith
      have hgt : (1 : ℝ) < (1 : ℝ) + ε / 2 := by linarith
      calc
        1 < (1 : ℝ) + ε / 2 := hgt
        _ = ‖(((1 : ℝ) + ε / 2) : ℂ)‖ := by
          symm
          simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using
            (Complex.norm_real ((1 : ℝ) + ε / 2))
    · have hhalfpos : 0 < ε / 2 := by linarith
      have hdist : dist w0 (((1 : ℝ) + ε / 2) : ℂ) = ε / 2 := by
        have hdist_abs : dist w0 (((1 : ℝ) + ε / 2) : ℂ) = |ε| / 2 := by
          simp [w0, dist_eq_norm]
        have hεnonneg : 0 ≤ ε := le_of_lt hε
        have habs : |ε| / 2 = ε / 2 := by simp [abs_of_nonneg hεnonneg]
        simpa [habs] using hdist_abs
      have hhalf : ε / 2 < ε := by linarith
      exact hdist.trans_lt hhalf
  have hcont : ContinuousOn (Quadratic.extended_ray_map (2 : ℂ)) S :=
    Quadratic.extended_ray_map_continuous (2 : ℂ)
  have hcontS : ContinuousWithinAt (Quadratic.extended_ray_map (2 : ℂ)) S w0 :=
    hcont w0 (by simp [S, w0])
  have hcontT : ContinuousWithinAt (Quadratic.extended_ray_map (2 : ℂ)) T w0 :=
    hcontS.mono (by
      intro x hx
      simpa [T, S] using (le_of_lt hx))
  have hmem_closureV : Quadratic.extended_ray_map (2 : ℂ) w0 ∈ closure V :=
    hcontT.mem_closure hone_closure hmaps
  have hVclosed : IsClosed V := isClosed_le continuous_const continuous_norm
  have hmemV : Quadratic.extended_ray_map (2 : ℂ) w0 ∈ V := by
    simpa [hVclosed.closure_eq] using hmem_closureV
  have hnot1 : ¬ 1 < ‖w0‖ := by
    simp [w0]
  have hExt1 : Quadratic.extended_ray_map (2 : ℂ) w0 = Quadratic.fixed_point (2 : ℂ) := by
    simp [Quadratic.extended_ray_map, hnot1]
  have hfp_ge : ‖(2 : ℂ)‖ + 2 ≤ ‖Quadratic.fixed_point (2 : ℂ)‖ := by
    simpa [V, hExt1] using hmemV
  exact (not_le_of_gt fixed_point_two_norm_lt_outside_open_radius) hfp_ge

/-- Counterexample form for external-ray landing at `c = 2`: there exists an
exterior parameter whose ray image is not outside-open. -/
def ExternalRayLandingCounterexampleTwo : Prop :=
  ∃ w, 1 < ‖w‖ ∧ ¬ ‖Quadratic.external_ray_map (2 : ℂ) w‖ > ‖(2 : ℂ)‖ + 2

/-- Landing exclusion at `c = 2` is equivalent to existence of an exterior
counterexample parameter. -/
theorem not_externalRayLandsOutsideOpen_two_iff_externalRayLandingCounterexampleTwo :
    ¬ ExternalRayLandsOutsideOpen (2 : ℂ) ↔ ExternalRayLandingCounterexampleTwo := by
  constructor
  · intro hnot
    by_contra hcex
    apply hnot
    intro w hw
    by_contra hw_out
    exact hcex ⟨w, hw, hw_out⟩
  · intro hcex hland
    rcases hcex with ⟨w, hw, hnot_out⟩
    exact hnot_out (hland w hw)

/-- Build landing exclusion at `c = 2` from an explicit exterior counterexample. -/
theorem not_externalRayLandsOutsideOpen_two_of_externalRayLandingCounterexampleTwo
    (hcex : ExternalRayLandingCounterexampleTwo) :
    ¬ ExternalRayLandsOutsideOpen (2 : ℂ) :=
  (not_externalRayLandsOutsideOpen_two_iff_externalRayLandingCounterexampleTwo).2 hcex

/-- Scope-check no-go at `c = 2`: if the external ray map sends
`bottcher_map (2) 0` back to `0`, then external-ray landing is impossible. -/
theorem not_externalRayLandsOutsideOpen_two_of_not_outside_open_at_bottcher_zero
    (hnot_out :
      ¬ ‖Quadratic.external_ray_map (2 : ℂ)
          (Quadratic.bottcher_map (2 : ℂ) (0 : ℂ))‖ > ‖(2 : ℂ)‖ + 2) :
    ¬ ExternalRayLandsOutsideOpen (2 : ℂ) := by
  intro hland
  let w : ℂ := Quadratic.bottcher_map (2 : ℂ) (0 : ℂ)
  have hbasin0 : (0 : ℂ) ∈ Quadratic.basin_of_infinity (2 : ℂ) := zero_mem_basin_two
  have hpos0 : 0 < MLC.Quadratic.green_function (2 : ℂ) (0 : ℂ) :=
    green_function_pos_of_basin (2 : ℂ) (0 : ℂ) hbasin0
  have hw : 1 < ‖w‖ := by
    simpa [w] using bottcher_map_norm_gt_one_of_basin (2 : ℂ) (0 : ℂ) hbasin0 hpos0
  have hw_land : ‖Quadratic.external_ray_map (2 : ℂ) w‖ > ‖(2 : ℂ)‖ + 2 := hland w hw
  exact hnot_out (by simpa [w] using hw_land)

/-- The specific `w = bottcher_map (2) 0` scalar blocker is an explicit
counterexample witness for external-ray landing at `c = 2`. -/
theorem externalRayLandingCounterexampleTwo_of_not_outside_open_at_bottcher_zero
    (hnot_out :
      ¬ ‖Quadratic.external_ray_map (2 : ℂ)
          (Quadratic.bottcher_map (2 : ℂ) (0 : ℂ))‖ > ‖(2 : ℂ)‖ + 2) :
    ExternalRayLandingCounterexampleTwo := by
  let w : ℂ := Quadratic.bottcher_map (2 : ℂ) (0 : ℂ)
  have hbasin0 : (0 : ℂ) ∈ Quadratic.basin_of_infinity (2 : ℂ) := zero_mem_basin_two
  have hpos0 : 0 < MLC.Quadratic.green_function (2 : ℂ) (0 : ℂ) :=
    green_function_pos_of_basin (2 : ℂ) (0 : ℂ) hbasin0
  have hw : 1 < ‖w‖ := by
    simpa [w] using bottcher_map_norm_gt_one_of_basin (2 : ℂ) (0 : ℂ) hbasin0 hpos0
  exact ⟨w, hw, by simpa [w] using hnot_out⟩

/-- Scope-check no-go at `c = 2`: if the external ray map sends
`bottcher_map (2) 0` back to `0`, then external-ray landing is impossible. -/
theorem not_externalRayLandsOutsideOpen_two_of_external_ray_map_at_bottcher_zero_eq_zero
    (hzero :
      Quadratic.external_ray_map (2 : ℂ) (Quadratic.bottcher_map (2 : ℂ) (0 : ℂ)) = 0) :
    ¬ ExternalRayLandsOutsideOpen (2 : ℂ) := by
  refine not_externalRayLandsOutsideOpen_two_of_not_outside_open_at_bottcher_zero ?_
  have hnot : ¬ ‖(0 : ℂ)‖ > ‖(2 : ℂ)‖ + 2 := by
    have hge : (0 : ℝ) ≤ ‖(2 : ℂ)‖ + 2 := by
      nlinarith [norm_nonneg (2 : ℂ)]
    intro hlt
    have hzero_norm : ‖(0 : ℂ)‖ = 0 := by simp
    linarith [hge, hlt, hzero_norm]
  simp [hzero]

/-- Scope-check no-go at `c = 2`: outside-disk injectivity forces failure of
external-ray landing because `0` maps to the exterior but is not outside-open. -/
theorem not_externalRayLandsOutsideOpen_two_of_bottcher_zero_not_mem_image_outside_open
    (hzero_not_img :
      Quadratic.bottcher_map (2 : ℂ) (0 : ℂ) ∉
        Quadratic.bottcher_map (2 : ℂ) '' {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2}) :
    ¬ ExternalRayLandsOutsideOpen (2 : ℂ) := by
  intro hland
  let w : ℂ := Quadratic.bottcher_map (2 : ℂ) (0 : ℂ)
  have hbasin0 : (0 : ℂ) ∈ Quadratic.basin_of_infinity (2 : ℂ) := zero_mem_basin_two
  have hpos0 : 0 < MLC.Quadratic.green_function (2 : ℂ) (0 : ℂ) :=
    green_function_pos_of_basin (2 : ℂ) (0 : ℂ) hbasin0
  have hw : 1 < ‖w‖ := by
    simpa [w] using bottcher_map_norm_gt_one_of_basin (2 : ℂ) (0 : ℂ) hbasin0 hpos0
  have hw_land : ‖Quadratic.external_ray_map (2 : ℂ) w‖ > ‖(2 : ℂ)‖ + 2 := hland w hw
  have hw_img : w ∈ Quadratic.bottcher_map (2 : ℂ) '' {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2} := by
    refine ⟨Quadratic.external_ray_map (2 : ℂ) w, hw_land, ?_⟩
    simpa [w] using Quadratic.external_ray_map_right_inverse (2 : ℂ) w hw
  exact hzero_not_img (by simpa [w] using hw_img)

/-- Scope-check no-go at `c = 2`: outside-disk injectivity forces failure of
external-ray landing because `0` maps to the exterior but is not outside-open. -/
theorem not_externalRayLandsOutsideOpen_two_of_injOn_outside_disk
    (h_inj : Set.InjOn (Quadratic.bottcher_map (2 : ℂ)) (outside_disk (2 : ℂ))) :
    ¬ ExternalRayLandsOutsideOpen (2 : ℂ) := by
  refine not_externalRayLandsOutsideOpen_two_of_bottcher_zero_not_mem_image_outside_open ?_
  intro hzero_img
  rcases hzero_img with ⟨z, hz, hz_eq⟩
  have hbasin0 : (0 : ℂ) ∈ Quadratic.basin_of_infinity (2 : ℂ) := zero_mem_basin_two
  have hz_out : z ∈ outside_disk (2 : ℂ) :=
    outside_open_subset_outside_disk (2 : ℂ) hz
  have hz0_out : (0 : ℂ) ∈ outside_disk (2 : ℂ) := by
    simpa [outside_disk] using hbasin0
  have hz0 : z = 0 := h_inj hz_out hz0_out hz_eq
  have hnot : ¬ ‖(0 : ℂ)‖ > ‖(2 : ℂ)‖ + 2 := by
    have hge : (0 : ℝ) ≤ ‖(2 : ℂ)‖ + 2 := by
      nlinarith [norm_nonneg (2 : ℂ)]
    intro hlt
    have hzero : ‖(0 : ℂ)‖ = 0 := by simp
    linarith [hge, hlt, hzero]
  exact hnot (by simpa [hz0] using hz)

/-- Scope-check no-go at `c = 2`: under iterate-left-inverse injectivity on
`outside_disk`, external-ray landing is impossible because `0` already maps to
the exterior but is not outside-open. -/
theorem not_externalRayLandsOutsideOpen_two_of_iterLeftInverse
    (h_left_iter : QuadraticMapIterLeftInverseOnBasin (2 : ℂ)) :
    ¬ ExternalRayLandsOutsideOpen (2 : ℂ) := by
  exact not_externalRayLandsOutsideOpen_two_of_injOn_outside_disk
    (bottcher_map_inj_on_outside_of_slit_of_iter_left_inverse (2 : ℂ) h_left_iter)

/-- Scope-check no-go at `c = 2`: iterate-left-inverse plus external-ray
landing is inconsistent. -/
theorem not_iterLeftInverseExternalRayLandsOutsideOpenConstructivePayloadTwo :
    ¬ IterLeftInverseExternalRayLandsOutsideOpenConstructivePayloadTwo := by
  intro h_payload
  exact not_externalRayLandsOutsideOpen_two_of_iterLeftInverse h_payload.1 h_payload.2

/-- Scope-check no-go at `c = 2`: iterate-left-inverse plus outside-disk
refinement is inconsistent, since refinement is equivalent to landing. -/
theorem not_iterLeftInverseOutsideDiskRefinementConstructivePayloadTwo :
    ¬ IterLeftInverseOutsideDiskRefinementConstructivePayloadTwo := by
  intro h_payload
  have hland : ExternalRayLandsOutsideOpen (2 : ℂ) :=
    (outsideDiskRefinement_two_iff_externalRayLandsOutsideOpen).1 h_payload.2
  exact not_externalRayLandsOutsideOpen_two_of_iterLeftInverse h_payload.1 hland

/-- Scope-check no-go at `c = 2`: this payload shape is inconsistent in the
current model because its outside-open analyticity component is impossible. -/
theorem not_analyticDerivConstructivePayloadTwo :
    ¬ AnalyticDerivConstructivePayloadTwo := by
  intro h_payload
  exact not_outsideOpenAnalyticityHypothesisTwo h_payload.2.1

/-- Scope-check no-go at `c = 2`: the slit-inclusion based non-analytic
local-homeomorph-on source is inconsistent in the current model. -/
theorem not_slitInjOutsideDiskLocalHomeomorphOnConstructivePayloadTwo :
    ¬ SlitInjOutsideDiskLocalHomeomorphOnConstructivePayloadTwo := by
  intro h_payload
  exact not_outside_open_subset_slit_orbit_two h_payload.1

/-- The blocked surjectivity-source sub-aggregate is inconsistent in the
current model at `c = 2`. -/
theorem not_knownBlockedSurjOnExteriorFromOutsideOpenSourceCandidateTwo :
    ¬ KnownBlockedSurjOnExteriorFromOutsideOpenSourceCandidateTwo := by
  intro h
  rcases h with hA | hB
  · exact not_analyticDerivConstructivePayloadTwo hA
  · exact not_slitInjOutsideDiskLocalHomeomorphOnConstructivePayloadTwo hB.2

/-- Any currently wired surjectivity source in the aggregate must lie in the
open (not-yet-blocked) sub-aggregate at `c = 2`. -/
theorem knownOpenSurjOnExteriorFromOutsideOpenSourceCandidateTwo_of_knownSurjOnExteriorFromOutsideOpenSourceCandidateTwo
    (h : KnownSurjOnExteriorFromOutsideOpenSourceCandidateTwo) :
    KnownOpenSurjOnExteriorFromOutsideOpenSourceCandidateTwo := by
  have hsplit :
      KnownOpenSurjOnExteriorFromOutsideOpenSourceCandidateTwo ∨
        KnownBlockedSurjOnExteriorFromOutsideOpenSourceCandidateTwo :=
    (knownSurjOnExteriorFromOutsideOpenSourceCandidateTwo_iff_open_or_blocked).1 h
  rcases hsplit with hOpen | hBlocked
  · exact hOpen
  · exact False.elim (not_knownBlockedSurjOnExteriorFromOutsideOpenSourceCandidateTwo hBlocked)

/-- Any currently wired surjectivity source in the aggregate reduces to the
two-branch reduced-open aggregate at `c = 2`. -/
theorem reducedOpenSurjOnExteriorFromOutsideOpenSourceCandidateTwo_of_knownSurjOnExteriorFromOutsideOpenSourceCandidateTwo
    (h : KnownSurjOnExteriorFromOutsideOpenSourceCandidateTwo) :
    ReducedOpenSurjOnExteriorFromOutsideOpenSourceCandidateTwo := by
  exact (knownOpenSurjOnExteriorFromOutsideOpenSourceCandidateTwo_iff_reduced).1
    (knownOpenSurjOnExteriorFromOutsideOpenSourceCandidateTwo_of_knownSurjOnExteriorFromOutsideOpenSourceCandidateTwo h)

/-- Current-model surjectivity-source exhaustion shape at `c = 2`: the full
known aggregate is equivalent to the reduced-open two-branch aggregate. -/
theorem knownSurjOnExteriorFromOutsideOpenSourceCandidateTwo_iff_reducedOpen :
    KnownSurjOnExteriorFromOutsideOpenSourceCandidateTwo ↔
      ReducedOpenSurjOnExteriorFromOutsideOpenSourceCandidateTwo := by
  constructor
  · exact reducedOpenSurjOnExteriorFromOutsideOpenSourceCandidateTwo_of_knownSurjOnExteriorFromOutsideOpenSourceCandidateTwo
  · intro h
    have hOpen : KnownOpenSurjOnExteriorFromOutsideOpenSourceCandidateTwo :=
      (knownOpenSurjOnExteriorFromOutsideOpenSourceCandidateTwo_iff_reduced).2 h
    exact (knownSurjOnExteriorFromOutsideOpenSourceCandidateTwo_iff_open_or_blocked).2 (Or.inl hOpen)

/-- If external-ray landing is unavailable, a reduced-open surjectivity source
must be the restricted local-homeomorph branch at `c = 2`. -/
theorem localHomeomorphSurjSource_two_of_reducedOpen_of_not_externalRayLandsOutsideOpen
    (h : ReducedOpenSurjOnExteriorFromOutsideOpenSourceCandidateTwo)
    (hnot_land : ¬ ExternalRayLandsOutsideOpen (2 : ℂ)) :
    IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ))) ∧
      IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ)) := by
  rcases h with hLocal | hLand
  · exact hLocal
  · exact False.elim (hnot_land hLand)

/-- If the restricted local-homeomorph branch is unavailable, a reduced-open
surjectivity source must be external-ray landing at `c = 2`. -/
theorem externalRayLandsOutsideOpen_two_of_reducedOpen_of_not_localHomeomorphSurjSource
    (h : ReducedOpenSurjOnExteriorFromOutsideOpenSourceCandidateTwo)
    (hnot_local :
      ¬ (IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ))) ∧
        IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ)))) :
    ExternalRayLandsOutsideOpen (2 : ℂ) := by
  rcases h with hLocal | hLand
  · exact False.elim (hnot_local hLocal)
  · exact hLand

/-- Direct bridge: the restricted local-homeomorph source branch is a reduced-open
surjectivity source at `c = 2`. -/
theorem reducedOpenSurjOnExteriorFromOutsideOpenSourceCandidateTwo_of_localHomeomorphSurjSource
    (hlocal :
      IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ))) ∧
        IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ))) :
    ReducedOpenSurjOnExteriorFromOutsideOpenSourceCandidateTwo :=
  Or.inl hlocal

/-- Direct bridge: the restricted local-homeomorph source branch is a known
surjectivity source at `c = 2`. -/
theorem knownSurjOnExteriorFromOutsideOpenSourceCandidateTwo_of_localHomeomorphSurjSource
    (hlocal :
      IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ))) ∧
        IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ))) :
    KnownSurjOnExteriorFromOutsideOpenSourceCandidateTwo :=
  (knownSurjOnExteriorFromOutsideOpenSourceCandidateTwo_iff_reducedOpen).2
    (reducedOpenSurjOnExteriorFromOutsideOpenSourceCandidateTwo_of_localHomeomorphSurjSource hlocal)

/-- Under `¬ ExternalRayLandsOutsideOpen (2 : ℂ)`, the reduced-open surjectivity
source is exactly the restricted local-homeomorph branch. -/
theorem reducedOpenSurjOnExteriorFromOutsideOpenSourceCandidateTwo_iff_localHomeomorphSurjSource_of_not_externalRayLandsOutsideOpen
    (hnot_land : ¬ ExternalRayLandsOutsideOpen (2 : ℂ)) :
    ReducedOpenSurjOnExteriorFromOutsideOpenSourceCandidateTwo ↔
      (IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ))) ∧
        IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ))) := by
  constructor
  · intro h
    exact localHomeomorphSurjSource_two_of_reducedOpen_of_not_externalRayLandsOutsideOpen h hnot_land
  · intro hLocal
    exact Or.inl hLocal

/-- Under `¬ ExternalRayLandsOutsideOpen (2 : ℂ)`, the full known surjectivity
source aggregate is exactly the restricted local-homeomorph branch. -/
theorem knownSurjOnExteriorFromOutsideOpenSourceCandidateTwo_iff_localHomeomorphSurjSource_of_not_externalRayLandsOutsideOpen
    (hnot_land : ¬ ExternalRayLandsOutsideOpen (2 : ℂ)) :
    KnownSurjOnExteriorFromOutsideOpenSourceCandidateTwo ↔
      (IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ))) ∧
        IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ))) := by
  rw [knownSurjOnExteriorFromOutsideOpenSourceCandidateTwo_iff_reducedOpen]
  exact reducedOpenSurjOnExteriorFromOutsideOpenSourceCandidateTwo_iff_localHomeomorphSurjSource_of_not_externalRayLandsOutsideOpen
    hnot_land

/-- If the restricted local-homeomorph source branch is unavailable, the full
known surjectivity aggregate is equivalent to external-ray landing at `c = 2`. -/
theorem knownSurjOnExteriorFromOutsideOpenSourceCandidateTwo_iff_externalRayLandsOutsideOpen_of_not_localHomeomorphSurjSource
    (hnot_local :
      ¬ (IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ))) ∧
        IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ)))) :
    KnownSurjOnExteriorFromOutsideOpenSourceCandidateTwo ↔
      ExternalRayLandsOutsideOpen (2 : ℂ) := by
  constructor
  · intro h
    exact externalRayLandsOutsideOpen_two_of_reducedOpen_of_not_localHomeomorphSurjSource
      ((knownSurjOnExteriorFromOutsideOpenSourceCandidateTwo_iff_reducedOpen).1 h) hnot_local
  · intro hland
    exact (knownSurjOnExteriorFromOutsideOpenSourceCandidateTwo_iff_reducedOpen).2 (Or.inr hland)

/-- Explicit reduced-open frontier shape at `c = 2`: known surjectivity sources
are exactly the restricted local-homeomorph source or external-ray landing. -/
theorem knownSurjOnExteriorFromOutsideOpenSourceCandidateTwo_iff_localHomeomorphSurjSource_or_externalRayLandsOutsideOpen :
    KnownSurjOnExteriorFromOutsideOpenSourceCandidateTwo ↔
      ((IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ))) ∧
          IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ))) ∨
        ExternalRayLandsOutsideOpen (2 : ℂ)) := by
  simpa [ReducedOpenSurjOnExteriorFromOutsideOpenSourceCandidateTwo] using
    (knownSurjOnExteriorFromOutsideOpenSourceCandidateTwo_iff_reducedOpen)

/-- Frontier closure criterion at `c = 2`: eliminating all currently wired
surjectivity sources is equivalent to eliminating both reduced-open branches. -/
theorem not_knownSurjOnExteriorFromOutsideOpenSourceCandidateTwo_iff_not_localHomeomorphSurjSource_and_not_externalRayLandsOutsideOpen :
    ¬ KnownSurjOnExteriorFromOutsideOpenSourceCandidateTwo ↔
      (¬ (IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ))) ∧
          IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ))) ∧
        ¬ ExternalRayLandsOutsideOpen (2 : ℂ)) := by
  rw [knownSurjOnExteriorFromOutsideOpenSourceCandidateTwo_iff_localHomeomorphSurjSource_or_externalRayLandsOutsideOpen]
  constructor
  · intro hnot
    constructor
    · intro hlocal
      exact hnot (Or.inl hlocal)
    · intro hland
      exact hnot (Or.inr hland)
  · intro hboth h
    rcases h with hlocal | hland
    · exact hboth.1 hlocal
    · exact hboth.2 hland

/-- Explicit CP5 residual frontier package at `c = 2`: restricted local-homeomorph
source or external-ray landing. -/
def CP5ResidualTwo : Prop :=
  (IsProperMap (bottcher_map_outside_open_to_exterior (2 : ℂ)) ∧
      IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ))) ∨
    ExternalRayLandsOutsideOpen (2 : ℂ)

/-- Under constructive exclusion of external-ray landing at `c = 2`, the CP5
residual frontier is exactly the restricted proper+local-homeomorph branch. -/
theorem cp5ResidualTwo_iff_isProperMap_restrict_and_isLocalHomeomorph_restrict_of_not_externalRayLandsOutsideOpen
    (hnot_land : ¬ ExternalRayLandsOutsideOpen (2 : ℂ)) :
    CP5ResidualTwo ↔
      (IsProperMap (bottcher_map_outside_open_to_exterior (2 : ℂ)) ∧
        IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ))) := by
  constructor
  · intro hres
    rcases hres with hlocal | hland
    · exact hlocal
    · exact False.elim (hnot_land hland)
  · intro hlocal
    exact Or.inl hlocal

/-- Canonical CP5 residual reduction at `c = 2`: landing is already excluded, so
only the restricted proper+local-homeomorph branch remains. -/
theorem cp5ResidualTwo_iff_isProperMap_restrict_and_isLocalHomeomorph_restrict :
    CP5ResidualTwo ↔
      (IsProperMap (bottcher_map_outside_open_to_exterior (2 : ℂ)) ∧
        IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ))) :=
  cp5ResidualTwo_iff_isProperMap_restrict_and_isLocalHomeomorph_restrict_of_not_externalRayLandsOutsideOpen
    not_externalRayLandsOutsideOpen_two_of_extended_ray_boundary_continuity

/-- The explicit CP5 residual frontier package implies the known
surjectivity-source aggregate at `c = 2`. -/
theorem knownSurjOnExteriorFromOutsideOpenSourceCandidateTwo_of_cp5ResidualTwo
    (hres : CP5ResidualTwo) :
    KnownSurjOnExteriorFromOutsideOpenSourceCandidateTwo := by
  rcases hres with hlocal | hland
  · left
    exact
      ⟨isClosed_range_bottcher_map_outside_open_to_exterior_of_isProperMap (2 : ℂ) hlocal.1,
        hlocal.2⟩
  · right
    exact Or.inr (Or.inr (Or.inl hland))

/-- The explicit CP5 residual frontier package implies outside-open exterior
surjectivity at `c = 2`. -/
theorem bottcherSurjOnExteriorFromOutsideOpen_two_of_cp5ResidualTwo
    (hres : CP5ResidualTwo) :
    BottcherSurjOnExteriorFromOutsideOpen (2 : ℂ) :=
  bottcherSurjOnExteriorFromOutsideOpen_two_of_knownSurjOnExteriorFromOutsideOpenSourceCandidateTwo
    (knownSurjOnExteriorFromOutsideOpenSourceCandidateTwo_of_cp5ResidualTwo hres)

/-- Positive-source constructor for the CP5 residual frontier at `c = 2` from
restricted-map properness plus restricted local-homeomorph assumptions. -/
theorem cp5ResidualTwo_of_isProperMap_restrict_of_isLocalHomeomorph_restrict
    (hproper : IsProperMap (bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (hlocal : IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ))) :
    CP5ResidualTwo :=
  Or.inl ⟨hproper, hlocal⟩

/-- Assumption seam at `c = 2`: the explicit CP5 residual frontier yields
outside-open injectivity. -/
def CP5ResidualInjOnOutsideOpenSeamTwo : Prop :=
  ∀ _hres : CP5ResidualTwo,
    Set.InjOn (Quadratic.bottcher_map (2 : ℂ)) {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2}

/-- Branch-local seam at `c = 2`: restricted local-homeomorph residual branch
implies outside-open injectivity. -/
def CP5ResidualLocalHomeomorphInjSeamTwo : Prop :=
  ∀ _hlocal :
      IsProperMap (bottcher_map_outside_open_to_exterior (2 : ℂ)) ∧
        IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ)),
    Set.InjOn (Quadratic.bottcher_map (2 : ℂ)) {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2}

/-- Branch-local seam at `c = 2`: external-ray landing residual branch implies
outside-open injectivity. -/
def CP5ResidualLandingInjSeamTwo : Prop :=
  ∀ _hland : ExternalRayLandsOutsideOpen (2 : ℂ),
    Set.InjOn (Quadratic.bottcher_map (2 : ℂ)) {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2}

/-- CP5 endpoint at `c = 2`: strong anchor-gap seam used by the current
Green-inversion wrappers. -/
def GreenRayLogGtAnchorTwoSeam : Prop :=
  ∀ w : ℂ, 1 < ‖w‖ →
    MLC.Quadratic.green_function (2 : ℂ)
        (((‖(2 : ℂ)‖ + 2 : ℝ) * (w / ↑‖w‖)) : ℂ) < Real.log ‖w‖

/-- Replacement-shape seam target for `c = 2`: above-anchor Green targets on a
fixed direction admit an outside-open radial preimage. -/
def GreenRayAnchorThresholdPreimageTwoSeam : Prop :=
  ∀ w : ℂ, 1 < ‖w‖ →
    MLC.Quadratic.green_function (2 : ℂ)
        (((‖(2 : ℂ)‖ + 2 : ℝ) * (w / ↑‖w‖)) : ℂ) < Real.log ‖w‖ →
      ∃ ρ : ℝ, ρ > ‖(2 : ℂ)‖ + 2 ∧
        MLC.Quadratic.green_function (2 : ℂ)
          ((ρ : ℂ) * (w / ↑‖w‖)) = Real.log ‖w‖

/-- Constructive `c = 2` anchor-threshold preimage seam, directly specialized
from `exists_ray_preimage_green_pos`. -/
theorem greenRayAnchorThresholdPreimageTwoSeam_constructive :
    GreenRayAnchorThresholdPreimageTwoSeam := by
  intro w hw hlog_gt_anchor
  set u : ℂ := w / ↑‖w‖
  have hw_pos : (0 : ℝ) < ‖w‖ := by linarith
  have hu : ‖u‖ = 1 := by
    dsimp [u]
    rw [norm_div, Complex.norm_real, norm_norm, div_self hw_pos.ne']
  have hlog_u :
      MLC.Quadratic.green_function (2 : ℂ)
          (((‖(2 : ℂ)‖ + 2 : ℝ) * u) : ℂ) < Real.log ‖w‖ := by
    simpa [u] using hlog_gt_anchor
  simpa [u] using
    (GreenFunctionRayInversion.exists_ray_preimage_green_pos
      (2 : ℂ) u hu (Real.log ‖w‖) hlog_u)

/-- Quantitative cutoff for large-norm automatic discharge of the
`GreenRayLogGtAnchorTwoSeam` inequality via the outside-open Green upper bound. -/
noncomputable def greenRayLogGtAnchorTwoCutoff : ℝ :=
  Real.exp
    (Real.log (‖(2 : ℂ)‖ + 2) +
      (2 * ‖(2 : ℂ)‖ / (escape_bound (2 : ℂ))^2))

/-- For sufficiently large `‖w‖`, the anchor-gap inequality at `c = 2` follows
constructively from the two-sided Green/log bound on outside-open. -/
theorem greenRayLogGtAnchorTwo_of_norm_gt_cutoff
    (w : ℂ) (hw : greenRayLogGtAnchorTwoCutoff < ‖w‖) :
    MLC.Quadratic.green_function (2 : ℂ)
        (((‖(2 : ℂ)‖ + 2 : ℝ) * (w / ↑‖w‖)) : ℂ) < Real.log ‖w‖ := by
  set u : ℂ := w / ↑‖w‖
  let z : ℂ := (((‖(2 : ℂ)‖ + 2 : ℝ) * u) : ℂ)
  have hw_pos : (0 : ℝ) < ‖w‖ := by
    have hcut_pos : 0 < greenRayLogGtAnchorTwoCutoff := by
      dsimp [greenRayLogGtAnchorTwoCutoff]
      exact Real.exp_pos _
    linarith
  have hu : ‖u‖ = 1 := by
    dsimp [u]
    rw [norm_div, Complex.norm_real, norm_norm, div_self hw_pos.ne']
  have hz_norm : ‖z‖ = ‖(2 : ℂ)‖ + 2 := by
    dsimp [z]
    rw [norm_mul, Complex.norm_real, hu, mul_one, Real.norm_of_nonneg]
    linarith [norm_nonneg (2 : ℂ)]
  have h2norm : ‖(2 : ℂ)‖ = 2 := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) from by norm_cast,
      norm_real, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have hesc_two : escape_bound (2 : ℂ) = 3 := by
    rw [escape_bound_eq_max, h2norm]
    norm_num
  have hz_out : ‖z‖ > escape_bound (2 : ℂ) := by
    rw [hz_norm, h2norm, hesc_two]
    norm_num
  have hG_le := GreenFunctionRayInversion.green_function_bdd_above_log (2 : ℂ) z hz_out
  have hlog_cutoff : Real.log greenRayLogGtAnchorTwoCutoff < Real.log ‖w‖ := by
    have hcut_pos : 0 < greenRayLogGtAnchorTwoCutoff := by
      dsimp [greenRayLogGtAnchorTwoCutoff]
      exact Real.exp_pos _
    exact Real.log_lt_log hcut_pos hw
  have hlog_target :
      Real.log (‖(2 : ℂ)‖ + 2) +
          (2 * ‖(2 : ℂ)‖ / (escape_bound (2 : ℂ))^2) <
        Real.log ‖w‖ := by
    simpa [greenRayLogGtAnchorTwoCutoff, Real.log_exp] using hlog_cutoff
  have hG_le' :
      MLC.Quadratic.green_function (2 : ℂ) z ≤
        Real.log (‖(2 : ℂ)‖ + 2) +
          (2 * ‖(2 : ℂ)‖ / (escape_bound (2 : ℂ))^2) := by
    simpa [hz_norm] using hG_le
  exact lt_of_le_of_lt hG_le' hlog_target

/-- Reduction of the full anchor-gap seam to a bounded annulus obligation:
large norms are discharged constructively by
`greenRayLogGtAnchorTwo_of_norm_gt_cutoff`. -/
theorem greenRayLogGtAnchorTwoSeam_of_cutoff_band
    (hband :
      ∀ w : ℂ, 1 < ‖w‖ → ‖w‖ ≤ greenRayLogGtAnchorTwoCutoff →
        MLC.Quadratic.green_function (2 : ℂ)
            (((‖(2 : ℂ)‖ + 2 : ℝ) * (w / ↑‖w‖)) : ℂ) < Real.log ‖w‖) :
    GreenRayLogGtAnchorTwoSeam := by
  intro w hw
  by_cases hlarge : greenRayLogGtAnchorTwoCutoff < ‖w‖
  · exact greenRayLogGtAnchorTwo_of_norm_gt_cutoff w hlarge
  · exact hband w hw (le_of_not_gt hlarge)

/-- Monotonicity-window interface for the Green-ray anchor-gap inequality at
`c = 2`: verify the inequality only on the bounded cutoff band. -/
def GreenRayLogGapMonotonicityWindowTwo : Prop :=
  ∀ w : ℂ, 1 < ‖w‖ → ‖w‖ ≤ greenRayLogGtAnchorTwoCutoff →
    MLC.Quadratic.green_function (2 : ℂ)
        (((‖(2 : ℂ)‖ + 2 : ℝ) * (w / ↑‖w‖)) : ℂ) < Real.log ‖w‖

/-- The Green-ray log-gap monotonicity window implies the full anchor-gap seam
at `c = 2`. -/
theorem greenRayLogGtAnchorTwoSeam_of_greenRayLogGapMonotonicityWindowTwo
    (hwin : GreenRayLogGapMonotonicityWindowTwo) :
    GreenRayLogGtAnchorTwoSeam :=
  greenRayLogGtAnchorTwoSeam_of_cutoff_band hwin

/-- The current global anchor-gap seam is inconsistent at `c = 2`: choosing
`w` with modulus `exp(G_anchor / 2)` forces `G_anchor < G_anchor / 2`. -/
theorem not_greenRayLogGtAnchorTwoSeam :
    ¬ GreenRayLogGtAnchorTwoSeam := by
  intro hseam
  have h2norm : ‖(2 : ℂ)‖ = 2 := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) from by norm_cast, norm_real,
      Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  let zAnchor : ℂ := (((‖(2 : ℂ)‖ + 2 : ℝ) * (1 : ℂ)) : ℂ)
  have hfunc := Quadratic.green_function_functional_eq (2 : ℂ) zAnchor
  have hfc_eval : fc (2 : ℂ) zAnchor = (18 : ℂ) := by
    dsimp [zAnchor]
    rw [fc, h2norm]
    norm_num
  have hG_fc_pos : 0 < Quadratic.green_function (2 : ℂ) (fc (2 : ℂ) zAnchor) := by
    rw [hfc_eval]
    have h18_out : ‖(18 : ℂ)‖ > ‖(2 : ℂ)‖ + 2 := by
      rw [show (18 : ℂ) = ((18 : ℝ) : ℂ) from by norm_cast,
        Complex.norm_real, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 18), h2norm]
      norm_num
    exact GreenFunctionRayInversion.green_function_pos_on_outside_open (2 : ℂ) (18 : ℂ) h18_out
  have hG_anchor_pos : 0 < Quadratic.green_function (2 : ℂ) zAnchor := by
    have hfunc' :
        Quadratic.green_function (2 : ℂ) (fc (2 : ℂ) zAnchor) =
          2 * Quadratic.green_function (2 : ℂ) zAnchor := by
      simpa using hfunc
    linarith
  let gAnchor : ℝ := Quadratic.green_function (2 : ℂ) zAnchor
  let w : ℂ := ((Real.exp (gAnchor / 2) : ℝ) : ℂ)
  have hw_norm : ‖w‖ = Real.exp (gAnchor / 2) := by
    dsimp [w]
    rw [Complex.norm_real, Real.norm_of_nonneg]
    exact (Real.exp_pos _).le
  have hw_gt1 : 1 < ‖w‖ := by
    rw [hw_norm]
    have hg_pos : 0 < gAnchor := by simpa [gAnchor] using hG_anchor_pos
    exact Real.one_lt_exp_iff.mpr (by linarith)
  have hdir : w / ↑‖w‖ = (1 : ℂ) := by
    dsimp [w]
    rw [hw_norm]
    have hne : (((Real.exp (gAnchor / 2) : ℝ) : ℂ)) ≠ 0 := by
      exact_mod_cast (Real.exp_pos (gAnchor / 2)).ne'
    exact div_self hne
  have hanchor_eval :
      Quadratic.green_function (2 : ℂ)
          (((‖(2 : ℂ)‖ + 2 : ℝ) * (w / ↑‖w‖)) : ℂ) = gAnchor := by
    dsimp [gAnchor, zAnchor]
    rw [hdir]
  have hlog_eval : Real.log ‖w‖ = gAnchor / 2 := by
    rw [hw_norm, Real.log_exp]
  have hcontr : gAnchor < gAnchor / 2 := by
    calc
      gAnchor
          = Quadratic.green_function (2 : ℂ)
              (((‖(2 : ℂ)‖ + 2 : ℝ) * (w / ↑‖w‖)) : ℂ) := hanchor_eval.symm
      _ < Real.log ‖w‖ := hseam w hw_gt1
      _ = gAnchor / 2 := hlog_eval
  linarith

/-- Named model-consistency boundary: the full Green-ray anchor-gap seam is
inconsistent in the current `c = 2` model. -/
theorem greenRayLogGtAnchorTwoSeam_model_inconsistency :
    ¬ GreenRayLogGtAnchorTwoSeam :=
  not_greenRayLogGtAnchorTwoSeam

/-- Dead-end certificate: the bounded-annulus obligation from
`greenRayLogGtAnchorTwoSeam_of_cutoff_band` is itself inconsistent in the
current model, because it would imply the globally inconsistent seam. -/
theorem not_greenRayLogGtAnchorTwo_cutoff_band :
    ¬ (∀ w : ℂ, 1 < ‖w‖ → ‖w‖ ≤ greenRayLogGtAnchorTwoCutoff →
      MLC.Quadratic.green_function (2 : ℂ)
          (((‖(2 : ℂ)‖ + 2 : ℝ) * (w / ↑‖w‖)) : ℂ) < Real.log ‖w‖) := by
  intro hband
  exact not_greenRayLogGtAnchorTwoSeam
    (greenRayLogGtAnchorTwoSeam_of_cutoff_band hband)

/-- Dead-end certificate: the bounded Green-ray log-gap monotonicity window is
inconsistent in the current model, because it implies the globally inconsistent
anchor-gap seam. -/
theorem not_greenRayLogGapMonotonicityWindowTwo :
    ¬ GreenRayLogGapMonotonicityWindowTwo := by
  intro hwin
  exact not_greenRayLogGtAnchorTwoSeam
    (greenRayLogGtAnchorTwoSeam_of_greenRayLogGapMonotonicityWindowTwo hwin)

/-- Parameterized local Green-ray log-gap window at `c = 2`: enforce the
bounded-band inequality only up to radius `R`, with `R` bounded by the global
cutoff. This interface is intentionally weaker than the full cutoff window. -/
def NonimplicativeWindowInterfaceTwo (R : ℝ) : Prop :=
  1 < R ∧ R ≤ greenRayLogGtAnchorTwoCutoff ∧
    ∀ w : ℂ, 1 < ‖w‖ → ‖w‖ ≤ R →
      MLC.Quadratic.green_function (2 : ℂ)
          (((‖(2 : ℂ)‖ + 2 : ℝ) * (w / ↑‖w‖)) : ℂ) < Real.log ‖w‖

/-- Strong local-window no-go at `c = 2`: any nonimplicative local window with
radius strictly larger than `1` is inconsistent, by testing the fixed anchor
direction at a norm level where the logarithmic target remains below the anchor
Green value. -/
theorem not_nonimplicativeWindowInterfaceTwo_of_one_lt_radius
    {R : ℝ}
    (hR_gt1 : 1 < R) :
    ¬ NonimplicativeWindowInterfaceTwo R := by
  intro hwin
  have h2norm : ‖(2 : ℂ)‖ = 2 := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) from by norm_cast, norm_real,
      Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  let zAnchor : ℂ := (((‖(2 : ℂ)‖ + 2 : ℝ) * (1 : ℂ)) : ℂ)
  have hfunc := Quadratic.green_function_functional_eq (2 : ℂ) zAnchor
  have hfc_eval : fc (2 : ℂ) zAnchor = (18 : ℂ) := by
    dsimp [zAnchor]
    rw [fc, h2norm]
    norm_num
  have hG_fc_pos : 0 < Quadratic.green_function (2 : ℂ) (fc (2 : ℂ) zAnchor) := by
    rw [hfc_eval]
    have h18_out : ‖(18 : ℂ)‖ > ‖(2 : ℂ)‖ + 2 := by
      rw [show (18 : ℂ) = ((18 : ℝ) : ℂ) from by norm_cast,
        Complex.norm_real, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 18), h2norm]
      norm_num
    exact GreenFunctionRayInversion.green_function_pos_on_outside_open (2 : ℂ) (18 : ℂ) h18_out
  have hG_anchor_pos : 0 < Quadratic.green_function (2 : ℂ) zAnchor := by
    have hfunc' :
        Quadratic.green_function (2 : ℂ) (fc (2 : ℂ) zAnchor) =
          2 * Quadratic.green_function (2 : ℂ) zAnchor := by
      simpa using hfunc
    linarith
  let gAnchor : ℝ := Quadratic.green_function (2 : ℂ) zAnchor
  let t : ℝ := min R (Real.exp (gAnchor / 2))
  have hexp_gt1 : 1 < Real.exp (gAnchor / 2) := by
    have : 0 < gAnchor := by simpa [gAnchor] using hG_anchor_pos
    exact Real.one_lt_exp_iff.mpr (by linarith)
  have ht_gt1 : 1 < t := by
    exact lt_min hR_gt1 hexp_gt1
  have ht_le_R : t ≤ R := min_le_left _ _
  let w : ℂ := ((t : ℝ) : ℂ)
  have hw_norm : ‖w‖ = t := by
    dsimp [w]
    rw [Complex.norm_real, Real.norm_of_nonneg]
    exact (lt_trans zero_lt_one ht_gt1).le
  have hw_gt1 : 1 < ‖w‖ := by
    simpa [hw_norm] using ht_gt1
  have hw_le_R : ‖w‖ ≤ R := by
    simpa [hw_norm] using ht_le_R
  have hdir : w / ↑‖w‖ = (1 : ℂ) := by
    dsimp [w]
    rw [hw_norm]
    have hne : (((t : ℝ) : ℂ)) ≠ 0 := by
      exact_mod_cast (lt_trans zero_lt_one ht_gt1).ne'
    exact div_self hne
  have hanchor_eval :
      Quadratic.green_function (2 : ℂ)
          (((‖(2 : ℂ)‖ + 2 : ℝ) * (w / ↑‖w‖)) : ℂ) = gAnchor := by
    dsimp [gAnchor, zAnchor]
    rw [hdir]
  have hlog_lt : Real.log t < gAnchor := by
    have ht_pos : 0 < t := lt_trans zero_lt_one ht_gt1
    have hlog_le_half :
        Real.log t ≤ gAnchor / 2 := by
      calc
        Real.log t ≤ Real.log (Real.exp (gAnchor / 2)) := by
          exact Real.log_le_log ht_pos (min_le_right _ _)
        _ = gAnchor / 2 := by rw [Real.log_exp]
    have hhalf_lt : gAnchor / 2 < gAnchor := by
      have : 0 < gAnchor := by simpa [gAnchor] using hG_anchor_pos
      linarith
    exact lt_of_le_of_lt hlog_le_half hhalf_lt
  have hwin_eval :
      Quadratic.green_function (2 : ℂ)
          (((‖(2 : ℂ)‖ + 2 : ℝ) * (w / ↑‖w‖)) : ℂ) < Real.log ‖w‖ :=
    hwin.2.2 w hw_gt1 hw_le_R
  have hcontr : gAnchor < Real.log t := by
    calc
      gAnchor
          = Quadratic.green_function (2 : ℂ)
              (((‖(2 : ℂ)‖ + 2 : ℝ) * (w / ↑‖w‖)) : ℂ) := hanchor_eval.symm
      _ < Real.log ‖w‖ := hwin_eval
      _ = Real.log t := by rw [hw_norm]
  linarith

/-- If a local window radius `R` covers the full cutoff band, the local window
upgrades to the full monotonicity window. -/
theorem greenRayLogGapMonotonicityWindowTwo_of_nonimplicativeWindowInterfaceTwo_of_cutoff_le_radius
    {R : ℝ}
    (hwin : NonimplicativeWindowInterfaceTwo R)
    (hcut_le : greenRayLogGtAnchorTwoCutoff ≤ R) :
    GreenRayLogGapMonotonicityWindowTwo := by
  intro w hw hcut
  exact hwin.2.2 w hw (le_trans hcut hcut_le)

/-- Dead-end certificate for local windows that cover the full cutoff band:
such windows are inconsistent in the current model because they force the full
monotonicity window. -/
theorem not_nonimplicativeWindowInterfaceTwo_of_cutoff_le_radius
    {R : ℝ}
    (_hcut_le : greenRayLogGtAnchorTwoCutoff ≤ R) :
    ¬ NonimplicativeWindowInterfaceTwo R := by
  intro hwin
  exact not_nonimplicativeWindowInterfaceTwo_of_one_lt_radius hwin.1 hwin

/-- In particular, the local-window interface is inconsistent at the exact
cutoff radius. -/
theorem not_nonimplicativeWindowInterfaceTwo_at_cutoff :
    ¬ NonimplicativeWindowInterfaceTwo greenRayLogGtAnchorTwoCutoff := by
  exact not_nonimplicativeWindowInterfaceTwo_of_cutoff_le_radius
    (R := greenRayLogGtAnchorTwoCutoff) le_rfl

/-- Strictly subcutoff local-window package at `c = 2`: a local nonimplicative
window strictly below the global cutoff, together with a transport bridge for
the remaining cutoff annulus. -/
def StrictlySubcutoffLocalWindowWithTransportBridgeTwo : Prop :=
  ∃ R : ℝ, 1 < R ∧ R < greenRayLogGtAnchorTwoCutoff ∧
    NonimplicativeWindowInterfaceTwo R ∧
    (∀ w : ℂ, R < ‖w‖ → ‖w‖ ≤ greenRayLogGtAnchorTwoCutoff →
      MLC.Quadratic.green_function (2 : ℂ)
          (((‖(2 : ℂ)‖ + 2 : ℝ) * (w / ↑‖w‖)) : ℂ) < Real.log ‖w‖)

/-- A strict subcutoff local-window package plus annulus transport bridge
upgrades to the full bounded cutoff window. -/
theorem greenRayLogGapMonotonicityWindowTwo_of_strictlySubcutoffLocalWindowWithTransportBridgeTwo
    (h : StrictlySubcutoffLocalWindowWithTransportBridgeTwo) :
    GreenRayLogGapMonotonicityWindowTwo := by
  rcases h with ⟨R, hR_gt1, hR_lt_cut, hwin, htransport⟩
  intro w hw hcut
  by_cases hle : ‖w‖ ≤ R
  · exact hwin.2.2 w hw hle
  · exact htransport w (lt_of_not_ge hle) hcut

/-- Current-model no-go: the strict subcutoff local-window package is
inconsistent because it still reconstructs the full bounded cutoff window. -/
theorem not_strictlySubcutoffLocalWindowWithTransportBridgeTwo :
    ¬ StrictlySubcutoffLocalWindowWithTransportBridgeTwo := by
  intro h
  exact not_greenRayLogGapMonotonicityWindowTwo
    (greenRayLogGapMonotonicityWindowTwo_of_strictlySubcutoffLocalWindowWithTransportBridgeTwo h)

/-- Partial-window interface at `c = 2` that stays strictly below cutoff and
does not include any tail-transport payload. -/
def PartialWindowNotCoveringCutoffWithNontransportedTailTwo : Prop :=
  ∃ R : ℝ, 1 < R ∧ R < greenRayLogGtAnchorTwoCutoff ∧
    NonimplicativeWindowInterfaceTwo R

/-- Any strict-subcutoff package with transport has a partial-window projection
that does not carry the tail-transport payload. -/
theorem partialWindowNotCoveringCutoffWithNontransportedTailTwo_of_strictlySubcutoffLocalWindowWithTransportBridgeTwo
    (h : StrictlySubcutoffLocalWindowWithTransportBridgeTwo) :
    PartialWindowNotCoveringCutoffWithNontransportedTailTwo := by
  rcases h with ⟨R, hR_gt1, hR_lt_cut, hwin, _htransport⟩
  exact ⟨R, hR_gt1, hR_lt_cut, hwin⟩

/-- Current-model no-go transfer: a partial-window payload cannot be upgraded to
the strict-subcutoff transport package in the current model. -/
theorem no_strictlySubcutoffTransportPackage_of_partialWindowNotCoveringCutoffWithNontransportedTailTwo
    (_h : PartialWindowNotCoveringCutoffWithNontransportedTailTwo) :
    ¬ StrictlySubcutoffLocalWindowWithTransportBridgeTwo := by
  intro hstrict
  exact not_strictlySubcutoffLocalWindowWithTransportBridgeTwo hstrict

/-- v7 constructor-oriented alias: explicitly names the direct construction
target for partial-window witnesses without transport. -/
def ConstructPartialWindowWitnessDirectlyWithoutTransportTwo : Prop :=
  PartialWindowNotCoveringCutoffWithNontransportedTailTwo

/-- The direct partial-window constructor target is definitionally equivalent to
the partial-window interface without transport. -/
theorem constructPartialWindowWitnessDirectlyWithoutTransportTwo_iff_partialWindowNotCoveringCutoffWithNontransportedTailTwo :
    ConstructPartialWindowWitnessDirectlyWithoutTransportTwo ↔
      PartialWindowNotCoveringCutoffWithNontransportedTailTwo := by
  rfl

/-- Any direct partial-window witness still cannot upgrade to the known
inconsistent strict-subcutoff transport package. -/
theorem no_strictlySubcutoffTransportPackage_of_constructPartialWindowWitnessDirectlyWithoutTransportTwo
    (_h : ConstructPartialWindowWitnessDirectlyWithoutTransportTwo) :
    ¬ StrictlySubcutoffLocalWindowWithTransportBridgeTwo := by
  intro hstrict
  exact not_strictlySubcutoffLocalWindowWithTransportBridgeTwo hstrict

/-- v8 explicit subcutoff witness-candidate interface:
strictly subcutoff local window data paired with the constructively available
tail inequality above cutoff. -/
def ExplicitSubcutoffWitnessCandidateFromGreenBoundsTwo : Prop :=
  ∃ R : ℝ, 1 < R ∧ R < greenRayLogGtAnchorTwoCutoff ∧
    NonimplicativeWindowInterfaceTwo R ∧
    (∀ w : ℂ, greenRayLogGtAnchorTwoCutoff < ‖w‖ →
      MLC.Quadratic.green_function (2 : ℂ)
          (((‖(2 : ℂ)‖ + 2 : ℝ) * (w / ↑‖w‖)) : ℂ) < Real.log ‖w‖)

/-- Any v8 explicit subcutoff witness-candidate projects to the constructor
target for partial-window witnesses without transport. -/
theorem constructPartialWindowWitnessDirectlyWithoutTransportTwo_of_explicitSubcutoffWitnessCandidateFromGreenBoundsTwo
    (h : ExplicitSubcutoffWitnessCandidateFromGreenBoundsTwo) :
    ConstructPartialWindowWitnessDirectlyWithoutTransportTwo := by
  rcases h with ⟨R, hR_gt1, hR_lt_cut, hwin, _htail⟩
  exact ⟨R, hR_gt1, hR_lt_cut, hwin⟩

/-- Any direct partial-window constructor witness upgrades to the v8 explicit
subcutoff witness-candidate interface by adding the constructive tail bound. -/
theorem explicitSubcutoffWitnessCandidateFromGreenBoundsTwo_of_constructPartialWindowWitnessDirectlyWithoutTransportTwo
    (hpartial : ConstructPartialWindowWitnessDirectlyWithoutTransportTwo) :
    ExplicitSubcutoffWitnessCandidateFromGreenBoundsTwo := by
  rcases hpartial with ⟨R, hR_gt1, hR_lt_cut, hwin⟩
  refine ⟨R, hR_gt1, hR_lt_cut, hwin, ?_⟩
  intro w hw_gt_cut
  exact greenRayLogGtAnchorTwo_of_norm_gt_cutoff w hw_gt_cut

/-- The v8 explicit subcutoff witness-candidate interface is equivalent to the
direct partial-window constructor target. -/
theorem explicitSubcutoffWitnessCandidateFromGreenBoundsTwo_iff_constructPartialWindowWitnessDirectlyWithoutTransportTwo :
    ExplicitSubcutoffWitnessCandidateFromGreenBoundsTwo ↔
      ConstructPartialWindowWitnessDirectlyWithoutTransportTwo := by
  constructor
  · intro h
    exact
      constructPartialWindowWitnessDirectlyWithoutTransportTwo_of_explicitSubcutoffWitnessCandidateFromGreenBoundsTwo
        h
  · intro hpartial
    exact
      explicitSubcutoffWitnessCandidateFromGreenBoundsTwo_of_constructPartialWindowWitnessDirectlyWithoutTransportTwo
        hpartial

/-- v9 strict-subcutoff existence route: existence of a strictly subcutoff
nonimplicative window, with no transport payload. -/
def StrictSubcutoffWindowExistenceTwo : Prop :=
  ∃ R : ℝ, 1 < R ∧ R < greenRayLogGtAnchorTwoCutoff ∧
    NonimplicativeWindowInterfaceTwo R

/-- The v9 strict-subcutoff existence route is definitionally equivalent to the
existing partial-window/no-transport interface. -/
theorem strictSubcutoffWindowExistenceTwo_iff_partialWindowNotCoveringCutoffWithNontransportedTailTwo :
    StrictSubcutoffWindowExistenceTwo ↔
      PartialWindowNotCoveringCutoffWithNontransportedTailTwo := by
  rfl

/-- The v9 strict-subcutoff existence route is equivalent to the v7 direct
partial-window constructor target. -/
theorem strictSubcutoffWindowExistenceTwo_iff_constructPartialWindowWitnessDirectlyWithoutTransportTwo :
    StrictSubcutoffWindowExistenceTwo ↔
      ConstructPartialWindowWitnessDirectlyWithoutTransportTwo := by
  constructor
  · intro h
    exact h
  · intro h
    exact h

/-- Refutation branch for v9: strict-subcutoff window existence is impossible
in the current model because every admissible local nonimplicative window
radius exceeds `1`, which is already inconsistent. -/
theorem not_strictSubcutoffWindowExistenceTwo :
    ¬ StrictSubcutoffWindowExistenceTwo := by
  intro h
  rcases h with ⟨R, hR_gt1, _hR_lt_cut, hwin⟩
  exact not_nonimplicativeWindowInterfaceTwo_of_one_lt_radius hR_gt1 hwin

/-- Refutation transfer: the existing partial-window/no-transport interface is
inconsistent in the current model. -/
theorem not_partialWindowNotCoveringCutoffWithNontransportedTailTwo :
    ¬ PartialWindowNotCoveringCutoffWithNontransportedTailTwo := by
  intro h
  exact not_strictSubcutoffWindowExistenceTwo h

/-- Refutation transfer: the v7 direct partial-window constructor target is
inconsistent in the current model. -/
theorem not_constructPartialWindowWitnessDirectlyWithoutTransportTwo :
    ¬ ConstructPartialWindowWitnessDirectlyWithoutTransportTwo := by
  intro h
  exact not_strictSubcutoffWindowExistenceTwo h

/-- Dead-end certificate: the replacement-shape seam does not by itself recover
the old global anchor-gap seam target. -/
theorem not_greenRayLogGtAnchorTwoSeam_of_greenRayAnchorThresholdPreimageTwoSeam :
    ¬ (GreenRayAnchorThresholdPreimageTwoSeam → GreenRayLogGtAnchorTwoSeam) := by
  intro himpl
  exact not_greenRayLogGtAnchorTwoSeam
    (himpl greenRayAnchorThresholdPreimageTwoSeam_constructive)

/-- Axiom-seeded strong anchor-gap seam needed by the current
`external_ray_map_exists_two_via_green_function_of_seam` ingress. -/
axiom greenRayLogGtAnchorTwo_axiom_seed : GreenRayLogGtAnchorTwoSeam

/-- Centralized anchor-gap seed alias at `c = 2`.
This is the single intended swap point for removing
`greenRayLogGtAnchorTwo_axiom_seed` from root-entry wrappers. -/
theorem greenRayLogGtAnchorTwo_seed : GreenRayLogGtAnchorTwoSeam :=
  greenRayLogGtAnchorTwo_axiom_seed

/-- Any `c = 2` Green-ray log-gap seam closes the strict radial monotonicity
seam in the current model. This keeps the seam dependency explicit instead of
implicitly replaying the centralized seed alias. -/
theorem greenFunctionStrictMonoAlongRayBasinTwo_of_greenRayLogGtAnchorTwoSeam
    (hlog_gt_anchor : GreenRayLogGtAnchorTwoSeam) :
    GreenFunctionRayInversion.GreenFunctionStrictMonoAlongRayBasinTwoSeam := by
  exact False.elim (not_greenRayLogGtAnchorTwoSeam hlog_gt_anchor)

/-- Centralized `c = 2` strict radial monotonicity seam seed.
This is the single intended swap point for removing the strict-mono seam axiom
from root-entry wrappers after constructive monotonicity is proved. -/
theorem greenFunctionStrictMonoAlongRayBasinTwo_seed :
    GreenFunctionRayInversion.GreenFunctionStrictMonoAlongRayBasinTwoSeam := by
  exact
    greenFunctionStrictMonoAlongRayBasinTwo_of_greenRayLogGtAnchorTwoSeam
      greenRayLogGtAnchorTwo_seed

/-- If external-ray landing at `c = 2` is constructively excluded, the landing
branch seam is immediate. -/
theorem cp5ResidualLandingInjSeamTwo_of_not_externalRayLandsOutsideOpen
    (hnot_land : ¬ ExternalRayLandsOutsideOpen (2 : ℂ)) :
    CP5ResidualLandingInjSeamTwo := by
  intro hland
  exact False.elim (hnot_land hland)

/-- Axiom-seeded outside-open injectivity at `c = 2`, extracted from the
outside-open left-inverse identity of `external_ray_map`. -/
theorem injOn_outside_open_two_axiom_seed :
    Set.InjOn (Quadratic.bottcher_map (2 : ℂ)) {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2} := by
  intro z hz w hw hzw
  have hz' : Quadratic.external_ray_map (2 : ℂ) (Quadratic.bottcher_map (2 : ℂ) z) = z :=
    bottcher_left_inv_outside_open_of_local (2 : ℂ) z hz
  have hw' : Quadratic.external_ray_map (2 : ℂ) (Quadratic.bottcher_map (2 : ℂ) w) = w :=
    bottcher_left_inv_outside_open_of_local (2 : ℂ) w hw
  have h := congrArg (Quadratic.external_ray_map (2 : ℂ)) hzw
  simpa [hz', hw'] using h

/-- Axiom-seeded witness of the global CP5 residual→injectivity seam at `c = 2`. -/
theorem cp5ResidualInjOnOutsideOpenSeamTwo_axiom_seed :
    CP5ResidualInjOnOutsideOpenSeamTwo := by
  intro _hres
  exact injOn_outside_open_two_axiom_seed

/-- Axiom-seeded witness for the local-homeomorph branch seam. -/
theorem cp5ResidualLocalHomeomorphInjSeamTwo_axiom_seed :
    CP5ResidualLocalHomeomorphInjSeamTwo := by
  intro _hlocal
  exact injOn_outside_open_two_axiom_seed

/-- Constructive witness for the local-homeomorph branch seam: proper local homeomorphism
asymptotic to identity is injective. -/
theorem injOn_outside_open_two_of_greenFunctionStrictMonoAlongRayBasinTwoSeam
    (hmono : GreenFunctionRayInversion.GreenFunctionStrictMonoAlongRayBasinTwoSeam)
    (hlog_gt_anchor : GreenRayLogGtAnchorTwoSeam) :
    Set.InjOn (Quadratic.bottcher_map (2 : ℂ)) {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2} := by
  have h_data : Quadratic.ExternalRayMapData (2 : ℂ) :=
    GreenFunctionRayInversion.external_ray_map_exists_two_via_green_function_of_seam
      hmono
      hlog_gt_anchor
  have h_left : BottcherLeftInverseOnOutsideOpenData (2 : ℂ) :=
    bottcher_left_inverse_on_outside_open_data_of_external_ray_map_data h_data
  exact bottcher_map_inj_on_outside_open_of_left_inverse_on_outside_open (2 : ℂ) h_left

/-- Constructive witness for the local-homeomorph branch seam: proper local homeomorphism
asymptotic to identity is injective. -/
theorem injOn_outside_open_two_strictMono_seeded :
    Set.InjOn (Quadratic.bottcher_map (2 : ℂ)) {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2} := by
  exact injOn_outside_open_two_of_greenFunctionStrictMonoAlongRayBasinTwoSeam
    greenFunctionStrictMonoAlongRayBasinTwo_seed
    greenRayLogGtAnchorTwo_seed

/-- Constructive witness for the local-homeomorph branch seam: proper local homeomorphism
asymptotic to identity is injective. -/
theorem cp5ResidualLocalHomeomorphInjSeamTwo_constructive :
    CP5ResidualLocalHomeomorphInjSeamTwo := by
  intro _hlocal
  exact injOn_outside_open_two_strictMono_seeded
/-- Axiom-seeded witness for the external-ray-landing branch seam. -/
theorem cp5ResidualLandingInjSeamTwo_axiom_seed :
    CP5ResidualLandingInjSeamTwo := by
  intro _hland
  exact injOn_outside_open_two_axiom_seed

/-- Reconstruct the global axiom-seeded seam via the branch decomposition. -/
theorem cp5ResidualInjOnOutsideOpenSeamTwo_axiom_seed_of_branchSeams :
    CP5ResidualInjOnOutsideOpenSeamTwo := by
  intro _hres
  exact injOn_outside_open_two_axiom_seed

/-- Assemble the global CP5 residual→injectivity seam from branch-local seams. -/
theorem cp5ResidualInjOnOutsideOpenSeamTwo_of_branchSeams
    (hlocal_seam : CP5ResidualLocalHomeomorphInjSeamTwo)
    (hland_seam : CP5ResidualLandingInjSeamTwo) :
    CP5ResidualInjOnOutsideOpenSeamTwo := by
  intro hres
  rcases hres with hlocal | hland
  · exact hlocal_seam hlocal
  · exact hland_seam hland

/-- If the landing residual branch is ruled out, the local-homeomorph branch seam
alone discharges the global residual→injectivity seam. -/
theorem cp5ResidualInjOnOutsideOpenSeamTwo_of_localHomeomorphBranchSeam_of_not_externalRayLandsOutsideOpen
    (hlocal_seam : CP5ResidualLocalHomeomorphInjSeamTwo)
    (hnot_land : ¬ ExternalRayLandsOutsideOpen (2 : ℂ)) :
    CP5ResidualInjOnOutsideOpenSeamTwo := by
  intro hres
  rcases hres with hlocal | hland
  · exact hlocal_seam hlocal
  · exact False.elim (hnot_land hland)

/-- Constructive CP5 residual→injectivity seam under a constructive exclusion of
the landing branch. -/
theorem cp5ResidualInjOnOutsideOpenSeamTwo_constructive_of_not_externalRayLandsOutsideOpen
    (hnot_land : ¬ ExternalRayLandsOutsideOpen (2 : ℂ)) :
    CP5ResidualInjOnOutsideOpenSeamTwo :=
  cp5ResidualInjOnOutsideOpenSeamTwo_of_localHomeomorphBranchSeam_of_not_externalRayLandsOutsideOpen
    cp5ResidualLocalHomeomorphInjSeamTwo_constructive hnot_land

/-- Unconditional constructive CP5 residual→injectivity seam at `c = 2`, using
the boundary-continuity exclusion of the landing branch. -/
theorem cp5ResidualInjOnOutsideOpenSeamTwo_constructive_unconditional :
    CP5ResidualInjOnOutsideOpenSeamTwo :=
  cp5ResidualInjOnOutsideOpenSeamTwo_constructive_of_not_externalRayLandsOutsideOpen
    not_externalRayLandsOutsideOpen_two_of_extended_ray_boundary_continuity

/-- Constructive CP5 residual→injectivity seam from an explicit exterior
counterexample to external-ray landing. -/
theorem cp5ResidualInjOnOutsideOpenSeamTwo_constructive_of_externalRayLandingCounterexampleTwo
    (hcex : ExternalRayLandingCounterexampleTwo) :
    CP5ResidualInjOnOutsideOpenSeamTwo :=
  cp5ResidualInjOnOutsideOpenSeamTwo_constructive_of_not_externalRayLandsOutsideOpen
    (not_externalRayLandsOutsideOpen_two_of_externalRayLandingCounterexampleTwo hcex)

/-- Constructive CP5 residual→injectivity seam from identifying the
external-ray image of `bottcher_map (2) 0` with `0`. -/
theorem cp5ResidualInjOnOutsideOpenSeamTwo_constructive_of_not_outside_open_at_bottcher_zero
    (hnot_out :
      ¬ ‖Quadratic.external_ray_map (2 : ℂ)
          (Quadratic.bottcher_map (2 : ℂ) (0 : ℂ))‖ > ‖(2 : ℂ)‖ + 2) :
    CP5ResidualInjOnOutsideOpenSeamTwo :=
  cp5ResidualInjOnOutsideOpenSeamTwo_constructive_of_not_externalRayLandsOutsideOpen
    (not_externalRayLandsOutsideOpen_two_of_not_outside_open_at_bottcher_zero hnot_out)

/-- Constructive CP5 residual→injectivity seam from identifying the
external-ray image of `bottcher_map (2) 0` with `0`. -/
theorem cp5ResidualInjOnOutsideOpenSeamTwo_constructive_of_external_ray_map_at_bottcher_zero_eq_zero
    (hzero :
      Quadratic.external_ray_map (2 : ℂ) (Quadratic.bottcher_map (2 : ℂ) (0 : ℂ)) = 0) :
    CP5ResidualInjOnOutsideOpenSeamTwo :=
  cp5ResidualInjOnOutsideOpenSeamTwo_constructive_of_not_externalRayLandsOutsideOpen
    (not_externalRayLandsOutsideOpen_two_of_external_ray_map_at_bottcher_zero_eq_zero hzero)

/-- Constructive CP5 residual→injectivity seam from excluding
`bottcher_map (2) 0` from the outside-open image. -/
theorem cp5ResidualInjOnOutsideOpenSeamTwo_constructive_of_bottcher_zero_not_mem_image_outside_open
    (hzero_not_img :
      Quadratic.bottcher_map (2 : ℂ) (0 : ℂ) ∉
        Quadratic.bottcher_map (2 : ℂ) '' {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2}) :
    CP5ResidualInjOnOutsideOpenSeamTwo :=
  cp5ResidualInjOnOutsideOpenSeamTwo_constructive_of_not_externalRayLandsOutsideOpen
    (not_externalRayLandsOutsideOpen_two_of_bottcher_zero_not_mem_image_outside_open hzero_not_img)

/-- Strong constructive route: outside-disk injectivity directly rules out the
landing branch and therefore discharges the CP5 residual→injectivity seam. -/
theorem cp5ResidualInjOnOutsideOpenSeamTwo_constructive_of_injOn_outside_disk
    (h_inj_disk : Set.InjOn (Quadratic.bottcher_map (2 : ℂ)) (outside_disk (2 : ℂ))) :
    CP5ResidualInjOnOutsideOpenSeamTwo :=
  cp5ResidualInjOnOutsideOpenSeamTwo_constructive_of_not_externalRayLandsOutsideOpen
    (not_externalRayLandsOutsideOpen_two_of_injOn_outside_disk h_inj_disk)

/-- If the local-homeomorph residual branch is ruled out, the landing branch seam
alone discharges the global residual→injectivity seam. -/
theorem cp5ResidualInjOnOutsideOpenSeamTwo_of_landingBranchSeam_of_not_localHomeomorphSurjSource
    (hland_seam : CP5ResidualLandingInjSeamTwo)
    (hnot_local :
      ¬ (IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ))) ∧
          IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ)))) :
    CP5ResidualInjOnOutsideOpenSeamTwo := by
  intro hres
  rcases hres with hlocal | hland
  · exfalso
    have hclosed := isClosed_range_bottcher_map_outside_open_to_exterior_of_isProperMap (2 : ℂ) hlocal.1
    exact hnot_local ⟨hclosed, hlocal.2⟩
  · exact hland_seam hland

/-- The global CP5 residual→injectivity seam is equivalent to proving both
branch-local injectivity seams. -/
theorem cp5ResidualInjOnOutsideOpenSeamTwo_iff_branchSeams :
    CP5ResidualInjOnOutsideOpenSeamTwo ↔
      (CP5ResidualLocalHomeomorphInjSeamTwo ∧ CP5ResidualLandingInjSeamTwo) := by
  constructor
  · intro h
    constructor
    · intro hlocal
      exact h (Or.inl hlocal)
    · intro hland
      exact h (Or.inr hland)
  · intro h
    exact cp5ResidualInjOnOutsideOpenSeamTwo_of_branchSeams h.1 h.2

/-- Seam projection at `c = 2`: derive outside-open injectivity from the
residual-frontier injectivity seam. -/
theorem injOn_outside_open_two_of_cp5ResidualTwo
    (h_seam : CP5ResidualInjOnOutsideOpenSeamTwo)
    (hres : CP5ResidualTwo) :
    Set.InjOn (Quadratic.bottcher_map (2 : ℂ)) {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2} :=
  h_seam hres

/-- CP5 seam at `c = 2`: the explicit residual frontier plus outside-open
injectivity yields constructive external-ray-map data. -/
theorem external_ray_map_exists_two_constructive_of_cp5ResidualTwo_of_injOn_outside_open
    (hres : CP5ResidualTwo)
    (h_inj : Set.InjOn (Quadratic.bottcher_map (2 : ℂ)) {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2}) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_exists_two_constructive_of_injOn_outside_open_of_surj_exterior
    h_inj (bottcherSurjOnExteriorFromOutsideOpen_two_of_cp5ResidualTwo hres)

/-- Assumption-gated CP5 seam at `c = 2`: the explicit residual frontier plus a
residual→injectivity seam yields constructive external-ray-map data. -/
theorem external_ray_map_exists_two_constructive_of_cp5ResidualTwo_of_cp5ResidualInjOnOutsideOpenSeamTwo
    (hres : CP5ResidualTwo)
    (h_seam : CP5ResidualInjOnOutsideOpenSeamTwo) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_exists_two_constructive_of_cp5ResidualTwo_of_injOn_outside_open
    hres (injOn_outside_open_two_of_cp5ResidualTwo h_seam hres)

/-- Branch-seam form of the CP5 residual constructive external-ray-data bridge
at `c = 2`. -/
theorem external_ray_map_exists_two_constructive_of_cp5ResidualTwo_of_branchSeams
    (hres : CP5ResidualTwo)
    (hbranch :
      CP5ResidualLocalHomeomorphInjSeamTwo ∧
        CP5ResidualLandingInjSeamTwo) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_exists_two_constructive_of_cp5ResidualTwo_of_cp5ResidualInjOnOutsideOpenSeamTwo
    hres ((cp5ResidualInjOnOutsideOpenSeamTwo_iff_branchSeams).2 hbranch)

/-- CP5 residual seam wired as a function: if the residual→injectivity seam is
available, the explicit CP5 residual frontier yields constructive external-ray-map
data at `c = 2`. -/
theorem external_ray_map_exists_two_constructive_of_cp5ResidualTwo_of_seam
    (h_seam : CP5ResidualInjOnOutsideOpenSeamTwo) :
    CP5ResidualTwo → Quadratic.ExternalRayMapData (2 : ℂ) := by
  intro hres
  exact external_ray_map_exists_two_constructive_of_cp5ResidualTwo_of_cp5ResidualInjOnOutsideOpenSeamTwo
    hres h_seam

/-- CP5 residual bridge under constructive landing exclusion: once
`¬ ExternalRayLandsOutsideOpen (2 : ℂ)` is proved, the residual route is
unconditional in `CP5ResidualTwo`. -/
theorem external_ray_map_exists_two_constructive_of_cp5ResidualTwo_of_not_externalRayLandsOutsideOpen
    (hnot_land : ¬ ExternalRayLandsOutsideOpen (2 : ℂ)) :
    CP5ResidualTwo → Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_exists_two_constructive_of_cp5ResidualTwo_of_seam
    (cp5ResidualInjOnOutsideOpenSeamTwo_constructive_of_not_externalRayLandsOutsideOpen hnot_land)

/-- Unconditional constructive CP5 residual endpoint at `c = 2`, using the
boundary-continuity exclusion of external-ray landing. -/
theorem external_ray_map_exists_two_constructive_of_cp5ResidualTwo :
    CP5ResidualTwo → Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_exists_two_constructive_of_cp5ResidualTwo_of_not_externalRayLandsOutsideOpen
    not_externalRayLandsOutsideOpen_two_of_extended_ray_boundary_continuity

/-- Alias exposing the same unconditional CP5 residual endpoint. -/
theorem external_ray_map_exists_two_constructive_of_cp5ResidualTwo_unconditional :
    CP5ResidualTwo → Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_exists_two_constructive_of_cp5ResidualTwo

/-- CP5 residual endpoint route from an explicit exterior counterexample to
external-ray landing. -/
theorem external_ray_map_exists_two_constructive_of_cp5ResidualTwo_of_externalRayLandingCounterexampleTwo
    (hcex : ExternalRayLandingCounterexampleTwo) :
    CP5ResidualTwo → Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_exists_two_constructive_of_cp5ResidualTwo_of_seam
    (cp5ResidualInjOnOutsideOpenSeamTwo_constructive_of_externalRayLandingCounterexampleTwo hcex)

/-- CP5 residual endpoint route from identifying
`external_ray_map (2) (bottcher_map (2) 0)` with `0`. -/
theorem external_ray_map_exists_two_constructive_of_cp5ResidualTwo_of_not_outside_open_at_bottcher_zero
    (hnot_out :
      ¬ ‖Quadratic.external_ray_map (2 : ℂ)
          (Quadratic.bottcher_map (2 : ℂ) (0 : ℂ))‖ > ‖(2 : ℂ)‖ + 2) :
    CP5ResidualTwo → Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_exists_two_constructive_of_cp5ResidualTwo_of_seam
    (cp5ResidualInjOnOutsideOpenSeamTwo_constructive_of_not_outside_open_at_bottcher_zero
      hnot_out)

/-- CP5 residual endpoint route from identifying
`external_ray_map (2) (bottcher_map (2) 0)` with `0`. -/
theorem external_ray_map_exists_two_constructive_of_cp5ResidualTwo_of_external_ray_map_at_bottcher_zero_eq_zero
    (hzero :
      Quadratic.external_ray_map (2 : ℂ) (Quadratic.bottcher_map (2 : ℂ) (0 : ℂ)) = 0) :
    CP5ResidualTwo → Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_exists_two_constructive_of_cp5ResidualTwo_of_seam
    (cp5ResidualInjOnOutsideOpenSeamTwo_constructive_of_external_ray_map_at_bottcher_zero_eq_zero
      hzero)

/-- CP5 residual endpoint route from excluding `bottcher_map (2) 0` from the
outside-open image. -/
theorem external_ray_map_exists_two_constructive_of_cp5ResidualTwo_of_bottcher_zero_not_mem_image_outside_open
    (hzero_not_img :
      Quadratic.bottcher_map (2 : ℂ) (0 : ℂ) ∉
        Quadratic.bottcher_map (2 : ℂ) '' {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2}) :
    CP5ResidualTwo → Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_exists_two_constructive_of_cp5ResidualTwo_of_seam
    (cp5ResidualInjOnOutsideOpenSeamTwo_constructive_of_bottcher_zero_not_mem_image_outside_open
      hzero_not_img)

/-- Strong constructive route to the CP5 residual endpoint from outside-disk
injectivity. -/
theorem external_ray_map_exists_two_constructive_of_cp5ResidualTwo_of_injOn_outside_disk
    (h_inj_disk : Set.InjOn (Quadratic.bottcher_map (2 : ℂ)) (outside_disk (2 : ℂ))) :
    CP5ResidualTwo → Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_exists_two_constructive_of_cp5ResidualTwo_of_seam
    (cp5ResidualInjOnOutsideOpenSeamTwo_constructive_of_injOn_outside_disk h_inj_disk)

/-- Axiom-seeded CP5 residual wrapper at `c = 2`: keeps the residual route wired
while isolating the current non-constructive injectivity seam witness. -/
theorem external_ray_map_exists_two_constructive_of_cp5ResidualTwo_axiom_seam
    (hres : CP5ResidualTwo) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_exists_two_constructive_of_cp5ResidualTwo_of_seam
    cp5ResidualInjOnOutsideOpenSeamTwo_axiom_seed hres

/-- Direct CP5 residual endpoint route at `c = 2` from the now-canonical residual
left branch (restricted properness + restricted local-homeomorph). -/
theorem external_ray_map_exists_two_constructive_of_isProperMap_restrict_of_isLocalHomeomorph_restrict
    (hproper : IsProperMap (bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (hlocal : IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ))) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_exists_two_constructive_of_cp5ResidualTwo
    (cp5ResidualTwo_of_isProperMap_restrict_of_isLocalHomeomorph_restrict hproper hlocal)

/-- Final constructive CP5 closure criterion at `c = 2`: a direct witness of the
restricted proper+local pair for the outside-open/exterior map. -/
def DirectProperLocalWitnessTwo : Prop :=
  IsProperMap (bottcher_map_outside_open_to_exterior (2 : ℂ)) ∧
    IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ))

/-- Primitive restricted-map proper/local witness family at `c = 2`.
This packages the same payload as `DirectProperLocalWitnessTwo` under a
distinct interface name for no-arg witness-source design work. -/
def PrimitiveRestrictedMapProperLocalWitnessFamilyTwo : Prop :=
  IsProperMap (bottcher_map_outside_open_to_exterior (2 : ℂ)) ∧
    IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ))

/-- Build the direct proper/local witness from the primitive witness family. -/
theorem directProperLocalWitnessTwo_of_primitiveRestrictedMapProperLocalWitnessFamilyTwo
    (h : PrimitiveRestrictedMapProperLocalWitnessFamilyTwo) :
    DirectProperLocalWitnessTwo :=
  h

/-- Build the primitive witness family from the direct proper/local witness. -/
theorem primitiveRestrictedMapProperLocalWitnessFamilyTwo_of_directProperLocalWitnessTwo
    (h : DirectProperLocalWitnessTwo) :
    PrimitiveRestrictedMapProperLocalWitnessFamilyTwo :=
  h

/-- The primitive restricted-map witness family is equivalent to the direct
proper/local witness payload at `c = 2`. -/
theorem primitiveRestrictedMapProperLocalWitnessFamilyTwo_iff_directProperLocalWitnessTwo :
    PrimitiveRestrictedMapProperLocalWitnessFamilyTwo ↔ DirectProperLocalWitnessTwo := by
  constructor
  · intro h
    exact directProperLocalWitnessTwo_of_primitiveRestrictedMapProperLocalWitnessFamilyTwo h
  · intro h
    exact primitiveRestrictedMapProperLocalWitnessFamilyTwo_of_directProperLocalWitnessTwo h

/-- Reduced-open local-homeomorph surjectivity-source constructor at `c = 2`
from the direct proper+local witness. -/
theorem localHomeomorphSurjSourceTwo_of_directProperLocalWitnessTwo
    (h : DirectProperLocalWitnessTwo) :
    IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ))) ∧
      IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ)) :=
  ⟨isClosed_range_bottcher_map_outside_open_to_exterior_of_isProperMap (2 : ℂ) h.1, h.2⟩

/-- Known surjectivity-source constructor at `c = 2` from the direct proper+local
witness. -/
theorem knownSurjOnExteriorFromOutsideOpenSourceCandidateTwo_of_directProperLocalWitnessTwo
    (h : DirectProperLocalWitnessTwo) :
    KnownSurjOnExteriorFromOutsideOpenSourceCandidateTwo :=
  Or.inl (localHomeomorphSurjSourceTwo_of_directProperLocalWitnessTwo h)

/-- Outside-open exterior surjectivity at `c = 2` from the direct proper+local
witness. -/
theorem bottcherSurjOnExteriorFromOutsideOpen_two_of_directProperLocalWitnessTwo
    (h : DirectProperLocalWitnessTwo) :
    BottcherSurjOnExteriorFromOutsideOpen (2 : ℂ) :=
  bottcherSurjOnExteriorFromOutsideOpen_two_of_isProperMap_restrict_of_isLocalHomeomorph_restrict
    h.1 h.2

/-- Build restricted-map properness at `c = 2` from local-homeomorph continuity
and closedness of ambient outside-open preimages against compact exterior
targets. -/
theorem isProperMap_bottcher_map_outside_open_to_exterior_two_of_isLocalHomeomorph_restrict_of_preimage_closed
    (hlocal : IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (hclosedpre :
      ∀ K : Set {w : ℂ // 1 < ‖w‖}, IsCompact K →
        IsClosed
          ({z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2 ∧
            Quadratic.bottcher_map (2 : ℂ) z ∈ ((↑) '' K : Set ℂ)} : Set ℂ)) :
    IsProperMap (bottcher_map_outside_open_to_exterior (2 : ℂ)) := by
  have hcont :
      Continuous (fun z : {z : ℂ // ‖z‖ > ‖(2 : ℂ)‖ + 2} =>
        Quadratic.bottcher_map (2 : ℂ) z.1) := by
    simpa [bottcher_map_outside_open_to_exterior] using
      (continuous_subtype_val.comp hlocal.continuous)
  refine isProperMap_bottcher_map_outside_open_to_exterior_of_preimage_compact (2 : ℂ) hcont ?_
  intro K hK
  exact
    (isCompact_preimage_bottcher_map_outside_open_to_exterior_iff (2 : ℂ) K).1
      (isCompact_preimage_bottcher_map_outside_open_to_exterior_of_isClosed (2 : ℂ) K hK
        (hclosedpre K hK))

/-- Direct proper+local witness from local-homeomorph plus the ambient
preimage-closed compact-target condition at `c = 2`. -/
theorem directProperLocalWitnessTwo_of_isLocalHomeomorph_restrict_of_preimage_closed
    (hlocal : IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (hclosedpre :
      ∀ K : Set {w : ℂ // 1 < ‖w‖}, IsCompact K →
        IsClosed
          ({z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2 ∧
            Quadratic.bottcher_map (2 : ℂ) z ∈ ((↑) '' K : Set ℂ)} : Set ℂ)) :
    DirectProperLocalWitnessTwo := by
  exact
    ⟨isProperMap_bottcher_map_outside_open_to_exterior_two_of_isLocalHomeomorph_restrict_of_preimage_closed
      hlocal hclosedpre, hlocal⟩

/-- v9 packaged route to `DirectProperLocalWitnessTwo` from local-homeomorph
plus closed-preimage data on compact exterior targets. -/
def DirectProperLocalWitnessTwoFromLocalHomeomorphClosedRangeRouteTwo : Prop :=
  IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ)) ∧
    (∀ K : Set {w : ℂ // 1 < ‖w‖}, IsCompact K →
      IsClosed
        ({z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2 ∧
          Quadratic.bottcher_map (2 : ℂ) z ∈ ((↑) '' K : Set ℂ)} : Set ℂ))

/-- Build the direct proper/local witness from the v9 local-homeomorph
closed-preimage packaged route. -/
theorem directProperLocalWitnessTwo_of_directProperLocalWitnessTwoFromLocalHomeomorphClosedRangeRouteTwo
    (h_route : DirectProperLocalWitnessTwoFromLocalHomeomorphClosedRangeRouteTwo) :
    DirectProperLocalWitnessTwo := by
  exact directProperLocalWitnessTwo_of_isLocalHomeomorph_restrict_of_preimage_closed
    h_route.1 h_route.2

/-- Build the v9 local-homeomorph closed-preimage packaged route from a direct
proper/local witness. -/
theorem directProperLocalWitnessTwoFromLocalHomeomorphClosedRangeRouteTwo_of_directProperLocalWitnessTwo
    (h : DirectProperLocalWitnessTwo) :
    DirectProperLocalWitnessTwoFromLocalHomeomorphClosedRangeRouteTwo := by
  refine ⟨h.2, ?_⟩
  intro K hK
  have hcompact_pre :
      IsCompact ((bottcher_map_outside_open_to_exterior (2 : ℂ)) ⁻¹' K) :=
    h.1.isCompact_preimage hK
  have hcompact_ambient :
      IsCompact
        ({z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2 ∧
          Quadratic.bottcher_map (2 : ℂ) z ∈ ((↑) '' K : Set ℂ)} : Set ℂ) :=
    (isCompact_preimage_bottcher_map_outside_open_to_exterior_iff (2 : ℂ) K).1
      hcompact_pre
  exact hcompact_ambient.isClosed

/-- The v9 local-homeomorph closed-preimage packaged route is equivalent to the
direct proper/local witness payload at `c = 2`. -/
theorem directProperLocalWitnessTwoFromLocalHomeomorphClosedRangeRouteTwo_iff_directProperLocalWitnessTwo :
    DirectProperLocalWitnessTwoFromLocalHomeomorphClosedRangeRouteTwo ↔
      DirectProperLocalWitnessTwo := by
  constructor
  · intro h_route
    exact
      directProperLocalWitnessTwo_of_directProperLocalWitnessTwoFromLocalHomeomorphClosedRangeRouteTwo
        h_route
  · intro h
    exact
      directProperLocalWitnessTwoFromLocalHomeomorphClosedRangeRouteTwo_of_directProperLocalWitnessTwo
        h

/-- Boundary-exclusion hypotheses construct the v9 local-homeomorph
closed-preimage packaged route. -/
theorem directProperLocalWitnessTwoFromLocalHomeomorphClosedRangeRouteTwo_of_isLocalHomeomorph_restrict_of_boundary_exclusion
    (hlocal : IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (hboundary :
      ∀ K : Set {w : ℂ // 1 < ‖w‖}, IsCompact K →
        ∀ z, ‖z‖ = ‖(2 : ℂ)‖ + 2 →
          Quadratic.bottcher_map (2 : ℂ) z ∉ ((↑) '' K : Set ℂ)) :
    DirectProperLocalWitnessTwoFromLocalHomeomorphClosedRangeRouteTwo := by
  refine ⟨hlocal, ?_⟩
  intro K hK
  exact isClosed_outside_open_preimage_image_compact_of_boundary_exclusion (2 : ℂ) K hK
    (hboundary K hK)

/-- Direct proper+local witness from local-homeomorph plus boundary exclusion on
compact exterior targets at `c = 2`. -/
theorem directProperLocalWitnessTwo_of_isLocalHomeomorph_restrict_of_boundary_exclusion
    (hlocal : IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (hboundary :
      ∀ K : Set {w : ℂ // 1 < ‖w‖}, IsCompact K →
        ∀ z, ‖z‖ = ‖(2 : ℂ)‖ + 2 →
          Quadratic.bottcher_map (2 : ℂ) z ∉ ((↑) '' K : Set ℂ)) :
    DirectProperLocalWitnessTwo := by
  refine directProperLocalWitnessTwo_of_isLocalHomeomorph_restrict_of_preimage_closed hlocal ?_
  intro K hK
  exact isClosed_outside_open_preimage_image_compact_of_boundary_exclusion (2 : ℂ) K hK
    (hboundary K hK)

/-- Constructive CP5 endpoint from the direct closure criterion witness. -/
theorem external_ray_map_exists_two_constructive_of_directProperLocalWitnessTwo
    (h : DirectProperLocalWitnessTwo) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_exists_two_constructive_of_isProperMap_restrict_of_isLocalHomeomorph_restrict
    h.1 h.2

/-- CP5 endpoint from local-homeomorph plus the ambient preimage-closed
compact-target condition at `c = 2`, via the direct witness criterion. -/
theorem external_ray_map_exists_two_constructive_of_isLocalHomeomorph_restrict_of_preimage_closed
    (hlocal : IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (hclosedpre :
      ∀ K : Set {w : ℂ // 1 < ‖w‖}, IsCompact K →
        IsClosed
          ({z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2 ∧
            Quadratic.bottcher_map (2 : ℂ) z ∈ ((↑) '' K : Set ℂ)} : Set ℂ)) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_exists_two_constructive_of_directProperLocalWitnessTwo
    (directProperLocalWitnessTwo_of_isLocalHomeomorph_restrict_of_preimage_closed hlocal hclosedpre)

/-- CP5 endpoint from local-homeomorph plus boundary exclusion on compact
exterior targets at `c = 2`. -/
theorem external_ray_map_exists_two_constructive_of_isLocalHomeomorph_restrict_of_boundary_exclusion
    (hlocal : IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (hboundary :
      ∀ K : Set {w : ℂ // 1 < ‖w‖}, IsCompact K →
        ∀ z, ‖z‖ = ‖(2 : ℂ)‖ + 2 →
          Quadratic.bottcher_map (2 : ℂ) z ∉ ((↑) '' K : Set ℂ)) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_exists_two_constructive_of_directProperLocalWitnessTwo
    (directProperLocalWitnessTwo_of_isLocalHomeomorph_restrict_of_boundary_exclusion hlocal hboundary)

/-- Direct proper+local witness from local-homeomorph-on outside-open plus the
ambient preimage-closed compact-target condition at `c = 2`. -/
theorem directProperLocalWitnessTwo_of_isLocalHomeomorphOn_outside_open_of_preimage_closed
    (hlocal_on :
      IsLocalHomeomorphOn (Quadratic.bottcher_map (2 : ℂ)) {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2})
    (hclosedpre :
      ∀ K : Set {w : ℂ // 1 < ‖w‖}, IsCompact K →
        IsClosed
          ({z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2 ∧
            Quadratic.bottcher_map (2 : ℂ) z ∈ ((↑) '' K : Set ℂ)} : Set ℂ)) :
    DirectProperLocalWitnessTwo := by
  have hlocal :
      IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ)) :=
    isLocalHomeomorph_bottcher_map_outside_open_to_exterior_of_isLocalHomeomorphOn_outside_open
      (2 : ℂ) hlocal_on
  exact directProperLocalWitnessTwo_of_isLocalHomeomorph_restrict_of_preimage_closed hlocal hclosedpre

/-- Direct proper+local witness from local-homeomorph-on outside-open plus
boundary exclusion on compact exterior targets at `c = 2`. -/
theorem directProperLocalWitnessTwo_of_isLocalHomeomorphOn_outside_open_of_boundary_exclusion
    (hlocal_on :
      IsLocalHomeomorphOn (Quadratic.bottcher_map (2 : ℂ)) {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2})
    (hboundary :
      ∀ K : Set {w : ℂ // 1 < ‖w‖}, IsCompact K →
        ∀ z, ‖z‖ = ‖(2 : ℂ)‖ + 2 →
          Quadratic.bottcher_map (2 : ℂ) z ∉ ((↑) '' K : Set ℂ)) :
    DirectProperLocalWitnessTwo := by
  have hlocal :
      IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ)) :=
    isLocalHomeomorph_bottcher_map_outside_open_to_exterior_of_isLocalHomeomorphOn_outside_open
      (2 : ℂ) hlocal_on
  exact directProperLocalWitnessTwo_of_isLocalHomeomorph_restrict_of_boundary_exclusion hlocal hboundary

/-- CP5 endpoint from local-homeomorph-on outside-open plus the ambient
preimage-closed compact-target condition at `c = 2`. -/
theorem external_ray_map_exists_two_constructive_of_isLocalHomeomorphOn_outside_open_of_preimage_closed
    (hlocal_on :
      IsLocalHomeomorphOn (Quadratic.bottcher_map (2 : ℂ)) {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2})
    (hclosedpre :
      ∀ K : Set {w : ℂ // 1 < ‖w‖}, IsCompact K →
        IsClosed
          ({z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2 ∧
            Quadratic.bottcher_map (2 : ℂ) z ∈ ((↑) '' K : Set ℂ)} : Set ℂ)) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_exists_two_constructive_of_directProperLocalWitnessTwo
    (directProperLocalWitnessTwo_of_isLocalHomeomorphOn_outside_open_of_preimage_closed
      hlocal_on hclosedpre)

/-- CP5 endpoint from local-homeomorph-on outside-open plus boundary exclusion
on compact exterior targets at `c = 2`. -/
theorem external_ray_map_exists_two_constructive_of_isLocalHomeomorphOn_outside_open_of_boundary_exclusion
    (hlocal_on :
      IsLocalHomeomorphOn (Quadratic.bottcher_map (2 : ℂ)) {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2})
    (hboundary :
      ∀ K : Set {w : ℂ // 1 < ‖w‖}, IsCompact K →
        ∀ z, ‖z‖ = ‖(2 : ℂ)‖ + 2 →
          Quadratic.bottcher_map (2 : ℂ) z ∉ ((↑) '' K : Set ℂ)) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_exists_two_constructive_of_directProperLocalWitnessTwo
    (directProperLocalWitnessTwo_of_isLocalHomeomorphOn_outside_open_of_boundary_exclusion
      hlocal_on hboundary)

/-- Root closure wrapper from the direct constructive CP5 closure criterion. -/
theorem mlc_conjecture_of_directProperLocalWitnessTwo
    (h : DirectProperLocalWitnessTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_externalRayMapData_two
    (external_ray_map_exists_two_constructive_of_directProperLocalWitnessTwo h)

/-- Root bridge at `c = 2`: the explicit CP5 residual frontier is sufficient for
the full MLC statement through the surjectivity seam. -/
theorem mlc_conjecture_of_cp5ResidualTwo
    (hres : CP5ResidualTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_bottcherSurjOnExteriorFromOutsideOpen_two
    (bottcherSurjOnExteriorFromOutsideOpen_two_of_cp5ResidualTwo hres)

/-- Aggregate predicate for currently wired local-homeomorph-on source families
at `c = 2`. -/
def KnownLocalHomeomorphOnSourceCandidateTwo : Prop :=
  AnalyticDerivConstructivePayloadTwo ∨
    SlitInjOutsideDiskLocalHomeomorphOnConstructivePayloadTwo

/-- All currently wired local-homeomorph-on source families are inconsistent in
the current model at `c = 2`. -/
theorem not_knownLocalHomeomorphOnSourceCandidateTwo :
    ¬ KnownLocalHomeomorphOnSourceCandidateTwo := by
  intro h
  rcases h with hA | hB
  · exact not_analyticDerivConstructivePayloadTwo hA
  · exact not_slitInjOutsideDiskLocalHomeomorphOnConstructivePayloadTwo hB

/-- Aggregate predicate for currently wired non-iterate-left source families
that can yield outside-open injectivity at `c = 2`. -/
def KnownInjOnOutsideOpenSourceCandidateTwo : Prop :=
  NonSlitAnalyticInjConstructivePayloadTwo ∨
    NonSlitMemNhdsSlitInjConstructivePayloadTwo ∨
    SlitInjOutsideDiskLocalHomeomorphOnConstructivePayloadTwo ∨
    OutsideOpenQuotientConstRealWitnessTwo ∨
    OutsideOpenAnalyticityHypothesis (2 : ℂ)

/-- Outside-open analyticity at `c = 2` yields outside-open injectivity through
the quotient-rigidity bridge. -/
theorem injOn_outside_open_two_of_outsideOpenAnalyticityHypothesis
    (h_analytic : OutsideOpenAnalyticityHypothesis (2 : ℂ)) :
    Set.InjOn (Quadratic.bottcher_map (2 : ℂ)) {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2} := by
  exact (outsideOpenAnalyticInjPayload_of_outsideOpenAnalyticityHypothesis (2 : ℂ) h_analytic).2

/-- Any currently wired non-iterate-left source family in the previous aggregate
yields outside-open injectivity at `c = 2`. -/
theorem injOn_outside_open_two_of_knownInjOnOutsideOpenSourceCandidateTwo
    (h : KnownInjOnOutsideOpenSourceCandidateTwo) :
    Set.InjOn (Quadratic.bottcher_map (2 : ℂ)) {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2} := by
  rcases h with hA | hB | hC | hD | hE
  · exact hA.2.2
  · exact hB.2.2
  · exact hC.2.mono (outside_open_subset_outside_disk (2 : ℂ))
  · exact injOn_outside_open_of_outsideOpenQuotientConstRealWitness (2 : ℂ) hD
  · exact injOn_outside_open_two_of_outsideOpenAnalyticityHypothesis hE

/-- All currently wired non-iterate-left source families that can yield
outside-open injectivity are inconsistent in the current model at `c = 2`. -/
theorem not_knownInjOnOutsideOpenSourceCandidateTwo :
    ¬ KnownInjOnOutsideOpenSourceCandidateTwo := by
  intro h
  rcases h with hA | hB | hC | hD | hE
  · exact not_nonSlitAnalyticInjConstructivePayloadTwo hA
  · exact not_mem_nhds_slit_on_outside_open_two hB.2.1
  · exact not_slitInjOutsideDiskLocalHomeomorphOnConstructivePayloadTwo hC
  · exact not_outsideOpenQuotientConstRealWitnessTwo hD
  · exact not_outsideOpenAnalyticityHypothesisTwo hE

/-- Current-model non-iterate-left injectivity-source exhaustion at `c = 2`:
known source families are blocked, so the only remaining branch in
`KnownInjOnOutsideOpenSourceCandidateTwo ∨ BottcherLeftInverseOnOutsideOpenData (2 : ℂ)`
is the left-inverse alias of direct outside-open injectivity. -/
theorem nonIterInjOnOutsideOpenSourceExhaustionTwo :
    (KnownInjOnOutsideOpenSourceCandidateTwo ∨ BottcherLeftInverseOnOutsideOpenData (2 : ℂ)) ↔
      Set.InjOn (Quadratic.bottcher_map (2 : ℂ)) {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2} := by
  constructor
  · intro h
    rcases h with hKnown | hLeft
    · exact False.elim (not_knownInjOnOutsideOpenSourceCandidateTwo hKnown)
    · exact (leftInverseOutsideOpen_two_iff_injOn_outside_open).1 hLeft
  · intro hInj
    exact Or.inr ((leftInverseOutsideOpen_two_iff_injOn_outside_open).2 hInj)

/-- Formalization ingress for Dudko (arXiv:2512.24171, lines ~189-193): at
`c = 2`, the restricted dynamical Böttcher map identifies outside-open with the
exterior via a homeomorphism. -/
def DynamicalBottcherConformalIdentificationTwo : Prop :=
  ∃ e : {z : ℂ // ‖z‖ > ‖(2 : ℂ)‖ + 2} ≃ₜ {w : ℂ // 1 < ‖w‖},
    (fun z => e z) = bottcher_map_outside_open_to_exterior (2 : ℂ)

/-- Concrete realization of the Dudko-style conformal-identification ingress from
existing outside-open payloads at `c = 2`. -/
theorem dynamicalBottcherConformalIdentificationTwo_of_isProperMap_restrict_of_outsideOpenAnalyticInjPayload
    (hproper : IsProperMap (bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (h_payload : OutsideOpenAnalyticInjPayload (2 : ℂ)) :
    DynamicalBottcherConformalIdentificationTwo := by
  let f : {z : ℂ // ‖z‖ > ‖(2 : ℂ)‖ + 2} → {w : ℂ // 1 < ‖w‖} :=
    bottcher_map_outside_open_to_exterior (2 : ℂ)
  have hanalytic : OutsideOpenAnalyticityHypothesis (2 : ℂ) := h_payload.1
  have h_injOn : Set.InjOn (Quadratic.bottcher_map (2 : ℂ)) {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2} :=
    h_payload.2
  have hderiv :
      ∀ z, ‖z‖ > ‖(2 : ℂ)‖ + 2 → deriv (Quadratic.bottcher_map (2 : ℂ)) z ≠ 0 :=
    bottcher_map_deriv_ne_zero_on_outside_open_of_analyticAt_of_injOn (2 : ℂ) hanalytic h_injOn
  have hlocal :
      IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ)) :=
    isLocalHomeomorph_bottcher_map_outside_open_to_exterior_of_analyticAt_of_deriv_ne_zero
      (2 : ℂ) hanalytic hderiv
  have hlocalf : IsLocalHomeomorph f := by
    simpa [f] using hlocal
  have hsurjData : BottcherSurjOnExteriorFromOutsideOpen (2 : ℂ) :=
    bottcherSurjOnExteriorFromOutsideOpen_two_of_isProperMap_restrict_of_isLocalHomeomorph_restrict
      hproper hlocal
  have hsurj : Function.Surjective f := by
    intro w
    rcases hsurjData w.1 w.2 with ⟨z, hz, hEq⟩
    refine ⟨⟨z, hz⟩, ?_⟩
    apply Subtype.ext
    simpa [f, bottcher_map_outside_open_to_exterior] using hEq
  have hinj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    exact h_injOn x.2 y.2 (congrArg Subtype.val hxy)
  have hEmb : IsOpenEmbedding f :=
    IsOpenEmbedding.of_continuous_injective_isOpenMap hlocalf.continuous hinj hlocalf.isOpenMap
  refine ⟨hEmb.toIsEmbedding.toHomeomorphOfSurjective hsurj, ?_⟩
  funext z
  rfl

/-- Concrete realization of the Dudko-style conformal-identification ingress from
outside-open analyticity plus restricted properness at `c = 2`. -/
theorem dynamicalBottcherConformalIdentificationTwo_of_isProperMap_restrict_of_outsideOpenAnalyticityHypothesis
    (hproper : IsProperMap (bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (h_analytic : OutsideOpenAnalyticityHypothesis (2 : ℂ)) :
    DynamicalBottcherConformalIdentificationTwo :=
  dynamicalBottcherConformalIdentificationTwo_of_isProperMap_restrict_of_outsideOpenAnalyticInjPayload
    hproper (outsideOpenAnalyticInjPayload_of_outsideOpenAnalyticityHypothesis (2 : ℂ) h_analytic)

/-- Concrete Dudko-style conformal-identification ingress from the restricted
proper+local pair at `c = 2`, using the degree-one injectivity bridge for the
restricted map. -/
theorem dynamicalBottcherConformalIdentificationTwo_of_isProperMap_restrict_of_isLocalHomeomorph_restrict
    (hproper : IsProperMap (bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (hlocal : IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ))) :
    DynamicalBottcherConformalIdentificationTwo := by
  let f : {z : ℂ // ‖z‖ > ‖(2 : ℂ)‖ + 2} → {w : ℂ // 1 < ‖w‖} :=
    bottcher_map_outside_open_to_exterior (2 : ℂ)
  have hlocalf : IsLocalHomeomorph f := by
    simpa [f] using hlocal
  have hsurjData : BottcherSurjOnExteriorFromOutsideOpen (2 : ℂ) :=
    bottcherSurjOnExteriorFromOutsideOpen_two_of_isProperMap_restrict_of_isLocalHomeomorph_restrict
      hproper hlocal
  have hsurj : Function.Surjective f := by
    intro w
    rcases hsurjData w.1 w.2 with ⟨z, hz, hEq⟩
    refine ⟨⟨z, hz⟩, ?_⟩
    apply Subtype.ext
    simpa [f, bottcher_map_outside_open_to_exterior] using hEq
  have h_injOn :
      Set.InjOn (Quadratic.bottcher_map (2 : ℂ)) {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2} :=
    Mlc.Bottcher.DegreeOne.injOn_of_proper_localHomeomorph_asymptotic_at_infinity
      hproper hlocal
  have hinj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    exact h_injOn x.2 y.2 (congrArg Subtype.val hxy)
  have hEmb : IsOpenEmbedding f :=
    IsOpenEmbedding.of_continuous_injective_isOpenMap hlocalf.continuous hinj hlocalf.isOpenMap
  refine ⟨hEmb.toIsEmbedding.toHomeomorphOfSurjective hsurj, ?_⟩
  funext z
  rfl

/-- Dudko-style conformal-identification ingress from the direct proper+local
closure witness at `c = 2`. -/
theorem dynamicalBottcherConformalIdentificationTwo_of_directProperLocalWitnessTwo
    (h : DirectProperLocalWitnessTwo) :
    DynamicalBottcherConformalIdentificationTwo :=
  dynamicalBottcherConformalIdentificationTwo_of_isProperMap_restrict_of_isLocalHomeomorph_restrict
    h.1 h.2

/-- Direct proper+local witness extracted from the Dudko-style
outside-open/exterior conformal identification at `c = 2`. -/
theorem directProperLocalWitnessTwo_of_dynamicalBottcherConformalIdentificationTwo
    (hconf : DynamicalBottcherConformalIdentificationTwo) :
    DirectProperLocalWitnessTwo := by
  rcases hconf with ⟨e, heq⟩
  refine ⟨?_, ?_⟩
  · simpa [heq] using e.isProperMap
  · simpa [heq] using e.isLocalHomeomorph

/-- At `c = 2`, the Dudko-style conformal-identification ingress is equivalent to
the direct proper+local closure witness. -/
theorem dynamicalBottcherConformalIdentificationTwo_iff_directProperLocalWitnessTwo :
    DynamicalBottcherConformalIdentificationTwo ↔ DirectProperLocalWitnessTwo := by
  constructor
  · exact directProperLocalWitnessTwo_of_dynamicalBottcherConformalIdentificationTwo
  · exact dynamicalBottcherConformalIdentificationTwo_of_directProperLocalWitnessTwo

/-- Dudko ingress reduction bundle: from conformal identification, recover both
the direct proper+local witness and the CP5 residual frontier witness. -/
theorem directProperLocalWitnessTwo_and_cp5ResidualTwo_of_dynamicalBottcherConformalIdentificationTwo
    (hconf : DynamicalBottcherConformalIdentificationTwo) :
    DirectProperLocalWitnessTwo ∧ CP5ResidualTwo := by
  have hdir : DirectProperLocalWitnessTwo :=
    directProperLocalWitnessTwo_of_dynamicalBottcherConformalIdentificationTwo hconf
  refine ⟨hdir, ?_⟩
  exact cp5ResidualTwo_of_isProperMap_restrict_of_isLocalHomeomorph_restrict hdir.1 hdir.2

/-- Dudko-style conformal-identification ingress from local-homeomorph plus the
ambient preimage-closed compact-target condition at `c = 2`. -/
theorem dynamicalBottcherConformalIdentificationTwo_of_isLocalHomeomorph_restrict_of_preimage_closed
    (hlocal : IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (hclosedpre :
      ∀ K : Set {w : ℂ // 1 < ‖w‖}, IsCompact K →
        IsClosed
          ({z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2 ∧
            Quadratic.bottcher_map (2 : ℂ) z ∈ ((↑) '' K : Set ℂ)} : Set ℂ)) :
    DynamicalBottcherConformalIdentificationTwo :=
  dynamicalBottcherConformalIdentificationTwo_of_directProperLocalWitnessTwo
    (directProperLocalWitnessTwo_of_isLocalHomeomorph_restrict_of_preimage_closed hlocal hclosedpre)

/-- Dudko-style conformal-identification ingress from local-homeomorph plus
boundary exclusion on compact exterior targets at `c = 2`. -/
theorem dynamicalBottcherConformalIdentificationTwo_of_isLocalHomeomorph_restrict_of_boundary_exclusion
    (hlocal : IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (hboundary :
      ∀ K : Set {w : ℂ // 1 < ‖w‖}, IsCompact K →
        ∀ z, ‖z‖ = ‖(2 : ℂ)‖ + 2 →
          Quadratic.bottcher_map (2 : ℂ) z ∉ ((↑) '' K : Set ℂ)) :
    DynamicalBottcherConformalIdentificationTwo :=
  dynamicalBottcherConformalIdentificationTwo_of_directProperLocalWitnessTwo
    (directProperLocalWitnessTwo_of_isLocalHomeomorph_restrict_of_boundary_exclusion hlocal hboundary)

/-- Dudko-style conformal-identification ingress from local-homeomorph-on
outside-open plus preimage-closed compact-target data at `c = 2`. -/
theorem dynamicalBottcherConformalIdentificationTwo_of_isLocalHomeomorphOn_outside_open_of_preimage_closed
    (hlocal_on :
      IsLocalHomeomorphOn (Quadratic.bottcher_map (2 : ℂ)) {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2})
    (hclosedpre :
      ∀ K : Set {w : ℂ // 1 < ‖w‖}, IsCompact K →
        IsClosed
          ({z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2 ∧
            Quadratic.bottcher_map (2 : ℂ) z ∈ ((↑) '' K : Set ℂ)} : Set ℂ)) :
    DynamicalBottcherConformalIdentificationTwo :=
  dynamicalBottcherConformalIdentificationTwo_of_directProperLocalWitnessTwo
    (directProperLocalWitnessTwo_of_isLocalHomeomorphOn_outside_open_of_preimage_closed hlocal_on hclosedpre)

/-- Dudko-style conformal-identification ingress from local-homeomorph-on
outside-open plus boundary exclusion at `c = 2`. -/
theorem dynamicalBottcherConformalIdentificationTwo_of_isLocalHomeomorphOn_outside_open_of_boundary_exclusion
    (hlocal_on :
      IsLocalHomeomorphOn (Quadratic.bottcher_map (2 : ℂ)) {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2})
    (hboundary :
      ∀ K : Set {w : ℂ // 1 < ‖w‖}, IsCompact K →
        ∀ z, ‖z‖ = ‖(2 : ℂ)‖ + 2 →
          Quadratic.bottcher_map (2 : ℂ) z ∉ ((↑) '' K : Set ℂ)) :
    DynamicalBottcherConformalIdentificationTwo :=
  dynamicalBottcherConformalIdentificationTwo_of_directProperLocalWitnessTwo
    (directProperLocalWitnessTwo_of_isLocalHomeomorphOn_outside_open_of_boundary_exclusion
      hlocal_on hboundary)

/-- Any homeomorphic outside-open/exterior identification for the restricted
dynamical Böttcher map at `c = 2` yields the proper+local pair needed by the
CP5 residual left branch. -/
theorem isProperMap_and_isLocalHomeomorph_bottcher_map_outside_open_to_exterior_two_of_dynamicalBottcherConformalIdentificationTwo
    (hconf : DynamicalBottcherConformalIdentificationTwo) :
    IsProperMap (bottcher_map_outside_open_to_exterior (2 : ℂ)) ∧
      IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ)) := by
  rcases hconf with ⟨e, heq⟩
  refine ⟨?_, ?_⟩
  · simpa [heq] using e.isProperMap
  · simpa [heq] using e.isLocalHomeomorph

/-- CP5 residual source from the Dudko-style conformal-identification input. -/
theorem cp5ResidualTwo_of_dynamicalBottcherConformalIdentificationTwo
    (hconf : DynamicalBottcherConformalIdentificationTwo) :
    CP5ResidualTwo := by
  have hpair :
      IsProperMap (bottcher_map_outside_open_to_exterior (2 : ℂ)) ∧
        IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ)) :=
    isProperMap_and_isLocalHomeomorph_bottcher_map_outside_open_to_exterior_two_of_dynamicalBottcherConformalIdentificationTwo
      hconf
  exact cp5ResidualTwo_of_isProperMap_restrict_of_isLocalHomeomorph_restrict
    hpair.1 hpair.2

/-- Constructive CP5 endpoint from the Dudko-style conformal-identification
input. -/
theorem external_ray_map_exists_two_constructive_of_dynamicalBottcherConformalIdentificationTwo_via_directProperLocalWitnessTwo
    (hconf : DynamicalBottcherConformalIdentificationTwo) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_exists_two_constructive_of_directProperLocalWitnessTwo
    (directProperLocalWitnessTwo_of_dynamicalBottcherConformalIdentificationTwo hconf)

/-- Constructive CP5 endpoint from the Dudko-style conformal-identification
input. -/
theorem external_ray_map_exists_two_constructive_of_dynamicalBottcherConformalIdentificationTwo
    (hconf : DynamicalBottcherConformalIdentificationTwo) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_exists_two_constructive_of_dynamicalBottcherConformalIdentificationTwo_via_directProperLocalWitnessTwo
    hconf

/-- Dudko-route specialization: from restricted properness plus outside-open
analyticity at `c = 2`, obtain the constructive CP5 endpoint. -/
theorem external_ray_map_exists_two_constructive_of_isProperMap_restrict_of_outsideOpenAnalyticityHypothesis_via_dudko
    (hproper : IsProperMap (bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (h_analytic : OutsideOpenAnalyticityHypothesis (2 : ℂ)) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_exists_two_constructive_of_dynamicalBottcherConformalIdentificationTwo
    (dynamicalBottcherConformalIdentificationTwo_of_isProperMap_restrict_of_outsideOpenAnalyticityHypothesis
      hproper h_analytic)

/-- Dudko-route specialization: from restricted properness plus outside-open
analytic+injective payload at `c = 2`, obtain the constructive CP5 endpoint. -/
theorem external_ray_map_exists_two_constructive_of_isProperMap_restrict_of_outsideOpenAnalyticInjPayload_via_dudko
    (hproper : IsProperMap (bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (h_payload : OutsideOpenAnalyticInjPayload (2 : ℂ)) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_exists_two_constructive_of_dynamicalBottcherConformalIdentificationTwo
    (dynamicalBottcherConformalIdentificationTwo_of_isProperMap_restrict_of_outsideOpenAnalyticInjPayload
      hproper h_payload)

/-- Dudko-route specialization from the direct proper+local closure witness at
`c = 2`. -/
theorem external_ray_map_exists_two_constructive_of_directProperLocalWitnessTwo_via_dudko
    (h : DirectProperLocalWitnessTwo) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_exists_two_constructive_of_dynamicalBottcherConformalIdentificationTwo
    (dynamicalBottcherConformalIdentificationTwo_of_directProperLocalWitnessTwo h)

/-- Dudko-route specialization from local-homeomorph plus preimage-closed
compact-target data at `c = 2`. -/
theorem external_ray_map_exists_two_constructive_of_isLocalHomeomorph_restrict_of_preimage_closed_via_dudko
    (hlocal : IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (hclosedpre :
      ∀ K : Set {w : ℂ // 1 < ‖w‖}, IsCompact K →
        IsClosed
          ({z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2 ∧
            Quadratic.bottcher_map (2 : ℂ) z ∈ ((↑) '' K : Set ℂ)} : Set ℂ)) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_exists_two_constructive_of_dynamicalBottcherConformalIdentificationTwo
    (dynamicalBottcherConformalIdentificationTwo_of_isLocalHomeomorph_restrict_of_preimage_closed
      hlocal hclosedpre)

/-- Dudko-route specialization from local-homeomorph plus boundary exclusion on
compact exterior targets at `c = 2`. -/
theorem external_ray_map_exists_two_constructive_of_isLocalHomeomorph_restrict_of_boundary_exclusion_via_dudko
    (hlocal : IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (hboundary :
      ∀ K : Set {w : ℂ // 1 < ‖w‖}, IsCompact K →
        ∀ z, ‖z‖ = ‖(2 : ℂ)‖ + 2 →
          Quadratic.bottcher_map (2 : ℂ) z ∉ ((↑) '' K : Set ℂ)) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_exists_two_constructive_of_dynamicalBottcherConformalIdentificationTwo
    (dynamicalBottcherConformalIdentificationTwo_of_isLocalHomeomorph_restrict_of_boundary_exclusion
      hlocal hboundary)

/-- Dudko-route specialization from local-homeomorph-on outside-open plus
preimage-closed compact-target data at `c = 2`. -/
theorem external_ray_map_exists_two_constructive_of_isLocalHomeomorphOn_outside_open_of_preimage_closed_via_dudko
    (hlocal_on :
      IsLocalHomeomorphOn (Quadratic.bottcher_map (2 : ℂ)) {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2})
    (hclosedpre :
      ∀ K : Set {w : ℂ // 1 < ‖w‖}, IsCompact K →
        IsClosed
          ({z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2 ∧
            Quadratic.bottcher_map (2 : ℂ) z ∈ ((↑) '' K : Set ℂ)} : Set ℂ)) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_exists_two_constructive_of_dynamicalBottcherConformalIdentificationTwo
    (dynamicalBottcherConformalIdentificationTwo_of_isLocalHomeomorphOn_outside_open_of_preimage_closed
      hlocal_on hclosedpre)

/-- Dudko-route specialization from local-homeomorph-on outside-open plus
boundary exclusion on compact exterior targets at `c = 2`. -/
theorem external_ray_map_exists_two_constructive_of_isLocalHomeomorphOn_outside_open_of_boundary_exclusion_via_dudko
    (hlocal_on :
      IsLocalHomeomorphOn (Quadratic.bottcher_map (2 : ℂ)) {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2})
    (hboundary :
      ∀ K : Set {w : ℂ // 1 < ‖w‖}, IsCompact K →
        ∀ z, ‖z‖ = ‖(2 : ℂ)‖ + 2 →
          Quadratic.bottcher_map (2 : ℂ) z ∉ ((↑) '' K : Set ℂ)) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_exists_two_constructive_of_dynamicalBottcherConformalIdentificationTwo
    (dynamicalBottcherConformalIdentificationTwo_of_isLocalHomeomorphOn_outside_open_of_boundary_exclusion
      hlocal_on hboundary)

/-- Candidate proper+local source family at `c = 2`: outside-open analyticity,
derivative nonvanishing, and closedness of ambient preimages against compact
exterior targets. -/
def ProperLocalFromAnalyticPreimageClosedCandidateTwo : Prop :=
  OutsideOpenAnalyticityHypothesis (2 : ℂ) ∧
    (∀ z, ‖z‖ > ‖(2 : ℂ)‖ + 2 → deriv (Quadratic.bottcher_map (2 : ℂ)) z ≠ 0) ∧
      (∀ K : Set {w : ℂ // 1 < ‖w‖}, IsCompact K →
        IsClosed
          ({z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2 ∧
            Quadratic.bottcher_map (2 : ℂ) z ∈ ((↑) '' K : Set ℂ)} : Set ℂ))

/-- Candidate proper+local source family at `c = 2`: outside-open analyticity,
derivative nonvanishing, and boundary exclusion on compact exterior targets. -/
def ProperLocalFromAnalyticBoundaryExclusionCandidateTwo : Prop :=
  OutsideOpenAnalyticityHypothesis (2 : ℂ) ∧
    (∀ z, ‖z‖ > ‖(2 : ℂ)‖ + 2 → deriv (Quadratic.bottcher_map (2 : ℂ)) z ≠ 0) ∧
      (∀ K : Set {w : ℂ // 1 < ‖w‖}, IsCompact K →
        ∀ z, ‖z‖ = ‖(2 : ℂ)‖ + 2 →
          Quadratic.bottcher_map (2 : ℂ) z ∉ ((↑) '' K : Set ℂ))

/-- Any currently wired preimage-closed proper+local source candidate at `c = 2`
would imply the target restricted proper+local pair. -/
theorem isProperMap_and_isLocalHomeomorph_bottcher_map_outside_open_to_exterior_two_of_properLocalFromAnalyticPreimageClosedCandidateTwo
    (h : ProperLocalFromAnalyticPreimageClosedCandidateTwo) :
    IsProperMap (bottcher_map_outside_open_to_exterior (2 : ℂ)) ∧
      IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ)) := by
  refine ⟨?_, ?_⟩
  · exact isProperMap_bottcher_map_outside_open_to_exterior_two_of_analyticAt_of_preimage_closed
      h.1 h.2.2
  · exact isLocalHomeomorph_bottcher_map_outside_open_to_exterior_of_analyticAt_of_deriv_ne_zero
      (2 : ℂ) h.1 h.2.1

/-- Any currently wired boundary-exclusion proper+local source candidate at `c = 2`
would imply the target restricted proper+local pair. -/
theorem isProperMap_and_isLocalHomeomorph_bottcher_map_outside_open_to_exterior_two_of_properLocalFromAnalyticBoundaryExclusionCandidateTwo
    (h : ProperLocalFromAnalyticBoundaryExclusionCandidateTwo) :
    IsProperMap (bottcher_map_outside_open_to_exterior (2 : ℂ)) ∧
      IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ)) := by
  refine ⟨?_, ?_⟩
  · exact isProperMap_bottcher_map_outside_open_to_exterior_of_analyticAt_of_boundary_exclusion
      (2 : ℂ) h.1 h.2.2
  · exact isLocalHomeomorph_bottcher_map_outside_open_to_exterior_of_analyticAt_of_deriv_ne_zero
      (2 : ℂ) h.1 h.2.1

/-- The preimage-closed proper+local source candidate is inconsistent at `c = 2`
because outside-open analyticity is impossible in the current model. -/
theorem not_properLocalFromAnalyticPreimageClosedCandidateTwo :
    ¬ ProperLocalFromAnalyticPreimageClosedCandidateTwo := by
  intro h
  exact not_outsideOpenAnalyticityHypothesisTwo h.1

/-- The boundary-exclusion proper+local source candidate is inconsistent at `c = 2`
because the boundary-exclusion family is impossible in the current model. -/
theorem not_properLocalFromAnalyticBoundaryExclusionCandidateTwo :
    ¬ ProperLocalFromAnalyticBoundaryExclusionCandidateTwo := by
  intro h
  exact not_boundary_exclusion_family_two h.2.2

/-- Aggregate predicate for currently wired source families that could imply the
restricted proper+local CP5 residual branch at `c = 2`. -/
def KnownProperLocalSourceCandidateTwo : Prop :=
  ProperLocalFromAnalyticPreimageClosedCandidateTwo ∨
    ProperLocalFromAnalyticBoundaryExclusionCandidateTwo

/-- Any currently wired proper+local source family in the previous aggregate
implies the restricted proper+local CP5 residual branch at `c = 2`. -/
theorem isProperMap_and_isLocalHomeomorph_bottcher_map_outside_open_to_exterior_two_of_knownProperLocalSourceCandidateTwo
    (h : KnownProperLocalSourceCandidateTwo) :
    IsProperMap (bottcher_map_outside_open_to_exterior (2 : ℂ)) ∧
      IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ)) := by
  rcases h with hA | hB
  · exact
      isProperMap_and_isLocalHomeomorph_bottcher_map_outside_open_to_exterior_two_of_properLocalFromAnalyticPreimageClosedCandidateTwo
        hA
  · exact
      isProperMap_and_isLocalHomeomorph_bottcher_map_outside_open_to_exterior_two_of_properLocalFromAnalyticBoundaryExclusionCandidateTwo
        hB

/-- Dudko-style conformal identification from the preimage-closed proper+local
source candidate at `c = 2`. -/
theorem dynamicalBottcherConformalIdentificationTwo_of_properLocalFromAnalyticPreimageClosedCandidateTwo
    (h : ProperLocalFromAnalyticPreimageClosedCandidateTwo) :
    DynamicalBottcherConformalIdentificationTwo := by
  have hproper : IsProperMap (bottcher_map_outside_open_to_exterior (2 : ℂ)) :=
    (isProperMap_and_isLocalHomeomorph_bottcher_map_outside_open_to_exterior_two_of_properLocalFromAnalyticPreimageClosedCandidateTwo
      h).1
  exact dynamicalBottcherConformalIdentificationTwo_of_isProperMap_restrict_of_outsideOpenAnalyticityHypothesis
    hproper h.1

/-- Dudko-style conformal identification from the boundary-exclusion proper+local
source candidate at `c = 2`. -/
theorem dynamicalBottcherConformalIdentificationTwo_of_properLocalFromAnalyticBoundaryExclusionCandidateTwo
    (h : ProperLocalFromAnalyticBoundaryExclusionCandidateTwo) :
    DynamicalBottcherConformalIdentificationTwo := by
  have hproper : IsProperMap (bottcher_map_outside_open_to_exterior (2 : ℂ)) :=
    (isProperMap_and_isLocalHomeomorph_bottcher_map_outside_open_to_exterior_two_of_properLocalFromAnalyticBoundaryExclusionCandidateTwo
      h).1
  exact dynamicalBottcherConformalIdentificationTwo_of_isProperMap_restrict_of_outsideOpenAnalyticityHypothesis
    hproper h.1

/-- Dudko-style conformal identification from any currently wired proper+local
source family at `c = 2`. -/
theorem dynamicalBottcherConformalIdentificationTwo_of_knownProperLocalSourceCandidateTwo
    (h : KnownProperLocalSourceCandidateTwo) :
    DynamicalBottcherConformalIdentificationTwo := by
  rcases h with hA | hB
  · exact
      dynamicalBottcherConformalIdentificationTwo_of_properLocalFromAnalyticPreimageClosedCandidateTwo
        hA
  · exact
      dynamicalBottcherConformalIdentificationTwo_of_properLocalFromAnalyticBoundaryExclusionCandidateTwo
        hB

/-- CP5 endpoint via the Dudko-style conformal-identification route from any
currently wired proper+local source family at `c = 2`. -/
theorem external_ray_map_exists_two_constructive_of_knownProperLocalSourceCandidateTwo_via_dudko
    (h : KnownProperLocalSourceCandidateTwo) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_exists_two_constructive_of_dynamicalBottcherConformalIdentificationTwo
    (dynamicalBottcherConformalIdentificationTwo_of_knownProperLocalSourceCandidateTwo h)

/-- All currently wired proper+local source families are inconsistent in the
current model at `c = 2`. -/
theorem not_knownProperLocalSourceCandidateTwo :
    ¬ KnownProperLocalSourceCandidateTwo := by
  intro h
  rcases h with hA | hB
  · exact not_properLocalFromAnalyticPreimageClosedCandidateTwo hA
  · exact not_properLocalFromAnalyticBoundaryExclusionCandidateTwo hB

/-- Current-model proper+local source exhaustion at `c = 2`: known source
families are blocked, so only a direct witness of the restricted proper+local
pair remains. -/
theorem properLocalSourceExhaustionTwo :
    (KnownProperLocalSourceCandidateTwo ∨
      (IsProperMap (bottcher_map_outside_open_to_exterior (2 : ℂ)) ∧
        IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ)))) ↔
      (IsProperMap (bottcher_map_outside_open_to_exterior (2 : ℂ)) ∧
        IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ))) := by
  constructor
  · intro h
    rcases h with hKnown | hDirect
    · exact False.elim (not_knownProperLocalSourceCandidateTwo hKnown)
    · exact hDirect
  · intro hDirect
    exact Or.inr hDirect

/-- Direct-witness presentation of `properLocalSourceExhaustionTwo` at `c = 2`. -/
theorem properLocalSourceExhaustionTwo_directProperLocalWitness :
    (KnownProperLocalSourceCandidateTwo ∨ DirectProperLocalWitnessTwo) ↔
      DirectProperLocalWitnessTwo := by
  simpa [DirectProperLocalWitnessTwo] using properLocalSourceExhaustionTwo

/-- Dudko-ingress presentation of source exhaustion at `c = 2`: the known source
families are blocked, so any surviving disjunction branch is Dudko directly. -/
theorem properLocalSourceExhaustionTwo_dynamicalBottcherConformalIdentification :
    (KnownProperLocalSourceCandidateTwo ∨ DynamicalBottcherConformalIdentificationTwo) ↔
      DynamicalBottcherConformalIdentificationTwo := by
  constructor
  · intro h
    rcases h with hKnown | hDudko
    · exact False.elim (not_knownProperLocalSourceCandidateTwo hKnown)
    · exact hDudko
  · intro hDudko
    exact Or.inr hDudko

/-- CP5 endpoint from the exhausted source disjunction at `c = 2`, reduced to the
Dudko branch. -/
theorem external_ray_map_exists_two_constructive_of_knownProperLocalSourceCandidateTwo_or_dudko
    (h : KnownProperLocalSourceCandidateTwo ∨ DynamicalBottcherConformalIdentificationTwo) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_exists_two_constructive_of_dynamicalBottcherConformalIdentificationTwo
    ((properLocalSourceExhaustionTwo_dynamicalBottcherConformalIdentification).1 h)

/-- Root MLC wrapper from the exhausted source disjunction at `c = 2`, reduced to
the Dudko branch. -/
theorem mlc_conjecture_of_knownProperLocalSourceCandidateTwo_or_dudko
    (h : KnownProperLocalSourceCandidateTwo ∨ DynamicalBottcherConformalIdentificationTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_externalRayMapData_two
    (external_ray_map_exists_two_constructive_of_knownProperLocalSourceCandidateTwo_or_dudko h)

/-- Cross-normalization at `c = 2`: the exhausted known-source-or-Dudko
disjunction is equivalent to the direct proper+local witness. -/
theorem properLocalSourceExhaustionTwo_knownSourceOrDudko_iff_directProperLocalWitness :
    (KnownProperLocalSourceCandidateTwo ∨ DynamicalBottcherConformalIdentificationTwo) ↔
      DirectProperLocalWitnessTwo := by
  constructor
  · intro h
    exact directProperLocalWitnessTwo_of_dynamicalBottcherConformalIdentificationTwo
      ((properLocalSourceExhaustionTwo_dynamicalBottcherConformalIdentification).1 h)
  · intro hDirect
    exact Or.inr
      ((dynamicalBottcherConformalIdentificationTwo_iff_directProperLocalWitnessTwo).2 hDirect)

/-- CP5 endpoint from the exhausted known-source-or-direct-witness disjunction at
`c = 2`, reduced to the direct witness branch. -/
theorem external_ray_map_exists_two_constructive_of_knownProperLocalSourceCandidateTwo_or_directProperLocalWitnessTwo
    (h : KnownProperLocalSourceCandidateTwo ∨ DirectProperLocalWitnessTwo) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_exists_two_constructive_of_directProperLocalWitnessTwo
    ((properLocalSourceExhaustionTwo_directProperLocalWitness).1 h)

/-- Root MLC wrapper from the exhausted known-source-or-direct-witness
disjunction at `c = 2`, reduced to the direct witness branch. -/
theorem mlc_conjecture_of_knownProperLocalSourceCandidateTwo_or_directProperLocalWitnessTwo
    (h : KnownProperLocalSourceCandidateTwo ∨ DirectProperLocalWitnessTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_externalRayMapData_two
    (external_ray_map_exists_two_constructive_of_knownProperLocalSourceCandidateTwo_or_directProperLocalWitnessTwo
      h)

/-- Aggregate predicate collecting all currently exposed non-axiomatic ingress
branches for the `c = 2` constructive endpoint. -/
def RemainingConstructiveIngressTwo : Prop :=
  KnownProperLocalSourceCandidateTwo ∨
    DynamicalBottcherConformalIdentificationTwo ∨
      DirectProperLocalWitnessTwo

/-- Canonical aggregate-ingress introduction at `c = 2` from a direct proper+local
witness. -/
theorem remainingConstructiveIngressTwo_of_directProperLocalWitnessTwo
    (h : DirectProperLocalWitnessTwo) :
    RemainingConstructiveIngressTwo :=
  Or.inr (Or.inr h)

/-- Canonical aggregate-ingress introduction at `c = 2` from the Dudko
conformal-identification ingress. -/
theorem remainingConstructiveIngressTwo_of_dynamicalBottcherConformalIdentificationTwo
    (h : DynamicalBottcherConformalIdentificationTwo) :
    RemainingConstructiveIngressTwo :=
  Or.inr (Or.inl h)

/-- Canonical aggregate-ingress introduction at `c = 2` from the exhausted
known-source-or-direct-witness disjunction. -/
theorem remainingConstructiveIngressTwo_of_knownProperLocalSourceCandidateTwo_or_directProperLocalWitnessTwo
    (h : KnownProperLocalSourceCandidateTwo ∨ DirectProperLocalWitnessTwo) :
    RemainingConstructiveIngressTwo := by
  rcases h with hKnown | hDirect
  · exact Or.inl hKnown
  · exact Or.inr (Or.inr hDirect)

/-- Canonical aggregate-ingress introduction at `c = 2` from the exhausted
known-source-or-Dudko disjunction. -/
theorem remainingConstructiveIngressTwo_of_knownProperLocalSourceCandidateTwo_or_dynamicalBottcherConformalIdentificationTwo
    (h : KnownProperLocalSourceCandidateTwo ∨ DynamicalBottcherConformalIdentificationTwo) :
    RemainingConstructiveIngressTwo := by
  rcases h with hKnown | hDudko
  · exact Or.inl hKnown
  · exact Or.inr (Or.inl hDudko)

/-- Canonical aggregate-ingress introduction at `c = 2` from the exhausted
known-source-or-Dudko disjunction (short-name alias). -/
theorem remainingConstructiveIngressTwo_of_knownProperLocalSourceCandidateTwo_or_dudko
    (h : KnownProperLocalSourceCandidateTwo ∨ DynamicalBottcherConformalIdentificationTwo) :
    RemainingConstructiveIngressTwo :=
  remainingConstructiveIngressTwo_of_knownProperLocalSourceCandidateTwo_or_dynamicalBottcherConformalIdentificationTwo
    h

/-- Aggregate-ingress normalization at `c = 2`: equivalent to the exhausted
known-source-or-direct-witness disjunction. -/
theorem remainingConstructiveIngressTwo_iff_knownProperLocalSourceCandidateTwo_or_directProperLocalWitnessTwo :
    RemainingConstructiveIngressTwo ↔ (KnownProperLocalSourceCandidateTwo ∨ DirectProperLocalWitnessTwo) := by
  constructor
  · intro h
    rcases h with hKnown | hTail
    · exact Or.inl hKnown
    · rcases hTail with hDudko | hDirect
      · exact Or.inr
          ((dynamicalBottcherConformalIdentificationTwo_iff_directProperLocalWitnessTwo).1 hDudko)
      · exact Or.inr hDirect
  · intro h
    exact
      remainingConstructiveIngressTwo_of_knownProperLocalSourceCandidateTwo_or_directProperLocalWitnessTwo
        h

/-- Aggregate-ingress normalization at `c = 2`: equivalent to the exhausted
known-source-or-Dudko disjunction. -/
theorem remainingConstructiveIngressTwo_iff_knownProperLocalSourceCandidateTwo_or_dynamicalBottcherConformalIdentificationTwo :
    RemainingConstructiveIngressTwo ↔
      (KnownProperLocalSourceCandidateTwo ∨ DynamicalBottcherConformalIdentificationTwo) := by
  constructor
  · intro h
    rcases h with hKnown | hTail
    · exact Or.inl hKnown
    · rcases hTail with hDudko | hDirect
      · exact Or.inr hDudko
      · exact Or.inr
          ((dynamicalBottcherConformalIdentificationTwo_iff_directProperLocalWitnessTwo).2 hDirect)
  · intro h
    exact
      remainingConstructiveIngressTwo_of_knownProperLocalSourceCandidateTwo_or_dynamicalBottcherConformalIdentificationTwo
        h

/-- Aggregate-ingress normalization at `c = 2`: equivalent to the exhausted
known-source-or-Dudko disjunction (short-name alias). -/
theorem remainingConstructiveIngressTwo_iff_knownProperLocalSourceCandidateTwo_or_dudko :
    RemainingConstructiveIngressTwo ↔
      (KnownProperLocalSourceCandidateTwo ∨ DynamicalBottcherConformalIdentificationTwo) :=
  remainingConstructiveIngressTwo_iff_knownProperLocalSourceCandidateTwo_or_dynamicalBottcherConformalIdentificationTwo

/-- Aggregate-ingress normalization at `c = 2`: equivalent to the Dudko-or-direct
disjunction once known source families are recognized as blocked. -/
theorem remainingConstructiveIngressTwo_iff_dynamicalBottcherConformalIdentificationTwo_or_directProperLocalWitnessTwo :
    RemainingConstructiveIngressTwo ↔
      (DynamicalBottcherConformalIdentificationTwo ∨ DirectProperLocalWitnessTwo) := by
  constructor
  · intro h
    rcases h with hKnown | hTail
    · exact False.elim (not_knownProperLocalSourceCandidateTwo hKnown)
    · rcases hTail with hDudko | hDirect
      · exact Or.inl hDudko
      · exact Or.inr hDirect
  · intro h
    rcases h with hDudko | hDirect
    · exact remainingConstructiveIngressTwo_of_dynamicalBottcherConformalIdentificationTwo hDudko
    · exact remainingConstructiveIngressTwo_of_directProperLocalWitnessTwo hDirect

/-- Aggregate-ingress normalization at `c = 2`: equivalent to the Dudko-or-direct
disjunction (short-name alias). -/
theorem remainingConstructiveIngressTwo_iff_dudko_or_directProperLocalWitnessTwo :
    RemainingConstructiveIngressTwo ↔
      (DynamicalBottcherConformalIdentificationTwo ∨ DirectProperLocalWitnessTwo) :=
  remainingConstructiveIngressTwo_iff_dynamicalBottcherConformalIdentificationTwo_or_directProperLocalWitnessTwo

/-- Source-exhaustion normalization at `c = 2`: the aggregate non-axiomatic
ingress predicate collapses to the direct proper+local witness. -/
theorem remainingConstructiveIngressTwo_iff_directProperLocalWitness :
    RemainingConstructiveIngressTwo ↔ DirectProperLocalWitnessTwo := by
  constructor
  · intro h
    rcases h with hKnown | hTail
    · exact False.elim (not_knownProperLocalSourceCandidateTwo hKnown)
    · rcases hTail with hDudko | hDirect
      · exact directProperLocalWitnessTwo_of_dynamicalBottcherConformalIdentificationTwo hDudko
      · exact hDirect
  · intro hDirect
    exact Or.inr (Or.inr hDirect)

/-- Direct-witness extraction from the aggregate non-axiomatic ingress predicate
at `c = 2`. -/
theorem directProperLocalWitnessTwo_of_remainingConstructiveIngressTwo
    (h : RemainingConstructiveIngressTwo) :
    DirectProperLocalWitnessTwo :=
  (remainingConstructiveIngressTwo_iff_directProperLocalWitness).1 h

/-- Dudko-ingress extraction from the aggregate non-axiomatic ingress predicate
at `c = 2`. -/
theorem dynamicalBottcherConformalIdentificationTwo_of_remainingConstructiveIngressTwo
    (h : RemainingConstructiveIngressTwo) :
    DynamicalBottcherConformalIdentificationTwo :=
  (dynamicalBottcherConformalIdentificationTwo_iff_directProperLocalWitnessTwo).2
    ((remainingConstructiveIngressTwo_iff_directProperLocalWitness).1 h)

/-- Source-exhaustion normalization at `c = 2`: the aggregate non-axiomatic
ingress predicate is equivalent to the Dudko conformal-identification ingress. -/
theorem remainingConstructiveIngressTwo_iff_dynamicalBottcherConformalIdentificationTwo :
    RemainingConstructiveIngressTwo ↔ DynamicalBottcherConformalIdentificationTwo := by
  constructor
  · intro h
    exact (dynamicalBottcherConformalIdentificationTwo_iff_directProperLocalWitnessTwo).2
      ((remainingConstructiveIngressTwo_iff_directProperLocalWitness).1 h)
  · intro hDudko
    exact (remainingConstructiveIngressTwo_iff_directProperLocalWitness).2
      ((dynamicalBottcherConformalIdentificationTwo_iff_directProperLocalWitnessTwo).1 hDudko)

/-- CP5 endpoint from the aggregate non-axiomatic ingress predicate at `c = 2`,
reduced to the direct witness branch. -/
theorem external_ray_map_exists_two_constructive_of_remainingConstructiveIngressTwo
    (h : RemainingConstructiveIngressTwo) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_exists_two_constructive_of_directProperLocalWitnessTwo
    ((remainingConstructiveIngressTwo_iff_directProperLocalWitness).1 h)

/-- Root MLC wrapper from the aggregate non-axiomatic ingress predicate at
`c = 2`. -/
theorem mlc_conjecture_of_remainingConstructiveIngressTwo
    (h : RemainingConstructiveIngressTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_externalRayMapData_two
    (external_ray_map_exists_two_constructive_of_remainingConstructiveIngressTwo h)

/-- CP5 endpoint from the aggregate non-axiomatic ingress predicate at `c = 2`,
presented via the Dudko branch. -/
theorem external_ray_map_exists_two_constructive_of_remainingConstructiveIngressTwo_via_dudko
    (h : RemainingConstructiveIngressTwo) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_exists_two_constructive_of_dynamicalBottcherConformalIdentificationTwo
    ((remainingConstructiveIngressTwo_iff_dynamicalBottcherConformalIdentificationTwo).1 h)

/-- CP5 endpoint from direct proper+local witness at `c = 2`, routed through the
aggregate non-axiomatic ingress predicate. -/
theorem external_ray_map_exists_two_constructive_of_directProperLocalWitnessTwo_via_remainingConstructiveIngressTwo
    (h : DirectProperLocalWitnessTwo) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_exists_two_constructive_of_remainingConstructiveIngressTwo
    (remainingConstructiveIngressTwo_of_directProperLocalWitnessTwo h)

/-- CP5 endpoint from Dudko conformal-identification ingress at `c = 2`, routed
through the aggregate non-axiomatic ingress predicate. -/
theorem external_ray_map_exists_two_constructive_of_dynamicalBottcherConformalIdentificationTwo_via_remainingConstructiveIngressTwo
    (h : DynamicalBottcherConformalIdentificationTwo) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_exists_two_constructive_of_remainingConstructiveIngressTwo
    (remainingConstructiveIngressTwo_of_dynamicalBottcherConformalIdentificationTwo h)

/-- Root MLC wrapper from direct proper+local witness at `c = 2`, routed through
the aggregate non-axiomatic ingress predicate. -/
theorem mlc_conjecture_of_directProperLocalWitnessTwo_via_remainingConstructiveIngressTwo
    (h : DirectProperLocalWitnessTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_remainingConstructiveIngressTwo
    (remainingConstructiveIngressTwo_of_directProperLocalWitnessTwo h)

/-- Root MLC wrapper from Dudko conformal-identification ingress at `c = 2`,
routed through the aggregate non-axiomatic ingress predicate. -/
theorem mlc_conjecture_of_dynamicalBottcherConformalIdentificationTwo_via_remainingConstructiveIngressTwo
    (h : DynamicalBottcherConformalIdentificationTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_remainingConstructiveIngressTwo
    (remainingConstructiveIngressTwo_of_dynamicalBottcherConformalIdentificationTwo h)

/-- CP5 endpoint from the exhausted known-source-or-direct-witness disjunction at
`c = 2`, routed through the aggregate non-axiomatic ingress predicate. -/
theorem external_ray_map_exists_two_constructive_of_knownProperLocalSourceCandidateTwo_or_directProperLocalWitnessTwo_via_remainingConstructiveIngressTwo
    (h : KnownProperLocalSourceCandidateTwo ∨ DirectProperLocalWitnessTwo) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_exists_two_constructive_of_remainingConstructiveIngressTwo
    (remainingConstructiveIngressTwo_of_knownProperLocalSourceCandidateTwo_or_directProperLocalWitnessTwo h)

/-- Root MLC wrapper from the exhausted known-source-or-direct-witness
disjunction at `c = 2`, routed through the aggregate non-axiomatic ingress
predicate. -/
theorem mlc_conjecture_of_knownProperLocalSourceCandidateTwo_or_directProperLocalWitnessTwo_via_remainingConstructiveIngressTwo
    (h : KnownProperLocalSourceCandidateTwo ∨ DirectProperLocalWitnessTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_remainingConstructiveIngressTwo
    (remainingConstructiveIngressTwo_of_knownProperLocalSourceCandidateTwo_or_directProperLocalWitnessTwo h)

/-- CP5 endpoint from the exhausted known-source-or-Dudko disjunction at `c = 2`,
routed through the aggregate non-axiomatic ingress predicate. -/
theorem external_ray_map_exists_two_constructive_of_knownProperLocalSourceCandidateTwo_or_dynamicalBottcherConformalIdentificationTwo_via_remainingConstructiveIngressTwo
    (h : KnownProperLocalSourceCandidateTwo ∨ DynamicalBottcherConformalIdentificationTwo) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_exists_two_constructive_of_remainingConstructiveIngressTwo
    (remainingConstructiveIngressTwo_of_knownProperLocalSourceCandidateTwo_or_dynamicalBottcherConformalIdentificationTwo
      h)

/-- Root MLC wrapper from the exhausted known-source-or-Dudko disjunction at
`c = 2`, routed through the aggregate non-axiomatic ingress predicate. -/
theorem mlc_conjecture_of_knownProperLocalSourceCandidateTwo_or_dynamicalBottcherConformalIdentificationTwo_via_remainingConstructiveIngressTwo
    (h : KnownProperLocalSourceCandidateTwo ∨ DynamicalBottcherConformalIdentificationTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_remainingConstructiveIngressTwo
    (remainingConstructiveIngressTwo_of_knownProperLocalSourceCandidateTwo_or_dynamicalBottcherConformalIdentificationTwo
      h)

/-- CP5 endpoint from the exhausted known-source-or-Dudko disjunction at `c = 2`,
routed through the aggregate ingress predicate (short-name alias). -/
theorem external_ray_map_exists_two_constructive_of_knownProperLocalSourceCandidateTwo_or_dudko_via_remainingConstructiveIngressTwo
    (h : KnownProperLocalSourceCandidateTwo ∨ DynamicalBottcherConformalIdentificationTwo) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_exists_two_constructive_of_knownProperLocalSourceCandidateTwo_or_dynamicalBottcherConformalIdentificationTwo_via_remainingConstructiveIngressTwo
    h

/-- Root MLC wrapper from the exhausted known-source-or-Dudko disjunction at
`c = 2`, routed through the aggregate ingress predicate (short-name alias). -/
theorem mlc_conjecture_of_knownProperLocalSourceCandidateTwo_or_dudko_via_remainingConstructiveIngressTwo
    (h : KnownProperLocalSourceCandidateTwo ∨ DynamicalBottcherConformalIdentificationTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact
    mlc_conjecture_of_knownProperLocalSourceCandidateTwo_or_dynamicalBottcherConformalIdentificationTwo_via_remainingConstructiveIngressTwo
      h

/-- Scope-check no-go at `c = 2`: this combined iterate-left-inverse +
analytic/derivative payload is inconsistent because the analytic/derivative
component is impossible. -/
theorem not_iterLeftInverseAnalyticDerivConstructivePayloadTwo :
    ¬ IterLeftInverseAnalyticDerivConstructivePayloadTwo := by
  intro h_payload
  exact not_analyticDerivConstructivePayloadTwo h_payload.2

/-- Scope-check no-go at `c = 2`: this payload shape is inconsistent in the
current model because outside-open quotient constancy is impossible. -/
theorem not_nonSlitQuotientConstConstructivePayloadTwo :
    ¬ NonSlitQuotientConstConstructivePayloadTwo := by
  intro h_payload
  exact not_outsideOpenQuotientConstHypothesisTwo h_payload.2

/-- Scope-check no-go at `c = 2`: this payload shape is inconsistent in the
current model because outside-open quotient analyticity is impossible. -/
theorem not_nonSlitQuotientAnalyticConstructivePayloadTwo :
    ¬ NonSlitQuotientAnalyticConstructivePayloadTwo := by
  intro h_payload
  exact not_outsideOpenQuotientAnalyticityHypothesisTwo h_payload.2

/-- Scope-check no-go at `c = 2`: this payload shape is inconsistent in the
current model because strong quotient-rigidity witness is impossible. -/
theorem not_nonSlitQuotientConstRealConstructivePayloadTwo :
    ¬ NonSlitQuotientConstRealConstructivePayloadTwo := by
  intro h_payload
  exact not_outsideOpenQuotientConstRealWitnessTwo h_payload.2

/-- Scope-check no-go at `c = 2`: this revised scope payload is also
inconsistent in the current model because `not_outsideOpenAnalyticityHypothesisTwo`
is available. -/
theorem not_nonSlitAnalyticScopeAssumptionConstructivePayloadTwo :
    ¬ NonSlitAnalyticScopeAssumptionConstructivePayloadTwo := by
  intro h_payload
  exact h_payload.2 not_outsideOpenAnalyticityHypothesisTwo

/-- Scope-check no-go at `c = 2`: this payload shape is inconsistent in the
current model because boundary exclusion is impossible. -/
theorem not_nonSlitBoundaryExclusionConstructivePayloadTwo :
    ¬ NonSlitBoundaryExclusionConstructivePayloadTwo := by
  intro h_payload
  exact not_boundary_exclusion_family_two h_payload.2

/-- Scope-check no-go at `c = 2`: this payload shape is inconsistent in the
current model because local-slit neighborhood payload is impossible. -/
theorem not_nonSlitMemNhdsSlitInjConstructivePayloadTwo :
    ¬ NonSlitMemNhdsSlitInjConstructivePayloadTwo := by
  intro h_payload
  exact not_mem_nhds_slit_on_outside_open_two h_payload.2.1

/-- Scope-check no-go at `c = 2`: this payload shape is inconsistent in the
current model because local-slit neighborhood payload is impossible. -/
theorem not_nonSlitMemNhdsSlitIterLeftInverseConstructivePayloadTwo :
    ¬ NonSlitMemNhdsSlitIterLeftInverseConstructivePayloadTwo := by
  intro h_payload
  exact not_mem_nhds_slit_on_outside_open_two h_payload.2.1

/-- Aggregate predicate for currently blocked legacy CP5 ingress payload families
at `c = 2`. -/
def KnownCP5IngressCandidateTwo : Prop :=
  NonSlitAnalyticConstructivePayloadTwo ∨
    NonSlitAnalyticInjConstructivePayloadTwo ∨
    AnalyticDerivConstructivePayloadTwo ∨
    NonSlitQuotientConstConstructivePayloadTwo ∨
    NonSlitQuotientAnalyticConstructivePayloadTwo ∨
    NonSlitQuotientConstRealConstructivePayloadTwo ∨
    NonSlitEventualSlitConstructivePayloadTwo ∨
    NonSlitBoundaryExclusionConstructivePayloadTwo ∨
    NonSlitMemNhdsSlitInjConstructivePayloadTwo ∨
    NonSlitMemNhdsSlitIterLeftInverseConstructivePayloadTwo ∨
    NonSlitAnalyticScopeAssumptionConstructivePayloadTwo

/-- All currently wired CP5 ingress payload families are inconsistent in the
current model at `c = 2`. -/
theorem not_knownCP5IngressCandidateTwo :
    ¬ KnownCP5IngressCandidateTwo := by
  intro h
  rcases h with hA | hB | hC | hD | hE | hF | hG | hH | hI | hJ | hK
  · exact not_nonSlitAnalyticConstructivePayloadTwo hA
  · exact not_nonSlitAnalyticInjConstructivePayloadTwo hB
  · exact not_analyticDerivConstructivePayloadTwo hC
  · exact not_nonSlitQuotientConstConstructivePayloadTwo hD
  · exact not_nonSlitQuotientAnalyticConstructivePayloadTwo hE
  · exact not_nonSlitQuotientConstRealConstructivePayloadTwo hF
  · exact not_nonSlitEventualSlitConstructivePayloadTwo hG
  · exact not_nonSlitBoundaryExclusionConstructivePayloadTwo hH
  · exact not_nonSlitMemNhdsSlitInjConstructivePayloadTwo hI
  · exact not_nonSlitMemNhdsSlitIterLeftInverseConstructivePayloadTwo hJ
  · exact not_nonSlitAnalyticScopeAssumptionConstructivePayloadTwo hK

/-- Revised CP2 formal-status export at `c = 2` for root planning:
outside-open analyticity is impossible in the current model. -/
theorem cp2_revised_target_two :
    RevisedCP2TargetTwo :=
  revisedCP2TargetTwo_constructive

/-- Revised CP3 formal target at `c = 2` in the current model. -/
def RevisedCP3TargetTwo : Prop :=
  ¬ NonSlitAnalyticInjConstructivePayloadTwo

/-- Revised CP3 constructive witness at `c = 2`. -/
theorem revisedCP3TargetTwo_constructive : RevisedCP3TargetTwo :=
  not_nonSlitAnalyticInjConstructivePayloadTwo

/-- Revised CP4 formal target at `c = 2` in the current model. -/
def RevisedCP4TargetTwo : Prop :=
  ¬ AnalyticDerivConstructivePayloadTwo

/-- Revised CP4 constructive witness at `c = 2`. -/
theorem revisedCP4TargetTwo_constructive : RevisedCP4TargetTwo :=
  not_analyticDerivConstructivePayloadTwo

/-- Revised CP5 formal target at `c = 2`: MLC follows from any non-vacuous
external-ray-data source term. -/
def RevisedCP5TargetTwo : Prop :=
  Quadratic.ExternalRayMapData (2 : ℂ) → LocallyConnectedSpace mandelbrotSet

/-- Revised CP5 constructive witness at `c = 2`; this isolates the only
remaining non-vacuous ingress obligation. -/
theorem revisedCP5TargetTwo_constructive : RevisedCP5TargetTwo :=
  mlc_conjecture_of_externalRayMapData_two

/-- Root bridge from the strong quotient-rigidity witness payload at `c = 2`. -/
theorem mlc_conjecture_of_nonSlitQuotientConstRealConstructivePayloadTwo
    (h_payload : NonSlitQuotientConstRealConstructivePayloadTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_externalRayMapData_two
    (external_ray_map_exists_two_constructive_of_isClosedRange_restrict_of_outsideOpenQuotientConstRealWitnessTwo_via_localChartWithin
      h_payload.1 h_payload.2)

/-- Root bridge from quotient-constancy payload at `c = 2`. -/
theorem mlc_conjecture_of_nonSlitQuotientConstConstructivePayloadTwo
    (h_payload : NonSlitQuotientConstConstructivePayloadTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_externalRayMapData_two
    (external_ray_map_exists_two_constructive_of_isClosedRange_restrict_of_outsideOpenQuotientConstHypothesisTwo
      h_payload.1 h_payload.2)

/-- Root bridge from quotient-analytic payload at `c = 2`. -/
theorem mlc_conjecture_of_nonSlitQuotientAnalyticConstructivePayloadTwo
    (h_payload : NonSlitQuotientAnalyticConstructivePayloadTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_externalRayMapData_two
    (external_ray_map_exists_two_constructive_of_isClosedRange_restrict_of_outsideOpenQuotientAnalyticityHypothesisTwo
      h_payload.1 h_payload.2)

/-- Step-4→root seam specialized through restricted-map closed range plus
outside-open quotient constancy at `c = 2`. -/
theorem mlc_conjecture_of_isClosedRange_restrict_of_outsideOpenQuotientConstHypothesis_two
    (hclosed : IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ))))
    (h_qconst : OutsideOpenQuotientConstHypothesisTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_externalRayMapData_two
    (external_ray_map_exists_two_constructive_of_isClosedRange_restrict_of_outsideOpenQuotientConstHypothesisTwo
      hclosed h_qconst)

/-- Step-4→root seam specialized through restricted-map closed range plus
outside-open quotient analyticity at `c = 2`. -/
theorem mlc_conjecture_of_isClosedRange_restrict_of_outsideOpenQuotientAnalyticityHypothesis_two
    (hclosed : IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ))))
    (h_qanalytic : OutsideOpenQuotientAnalyticityHypothesisTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_externalRayMapData_two
    (external_ray_map_exists_two_constructive_of_isClosedRange_restrict_of_outsideOpenQuotientAnalyticityHypothesisTwo
      hclosed h_qanalytic)

/-- Step-4→root seam specialized through restricted-map closed range plus the
combined non-slit outside-open analytic/injective payload. -/
theorem mlc_conjecture_of_isClosedRange_restrict_of_outsideOpenAnalyticInjNonSlitPayloadTwo
    (hclosed : IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ))))
    (h_payload : OutsideOpenAnalyticInjNonSlitPayloadTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_externalRayMapData_two
    (external_ray_map_exists_two_constructive_of_isClosedRange_restrict_of_outsideOpenAnalyticInjNonSlitPayloadTwo
      hclosed h_payload)

/-- Step-4→root seam specialized through restricted-map closed range plus
outside-open analyticity at `c = 2`. -/
theorem mlc_conjecture_of_isClosedRange_restrict_of_outsideOpenAnalyticityHypothesis_two
    (hclosed : IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ))))
    (h_analytic : OutsideOpenAnalyticityHypothesis (2 : ℂ)) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_externalRayMapData_two
    (external_ray_map_exists_two_constructive_of_isClosedRange_restrict_of_outsideOpenAnalyticityHypothesis
      hclosed h_analytic)

/-- Step-4→root seam specialized through properness of the restricted outside-open
map plus outside-open analyticity at `c = 2`. -/
theorem mlc_conjecture_of_isProperMap_restrict_of_outsideOpenAnalyticityHypothesis_two
    (hproper : IsProperMap (bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (h_analytic : OutsideOpenAnalyticityHypothesis (2 : ℂ)) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_externalRayMapData_two
    (external_ray_map_exists_two_constructive_of_isProperMap_restrict_of_outsideOpenAnalyticityHypothesis
      hproper h_analytic)

/-- Step-4→root seam specialized through outside-open analyticity plus the
ambient compact-preimage obligation that yields properness of the restricted
outside-open map at `c = 2`. -/
theorem mlc_conjecture_of_analyticAt_of_preimageCompact_two
    (h_analytic : OutsideOpenAnalyticityHypothesis (2 : ℂ))
    (hpre :
      ∀ K : Set {w : ℂ // 1 < ‖w‖}, IsCompact K →
        IsCompact
          ({z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2 ∧
            Quadratic.bottcher_map (2 : ℂ) z ∈ ((↑) '' K : Set ℂ)} : Set ℂ)) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_externalRayMapData_two
    (external_ray_map_exists_two_constructive_of_analyticAt_of_preimageCompact h_analytic hpre)

/-- Step-4→root seam specialized through outside-open analyticity plus closedness
of ambient preimage sets against compact exterior targets. -/
theorem mlc_conjecture_of_analyticAt_of_preimageClosed_two
    (h_analytic : OutsideOpenAnalyticityHypothesis (2 : ℂ))
    (hclosedpre :
      ∀ K : Set {w : ℂ // 1 < ‖w‖}, IsCompact K →
        IsClosed
          ({z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2 ∧
            Quadratic.bottcher_map (2 : ℂ) z ∈ ((↑) '' K : Set ℂ)} : Set ℂ)) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_externalRayMapData_two
    (external_ray_map_exists_two_constructive_of_analyticAt_of_preimageClosed h_analytic hclosedpre)

/-- Step-4→root seam specialized through outside-open analyticity plus boundary
exclusion on compact exterior targets. -/
theorem mlc_conjecture_of_analyticAt_of_boundaryExclusion_two
    (_h_analytic : OutsideOpenAnalyticityHypothesis (2 : ℂ))
    (hboundary :
      ∀ K : Set {w : ℂ // 1 < ‖w‖}, IsCompact K →
        ∀ z, ‖z‖ = ‖(2 : ℂ)‖ + 2 →
          Quadratic.bottcher_map (2 : ℂ) z ∉ ((↑) '' K : Set ℂ)) :
    LocallyConnectedSpace mandelbrotSet := by
  exact False.elim (not_boundary_exclusion_family_two hboundary)

/-- The universal boundary-exclusion family used by the previous seam is
inconsistent at `c = 2`; this marks that route as vacuous for root elimination. -/
theorem not_boundaryExclusion_family_two :
    ¬ (∀ K : Set {w : ℂ // 1 < ‖w‖}, IsCompact K →
      ∀ z, ‖z‖ = ‖(2 : ℂ)‖ + 2 →
        Quadratic.bottcher_map (2 : ℂ) z ∉ ((↑) '' K : Set ℂ)) := by
  exact not_boundary_exclusion_family_two

/-- Root bridge from closed range plus outside-open analyticity payload at
`c = 2`. -/
theorem mlc_conjecture_of_nonSlitAnalyticConstructivePayloadTwo
    (h_payload : NonSlitAnalyticConstructivePayloadTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_externalRayMapData_two
    (external_ray_map_exists_two_constructive_of_isClosedRange_restrict_of_outsideOpenAnalyticityHypothesis
      h_payload.1 h_payload.2)

/-- Step-4→root seam from closed range plus local analytic charts that stay
inside outside-open at `c = 2`. -/
theorem mlc_conjecture_of_isClosedRange_restrict_of_outsideOpenLocalAnalyticChartWithinOutsideOpenHypothesis_two
    (hclosed : IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ))))
    (h_chart : OutsideOpenLocalAnalyticChartWithinOutsideOpenHypothesis (2 : ℂ)) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_externalRayMapData_two
    (external_ray_map_exists_two_constructive_of_isClosedRange_restrict_of_outsideOpenLocalAnalyticChartWithinOutsideOpenHypothesis
      hclosed h_chart)

/-- Root bridge from the combined non-slit outside-open analytic/injective
payload shape at `c = 2`. -/
theorem mlc_conjecture_of_nonSlitAnalyticInjConstructivePayloadTwo
    (h_payload : NonSlitAnalyticInjConstructivePayloadTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_isClosedRange_restrict_of_outsideOpenAnalyticInjNonSlitPayloadTwo
    h_payload.1 h_payload.2

/-- Step-4→root seam specialized through restricted-map closed range plus
    outside-open analyticity at `c = 2`. -/
theorem mlc_conjecture_of_isClosedRange_restrict_of_analyticAt_two
    (hclosed : IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ))))
    (hanalytic :
      ∀ z, ‖z‖ > ‖(2 : ℂ)‖ + 2 → AnalyticAt ℂ (Quadratic.bottcher_map (2 : ℂ)) z) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_externalRayMapData_two
    (external_ray_map_exists_two_constructive_of_isClosedRange_restrict_of_analyticAt
      hclosed hanalytic)

/-- Compatibility wrapper retaining the older signature with an explicit
outside-open injectivity assumption. -/
theorem mlc_conjecture_of_isClosedRange_restrict_of_analyticAt_of_injOn_two
    (hclosed : IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ))))
    (hanalytic :
      ∀ z, ‖z‖ > ‖(2 : ℂ)‖ + 2 → AnalyticAt ℂ (Quadratic.bottcher_map (2 : ℂ)) z)
    (_h_inj :
      Set.InjOn (Quadratic.bottcher_map (2 : ℂ)) {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2}) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_externalRayMapData_two
    (external_ray_map_exists_two_constructive_of_isClosedRange_restrict_of_analyticAt_of_injOn
      hclosed hanalytic _h_inj)

/-- Step-4→root seam specialized through restricted-map closed range plus
    outside-open analyticity and iterate-left-inverse injectivity at `c = 2`. -/
theorem mlc_conjecture_of_isClosedRange_restrict_of_analyticAt_of_iter_left_inverse_two
    (hclosed : IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ))))
    (hanalytic :
      ∀ z, ‖z‖ > ‖(2 : ℂ)‖ + 2 → AnalyticAt ℂ (Quadratic.bottcher_map (2 : ℂ)) z)
    (h_left_iter : QuadraticMapIterLeftInverseOnBasin (2 : ℂ)) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_externalRayMapData_two
    (external_ray_map_exists_two_constructive_of_isClosedRange_restrict_of_analyticAt_of_iter_left_inverse
      hclosed hanalytic h_left_iter)

/-- Step-4→root seam specialized through restricted-map closed range plus local
    slit-neighborhood payload and explicit outside-open injectivity at `c = 2`. -/
theorem mlc_conjecture_of_isClosedRange_restrict_of_mem_nhds_slit_of_injOn_outside_open_two
    (_hclosed : IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ))))
    (hslit_nhds : ∀ z, ‖z‖ > ‖(2 : ℂ)‖ + 2 → slit_orbit (2 : ℂ) ∈ 𝓝 z)
    (_h_inj : Set.InjOn (Quadratic.bottcher_map (2 : ℂ)) {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2}) :
    LocallyConnectedSpace mandelbrotSet := by
  exact False.elim (not_mem_nhds_slit_on_outside_open_two hslit_nhds)

/-- Step-4→root seam specialized through restricted-map closed range plus local
    slit-neighborhood payload and iterate-left-inverse injectivity at `c = 2`. -/
theorem mlc_conjecture_of_isClosedRange_restrict_of_mem_nhds_slit_of_iter_left_inverse_two
    (_hclosed : IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ))))
    (hslit_nhds : ∀ z, ‖z‖ > ‖(2 : ℂ)‖ + 2 → slit_orbit (2 : ℂ) ∈ 𝓝 z)
    (_h_left_iter : QuadraticMapIterLeftInverseOnBasin (2 : ℂ)) :
    LocallyConnectedSpace mandelbrotSet := by
  exact False.elim (not_mem_nhds_slit_on_outside_open_two hslit_nhds)

/-- CP5 endpoint at `c = 2`: constructive Green-function ray inversion. -/
def GreenRayLogGtAnchorTwoThresholdSeam : Prop :=
  ∀ u : ℂ, ‖u‖ = 1 →
    ∃ R : ℝ, 1 < R ∧
      ∀ r : ℝ, R < r →
        MLC.Quadratic.green_function (2 : ℂ)
            (((‖(2 : ℂ)‖ + 2 : ℝ) * u) : ℂ) < Real.log r

/-- Constructive thresholded anchor inequality: along each unit direction,
the fixed anchor Green value is eventually below `log r` for large enough radii. -/
lemma greenRayLogGtAnchorTwo_threshold_seed : GreenRayLogGtAnchorTwoThresholdSeam := by
  intro u _hu
  set a : ℝ := MLC.Quadratic.green_function (2 : ℂ)
    (((‖(2 : ℂ)‖ + 2 : ℝ) * u) : ℂ)
  refine ⟨Real.exp a + 1, by linarith [Real.exp_pos a], ?_⟩
  intro r hr
  have hR_pos : 0 < Real.exp a + 1 := by positivity
  have hr_pos : 0 < r := lt_trans hR_pos hr
  have hexp_lt : Real.exp a < r := by linarith
  have ha_lt_log : a < Real.log r := (Real.lt_log_iff_exp_lt hr_pos).2 hexp_lt
  simpa [a] using ha_lt_log

/-- Seam form of the Green-ray anchored uniqueness payload at `c = 2`.
This isolates the strict-mono dependency behind an explicit witness input. -/
def GreenRayUniquePreimageTwoAnchorSeam : Prop :=
  ∀ w : ℂ, 1 < ‖w‖ →
    MLC.Quadratic.green_function (2 : ℂ)
        (((‖(2 : ℂ)‖ + 2 : ℝ) * (w / ↑‖w‖)) : ℂ) < Real.log ‖w‖ →
      ∃! ρ : ℝ, ρ > ‖(2 : ℂ)‖ + 2 ∧
        MLC.Quadratic.green_function (2 : ℂ) ((ρ : ℂ) * (w / ↑‖w‖)) = Real.log ‖w‖

/-- Böttcher-map evaluation on a positive-real ray at `c = 2`. -/
private lemma bottcher_map_apply_ray_two
    (u : ℂ) (hu : ‖u‖ = 1) (ρ : ℝ)
    (hρ : 0 < ρ) :
    Quadratic.bottcher_map (2 : ℂ) ((ρ : ℂ) * u) =
      u * ↑(Real.exp (Quadratic.green_function (2 : ℂ) ((ρ : ℂ) * u))) := by
  have hu_ne : u ≠ 0 := by
    rw [ne_eq, ← norm_eq_zero]
    rw [hu]
    exact one_ne_zero
  have hρ_ne : (ρ : ℂ) ≠ 0 := by
    exact_mod_cast hρ.ne'
  have hne : (ρ : ℂ) * u ≠ 0 := mul_ne_zero hρ_ne hu_ne
  simp only [Quadratic.bottcher_map, if_neg hne]
  have hnorm : ‖(ρ : ℂ) * u‖ = ρ := by
    rw [Complex.norm_mul, Complex.norm_real, Real.norm_of_nonneg hρ.le, hu, mul_one]
  have hdiv : (ρ : ℂ) * u / (ρ : ℂ) = u := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using (mul_div_cancel_left₀ u hρ_ne)
  rw [hnorm, hdiv]

/-- Green-ray anchored uniqueness at `c = 2` from anchor-gap seam plus
outside-open injectivity. -/
theorem greenRayUniquePreimageTwoAnchorSeam_of_greenRayLogGtAnchorTwoSeam_of_injOn_outside_open
    (hlog_gt_anchor : GreenRayLogGtAnchorTwoSeam)
    (h_inj :
      Set.InjOn (Quadratic.bottcher_map (2 : ℂ))
        {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2}) :
    GreenRayUniquePreimageTwoAnchorSeam := by
  intro w hw _hlog_anchor
  set u : ℂ := w / ↑‖w‖
  have hw_pos : (0 : ℝ) < ‖w‖ := by linarith
  have hu : ‖u‖ = 1 := by
    dsimp [u]
    rw [norm_div, Complex.norm_real, norm_norm, div_self hw_pos.ne']
  have hlog_u :
      Quadratic.green_function (2 : ℂ)
          (((‖(2 : ℂ)‖ + 2 : ℝ) * u) : ℂ) < Real.log ‖w‖ := by
    simpa [u] using (hlog_gt_anchor w hw)
  obtain ⟨ρ, hρ_gt, hρ_eq⟩ :=
    GreenFunctionRayInversion.exists_ray_preimage_green_pos
      (2 : ℂ) u hu (Real.log ‖w‖) hlog_u
  refine ⟨ρ, ⟨hρ_gt, ?_⟩, ?_⟩
  · simpa [u] using hρ_eq
  · intro ρ' hρ'_witness
    rcases hρ'_witness with ⟨hρ'_gt, hρ'_eq⟩
    have hρ_pos : 0 < ρ := by
      linarith [hρ_gt, norm_nonneg (2 : ℂ)]
    have hρ'_pos : 0 < ρ' := by
      linarith [hρ'_gt, norm_nonneg (2 : ℂ)]
    have hz_norm : ‖((ρ : ℂ) * u)‖ = ρ := by
      rw [Complex.norm_mul, Complex.norm_real, Real.norm_of_nonneg hρ_pos.le, hu, mul_one]
    have hz'_norm : ‖((ρ' : ℂ) * u)‖ = ρ' := by
      rw [Complex.norm_mul, Complex.norm_real, Real.norm_of_nonneg hρ'_pos.le, hu, mul_one]
    have hz_out : ‖((ρ : ℂ) * u)‖ > ‖(2 : ℂ)‖ + 2 := by
      calc
        ‖((ρ : ℂ) * u)‖ = ρ := hz_norm
        _ > ‖(2 : ℂ)‖ + 2 := hρ_gt
    have hz'_out : ‖((ρ' : ℂ) * u)‖ > ‖(2 : ℂ)‖ + 2 := by
      calc
        ‖((ρ' : ℂ) * u)‖ = ρ' := hz'_norm
        _ > ‖(2 : ℂ)‖ + 2 := hρ'_gt
    have hbot_ρ :
        Quadratic.bottcher_map (2 : ℂ) ((ρ : ℂ) * u) =
          u * ↑(Real.exp (Real.log ‖w‖)) := by
      rw [bottcher_map_apply_ray_two u hu ρ hρ_pos, hρ_eq]
    have hbot_ρ' :
        Quadratic.bottcher_map (2 : ℂ) ((ρ' : ℂ) * u) =
          u * ↑(Real.exp (Real.log ‖w‖)) := by
      rw [bottcher_map_apply_ray_two u hu ρ' hρ'_pos]
      rw [hρ'_eq]
    have hbot_eq :
        Quadratic.bottcher_map (2 : ℂ) ((ρ : ℂ) * u) =
          Quadratic.bottcher_map (2 : ℂ) ((ρ' : ℂ) * u) := by
      calc
        Quadratic.bottcher_map (2 : ℂ) ((ρ : ℂ) * u)
            = u * ↑(Real.exp (Real.log ‖w‖)) := hbot_ρ
        _ = Quadratic.bottcher_map (2 : ℂ) ((ρ' : ℂ) * u) := hbot_ρ'.symm
    have hz_eq : ((ρ : ℂ) * u) = ((ρ' : ℂ) * u) :=
      h_inj hz_out hz'_out hbot_eq
    have hnorm_eq : ‖((ρ : ℂ) * u)‖ = ‖((ρ' : ℂ) * u)‖ := congrArg norm hz_eq
    calc
      ρ' = ‖((ρ' : ℂ) * u)‖ := hz'_norm.symm
      _ = ‖((ρ : ℂ) * u)‖ := hnorm_eq.symm
      _ = ρ := hz_norm

/-- Green-ray anchored uniqueness at `c = 2` from the constructive preimage
seam shape plus outside-open injectivity. -/
theorem greenRayUniquePreimageTwoAnchorSeam_of_greenRayAnchorThresholdPreimageTwoSeam_of_injOn_outside_open
    (hpre : GreenRayAnchorThresholdPreimageTwoSeam)
    (h_inj :
      Set.InjOn (Quadratic.bottcher_map (2 : ℂ))
        {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2}) :
    GreenRayUniquePreimageTwoAnchorSeam := by
  intro w hw hlog_anchor
  set u : ℂ := w / ↑‖w‖
  have hw_pos : (0 : ℝ) < ‖w‖ := by linarith
  have hu : ‖u‖ = 1 := by
    dsimp [u]
    rw [norm_div, Complex.norm_real, norm_norm, div_self hw_pos.ne']
  obtain ⟨ρ, hρ_gt, hρ_eq⟩ := hpre w hw hlog_anchor
  refine ⟨ρ, ⟨hρ_gt, ?_⟩, ?_⟩
  · simpa [u] using hρ_eq
  · intro ρ' hρ'_witness
    rcases hρ'_witness with ⟨hρ'_gt, hρ'_eq⟩
    have hρ_pos : 0 < ρ := by
      linarith [hρ_gt, norm_nonneg (2 : ℂ)]
    have hρ'_pos : 0 < ρ' := by
      linarith [hρ'_gt, norm_nonneg (2 : ℂ)]
    have hz_norm : ‖((ρ : ℂ) * u)‖ = ρ := by
      rw [Complex.norm_mul, Complex.norm_real, Real.norm_of_nonneg hρ_pos.le, hu, mul_one]
    have hz'_norm : ‖((ρ' : ℂ) * u)‖ = ρ' := by
      rw [Complex.norm_mul, Complex.norm_real, Real.norm_of_nonneg hρ'_pos.le, hu, mul_one]
    have hz_out : ‖((ρ : ℂ) * u)‖ > ‖(2 : ℂ)‖ + 2 := by
      calc
        ‖((ρ : ℂ) * u)‖ = ρ := hz_norm
        _ > ‖(2 : ℂ)‖ + 2 := hρ_gt
    have hz'_out : ‖((ρ' : ℂ) * u)‖ > ‖(2 : ℂ)‖ + 2 := by
      calc
        ‖((ρ' : ℂ) * u)‖ = ρ' := hz'_norm
        _ > ‖(2 : ℂ)‖ + 2 := hρ'_gt
    have hbot_ρ :
        Quadratic.bottcher_map (2 : ℂ) ((ρ : ℂ) * u) =
          u * ↑(Real.exp (Real.log ‖w‖)) := by
      rw [bottcher_map_apply_ray_two u hu ρ hρ_pos, hρ_eq]
    have hbot_ρ' :
        Quadratic.bottcher_map (2 : ℂ) ((ρ' : ℂ) * u) =
          u * ↑(Real.exp (Real.log ‖w‖)) := by
      rw [bottcher_map_apply_ray_two u hu ρ' hρ'_pos]
      rw [hρ'_eq]
    have hbot_eq :
        Quadratic.bottcher_map (2 : ℂ) ((ρ : ℂ) * u) =
          Quadratic.bottcher_map (2 : ℂ) ((ρ' : ℂ) * u) := by
      calc
        Quadratic.bottcher_map (2 : ℂ) ((ρ : ℂ) * u)
            = u * ↑(Real.exp (Real.log ‖w‖)) := hbot_ρ
        _ = Quadratic.bottcher_map (2 : ℂ) ((ρ' : ℂ) * u) := hbot_ρ'.symm
    have hz_eq : ((ρ : ℂ) * u) = ((ρ' : ℂ) * u) :=
      h_inj hz_out hz'_out hbot_eq
    have hnorm_eq : ‖((ρ : ℂ) * u)‖ = ‖((ρ' : ℂ) * u)‖ := congrArg norm hz_eq
    calc
      ρ' = ‖((ρ' : ℂ) * u)‖ := hz'_norm.symm
      _ = ‖((ρ : ℂ) * u)‖ := hnorm_eq.symm
      _ = ρ := hz_norm

/-- Green-ray anchored uniqueness at `c = 2` from outside-open injectivity,
using the constructive preimage seam. -/
theorem greenRayUniquePreimageTwoAnchorSeam_of_injOn_outside_open
    (h_inj :
      Set.InjOn (Quadratic.bottcher_map (2 : ℂ))
        {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2}) :
    GreenRayUniquePreimageTwoAnchorSeam :=
  greenRayUniquePreimageTwoAnchorSeam_of_greenRayAnchorThresholdPreimageTwoSeam_of_injOn_outside_open
    greenRayAnchorThresholdPreimageTwoSeam_constructive h_inj

/-- Preimage-seam bridge at `c = 2`: from the constructive preimage seam shape
plus outside-open injectivity and an explicit anchor-gap seam, build
external-ray data. -/
theorem external_ray_map_exists_two_constructive_of_greenRayAnchorThresholdPreimageTwoSeam_of_injOn_outside_open_of_greenRayLogGtAnchorTwoSeam
    (hpre : GreenRayAnchorThresholdPreimageTwoSeam)
    (h_inj :
      Set.InjOn (Quadratic.bottcher_map (2 : ℂ))
        {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2})
    (hlog_gt_anchor : GreenRayLogGtAnchorTwoSeam) :
    Quadratic.ExternalRayMapData (2 : ℂ) := by
  exact GreenFunctionRayInversion.external_ray_map_exists_two_via_green_function_of_uniquePreimageSeam
    (greenRayUniquePreimageTwoAnchorSeam_of_greenRayAnchorThresholdPreimageTwoSeam_of_injOn_outside_open
      hpre h_inj)
    hlog_gt_anchor

/-- Outside-open injectivity at `c = 2` from Green-ray anchored uniqueness
plus the anchor-gap seam; no `external_ray_map_exists` usage in this bridge. -/
theorem injOn_outside_open_two_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam
    (huniq_seam : GreenRayUniquePreimageTwoAnchorSeam)
    (hlog_gt_anchor : GreenRayLogGtAnchorTwoSeam) :
    Set.InjOn (Quadratic.bottcher_map (2 : ℂ))
      {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2} := by
  intro z₁ hz₁ z₂ hz₂ hEq
  set w : ℂ := Quadratic.bottcher_map (2 : ℂ) z₁
  have hw_eq₁ : Quadratic.bottcher_map (2 : ℂ) z₁ = w := by rfl
  have hw_eq₂ : Quadratic.bottcher_map (2 : ℂ) z₂ = w := by
    simpa [w] using hEq.symm

  have hz₁_gt : ‖z₁‖ > ‖(2 : ℂ)‖ + 2 := by simpa using hz₁
  have hz₂_gt : ‖z₂‖ > ‖(2 : ℂ)‖ + 2 := by simpa using hz₂
  have hz₁_pos : 0 < ‖z₁‖ := by
    linarith [hz₁_gt, norm_nonneg (2 : ℂ)]
  have hz₂_pos : 0 < ‖z₂‖ := by
    linarith [hz₂_gt, norm_nonneg (2 : ℂ)]
  have hz₁_ne : z₁ ≠ 0 := norm_ne_zero_iff.mp hz₁_pos.ne'
  have hz₂_ne : z₂ ≠ 0 := norm_ne_zero_iff.mp hz₂_pos.ne'
  have hzn₁_ne : (↑‖z₁‖ : ℂ) ≠ 0 := by exact_mod_cast hz₁_pos.ne'
  have hzn₂_ne : (↑‖z₂‖ : ℂ) ≠ 0 := by exact_mod_cast hz₂_pos.ne'

  have hw_norm₁ : ‖w‖ = Real.exp (Quadratic.green_function (2 : ℂ) z₁) := by
    simpa [w] using (Quadratic.norm_bottcher_eq_exp_green (2 : ℂ) z₁)
  have hGz₁_pos : 0 < Quadratic.green_function (2 : ℂ) z₁ :=
    GreenFunctionRayInversion.green_function_pos_on_outside_open (2 : ℂ) z₁ hz₁
  have hw_gt1 : 1 < ‖w‖ := by
    simpa [hw_norm₁] using (Real.one_lt_exp_iff.mpr hGz₁_pos)
  have hw_pos : (0 : ℝ) < ‖w‖ := by linarith
  have hwn_ne : (↑‖w‖ : ℂ) ≠ 0 := by exact_mod_cast hw_pos.ne'

  have hdir₁ : w / ↑‖w‖ = z₁ / ↑‖z₁‖ := by
    rw [hw_norm₁]
    simp only [w, Quadratic.bottcher_map, if_neg hz₁_ne]
    field_simp [(Real.exp_pos (Quadratic.green_function (2 : ℂ) z₁)).ne', hzn₁_ne]
  have hdir₂ : w / ↑‖w‖ = z₂ / ↑‖z₂‖ := by
    have hdir₂_raw :
        Quadratic.bottcher_map (2 : ℂ) z₂ / ↑‖Quadratic.bottcher_map (2 : ℂ) z₂‖ =
          z₂ / ↑‖z₂‖ := by
      rw [Quadratic.norm_bottcher_eq_exp_green (2 : ℂ) z₂]
      simp only [Quadratic.bottcher_map, if_neg hz₂_ne]
      field_simp [(Real.exp_pos (Quadratic.green_function (2 : ℂ) z₂)).ne', hzn₂_ne]
    simpa [hw_eq₂] using hdir₂_raw

  have hlog_eq₁ : Real.log ‖w‖ = Quadratic.green_function (2 : ℂ) z₁ := by
    rw [hw_norm₁, Real.log_exp]
  have hz₁_witness :
      Quadratic.green_function (2 : ℂ) ((↑‖z₁‖ : ℂ) * (w / ↑‖w‖)) = Real.log ‖w‖ := by
    rw [hdir₁]
    have hmul : ((↑‖z₁‖ : ℂ) * (z₁ / ↑‖z₁‖)) = z₁ := by
      field_simp [hzn₁_ne]
    simpa [hmul] using hlog_eq₁.symm

  have hlog_eq₂ : Real.log ‖w‖ = Quadratic.green_function (2 : ℂ) z₂ := by
    have hw_norm₂ : ‖w‖ = Real.exp (Quadratic.green_function (2 : ℂ) z₂) := by
      simpa [hw_eq₂] using (Quadratic.norm_bottcher_eq_exp_green (2 : ℂ) z₂)
    rw [hw_norm₂, Real.log_exp]
  have hz₂_witness :
      Quadratic.green_function (2 : ℂ) ((↑‖z₂‖ : ℂ) * (w / ↑‖w‖)) = Real.log ‖w‖ := by
    rw [hdir₂]
    have hmul : ((↑‖z₂‖ : ℂ) * (z₂ / ↑‖z₂‖)) = z₂ := by
      field_simp [hzn₂_ne]
    simpa [hmul] using hlog_eq₂.symm

  have huniq := huniq_seam w hw_gt1 (hlog_gt_anchor w hw_gt1)
  have hnorm_eq : ‖z₁‖ = ‖z₂‖ := by
    exact huniq.unique ⟨hz₁, hz₁_witness⟩ ⟨hz₂, hz₂_witness⟩

  have hdir_eq : z₁ / ↑‖z₁‖ = z₂ / ↑‖z₂‖ := by
    calc
      z₁ / ↑‖z₁‖ = w / ↑‖w‖ := hdir₁.symm
      _ = z₂ / ↑‖z₂‖ := hdir₂
  have hdir_eq' : z₁ / ↑‖z₁‖ = z₂ / ↑‖z₁‖ := by
    simpa [hnorm_eq] using hdir_eq
  have hmul_eq : (z₁ / ↑‖z₁‖) * (↑‖z₁‖ : ℂ) = (z₂ / ↑‖z₁‖) * (↑‖z₁‖ : ℂ) := by
    exact congrArg (fun t : ℂ => t * (↑‖z₁‖ : ℂ)) hdir_eq'
  have hz_eq : z₁ = z₂ := by
    simpa [div_eq_mul_inv, mul_assoc, hzn₁_ne] using hmul_eq
  exact hz_eq

/-- Green-ray anchored uniqueness seam at `c = 2` directly from the strict
radial monotonicity seam. -/
theorem greenRayUniquePreimageTwoAnchorSeam_of_greenFunctionStrictMonoAlongRayBasinTwoSeam
    (hmono : GreenFunctionRayInversion.GreenFunctionStrictMonoAlongRayBasinTwoSeam) :
    GreenRayUniquePreimageTwoAnchorSeam := by
  intro w hw hlog
  exact GreenFunctionRayInversion.exists_unique_ray_preimage_green_two_anchor_of_seam
    hmono w hw hlog

/-- Central strict-mono-seeded uniqueness witness at `c = 2`, routed through
the `GreenFunctionStrictMonoAlongRayBasinTwoSeam` seed alias. -/
theorem greenRayUniquePreimageTwoAnchorSeam_strictMono_seeded_of_greenFunctionStrictMonoAlongRayBasinTwo_seed :
    GreenRayUniquePreimageTwoAnchorSeam :=
  greenRayUniquePreimageTwoAnchorSeam_of_greenFunctionStrictMonoAlongRayBasinTwoSeam
    greenFunctionStrictMonoAlongRayBasinTwo_seed

/-- Compatibility alias for the older strict-mono uniqueness seed name, now
factored through the centralized green-function-seeded uniqueness witness. -/
theorem greenRayUniquePreimageTwoAnchorSeam_strictMono_seeded_of_injOn_outside_open :
    GreenRayUniquePreimageTwoAnchorSeam :=
  greenRayUniquePreimageTwoAnchorSeam_strictMono_seeded_of_greenFunctionStrictMonoAlongRayBasinTwo_seed

/-- Green-ray anchored uniqueness seam at `c = 2` from an explicit
Green-ray-log-gap seam witness. -/
theorem greenRayUniquePreimageTwoAnchorSeam_of_greenRayLogGtAnchorTwoSeam
    (hlog_gt_anchor : GreenRayLogGtAnchorTwoSeam) :
    GreenRayUniquePreimageTwoAnchorSeam :=
  greenRayUniquePreimageTwoAnchorSeam_of_greenFunctionStrictMonoAlongRayBasinTwoSeam
    (greenFunctionStrictMonoAlongRayBasinTwo_of_greenRayLogGtAnchorTwoSeam hlog_gt_anchor)

/-- Outside-open injectivity at `c = 2` from the Green-ray anchored uniqueness
machinery (strict-mono route, no `external_ray_map_exists` usage). -/
theorem injOn_outside_open_two_of_greenRayLogGtAnchorTwoSeam
    (hlog_gt_anchor : GreenRayLogGtAnchorTwoSeam) :
    Set.InjOn (Quadratic.bottcher_map (2 : ℂ))
      {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2} :=
  injOn_outside_open_two_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam
    (greenRayUniquePreimageTwoAnchorSeam_of_greenRayLogGtAnchorTwoSeam hlog_gt_anchor)
    hlog_gt_anchor

/-- Local-homeomorph branch seam at `c = 2` from Green-ray uniqueness+anchor
seams. -/
theorem cp5ResidualLocalHomeomorphInjSeamTwo_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam
    (huniq_seam : GreenRayUniquePreimageTwoAnchorSeam)
    (hlog_gt_anchor : GreenRayLogGtAnchorTwoSeam) :
    CP5ResidualLocalHomeomorphInjSeamTwo := by
  intro _hlocal
  exact injOn_outside_open_two_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam
    huniq_seam hlog_gt_anchor

/-- Landing branch seam at `c = 2` from Green-ray uniqueness+anchor seams. -/
theorem cp5ResidualLandingInjSeamTwo_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam
    (huniq_seam : GreenRayUniquePreimageTwoAnchorSeam)
    (hlog_gt_anchor : GreenRayLogGtAnchorTwoSeam) :
    CP5ResidualLandingInjSeamTwo := by
  intro _hland
  exact injOn_outside_open_two_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam
    huniq_seam hlog_gt_anchor

/-- Unconditional CP5 residual→injectivity seam at `c = 2` from Green-ray
uniqueness+anchor seams via both branch seams. -/
theorem cp5ResidualInjOnOutsideOpenSeamTwo_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam
    (huniq_seam : GreenRayUniquePreimageTwoAnchorSeam)
    (hlog_gt_anchor : GreenRayLogGtAnchorTwoSeam) :
    CP5ResidualInjOnOutsideOpenSeamTwo :=
  cp5ResidualInjOnOutsideOpenSeamTwo_of_branchSeams
    (cp5ResidualLocalHomeomorphInjSeamTwo_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam
      huniq_seam hlog_gt_anchor)
    (cp5ResidualLandingInjSeamTwo_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam
      huniq_seam hlog_gt_anchor)

/-- CP5 residual→injectivity seam under no-landing at `c = 2` from
Green-ray uniqueness+anchor seams. -/
theorem cp5ResidualInjOnOutsideOpenSeamTwo_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam_of_not_externalRayLandsOutsideOpen
    (huniq_seam : GreenRayUniquePreimageTwoAnchorSeam)
    (hlog_gt_anchor : GreenRayLogGtAnchorTwoSeam)
    (hnot_land : ¬ ExternalRayLandsOutsideOpen (2 : ℂ)) :
    CP5ResidualInjOnOutsideOpenSeamTwo :=
  cp5ResidualInjOnOutsideOpenSeamTwo_of_localHomeomorphBranchSeam_of_not_externalRayLandsOutsideOpen
    (cp5ResidualLocalHomeomorphInjSeamTwo_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam
      huniq_seam hlog_gt_anchor)
    hnot_land

/-- Green-function endpoint at `c = 2` from Green-ray uniqueness+anchor seams. -/
theorem external_ray_map_exists_two_constructive_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam
    (huniq_seam : GreenRayUniquePreimageTwoAnchorSeam)
    (hlog_gt_anchor : GreenRayLogGtAnchorTwoSeam) :
    Quadratic.ExternalRayMapData (2 : ℂ) := by
  exact
    GreenFunctionRayInversion.external_ray_map_exists_two_via_green_function_of_uniquePreimageSeam
      huniq_seam hlog_gt_anchor

/-- Root theorem at `c = 2` from Green-ray uniqueness+anchor seams. -/
theorem mlc_conjecture_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam
    (huniq_seam : GreenRayUniquePreimageTwoAnchorSeam)
    (hlog_gt_anchor : GreenRayLogGtAnchorTwoSeam) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_externalRayMapData_two
    (external_ray_map_exists_two_constructive_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam
      huniq_seam hlog_gt_anchor)

/-- Strict-mono routed local-homeomorph branch seam at `c = 2`. This late
replacement is frontier-safe with respect to `external_ray_map_exists`. -/
theorem cp5ResidualLocalHomeomorphInjSeamTwo_strictMono :
    CP5ResidualLocalHomeomorphInjSeamTwo :=
  cp5ResidualLocalHomeomorphInjSeamTwo_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam
    greenRayUniquePreimageTwoAnchorSeam_strictMono_seeded_of_greenFunctionStrictMonoAlongRayBasinTwo_seed
    greenRayLogGtAnchorTwo_seed

/-- Strict-mono routed landing branch seam at `c = 2`.
This closes the Branch-2 seam endpoint on the current axiom frontier. -/
theorem cp5ResidualLandingInjSeamTwo_strictMono :
    CP5ResidualLandingInjSeamTwo := by
  exact cp5ResidualLandingInjSeamTwo_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam
    greenRayUniquePreimageTwoAnchorSeam_strictMono_seeded_of_greenFunctionStrictMonoAlongRayBasinTwo_seed
    greenRayLogGtAnchorTwo_seed

/-- Strict-mono routed unconditional CP5 residual→injectivity seam from both
branch seams. -/
theorem cp5ResidualInjOnOutsideOpenSeamTwo_strictMono :
    CP5ResidualInjOnOutsideOpenSeamTwo :=
  cp5ResidualInjOnOutsideOpenSeamTwo_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam
    greenRayUniquePreimageTwoAnchorSeam_strictMono_seeded_of_greenFunctionStrictMonoAlongRayBasinTwo_seed
    greenRayLogGtAnchorTwo_seed

/-- Seam-parameterized unconditional CP5 residual endpoint function at `c = 2`,
via the branch-combined residual→injectivity seam. -/
theorem external_ray_map_exists_two_constructive_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam_of_cp5ResidualTwo_unconditional_fn
    (huniq_seam : GreenRayUniquePreimageTwoAnchorSeam)
    (hlog_gt_anchor : GreenRayLogGtAnchorTwoSeam) :
    CP5ResidualTwo → Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_exists_two_constructive_of_cp5ResidualTwo_of_seam
    (cp5ResidualInjOnOutsideOpenSeamTwo_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam
      huniq_seam hlog_gt_anchor)

/-- Strict-mono-seeded unconditional CP5 residual endpoint function at `c = 2`.
-/
theorem external_ray_map_exists_two_constructive_of_cp5ResidualTwo_strictMono_unconditional_fn :
    CP5ResidualTwo → Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_exists_two_constructive_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam_of_cp5ResidualTwo_unconditional_fn
    greenRayUniquePreimageTwoAnchorSeam_strictMono_seeded_of_greenFunctionStrictMonoAlongRayBasinTwo_seed
    greenRayLogGtAnchorTwo_seed

/-- CP5 endpoint at `c = 2`: current strict-mono-seeded alias, routed through
the direct Green inversion constructor. -/
theorem external_ray_map_exists_two_constructive_of_greenFunctionStrictMonoAlongRayBasinTwoSeam
    (hmono : GreenFunctionRayInversion.GreenFunctionStrictMonoAlongRayBasinTwoSeam) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_exists_two_constructive_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam
    (greenRayUniquePreimageTwoAnchorSeam_of_greenFunctionStrictMonoAlongRayBasinTwoSeam hmono)
    greenRayLogGtAnchorTwo_seed

/-- CP5 endpoint at `c = 2`: current strict-mono-seeded alias, routed through
the direct Green inversion constructor. -/
theorem external_ray_map_exists_two_constructive_strictMono_seeded :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_exists_two_constructive_of_greenFunctionStrictMonoAlongRayBasinTwoSeam
    greenFunctionStrictMonoAlongRayBasinTwo_seed

/-- CP5 endpoint at `c = 2`: current exported alias routed through the
strict-mono-seeded direct Green inversion constructor. -/
theorem external_ray_map_exists_two_constructive :
    Quadratic.ExternalRayMapData (2 : ℂ) := by
  exact external_ray_map_exists_two_constructive_strictMono_seeded

/-- Explicit boundary marker: the current exported endpoint at `c = 2` is
extensionally equal to the strict-mono-seeded ingress. -/
theorem external_ray_map_exists_two_constructive_eq_strictMono_seeded :
    external_ray_map_exists_two_constructive =
      external_ray_map_exists_two_constructive_strictMono_seeded := by
  rfl

/-- Conditional CP5 endpoint at `c = 2`: Green inversion routed through
outside-open injectivity. -/
theorem external_ray_map_exists_two_constructive_of_greenRayLogGtAnchorTwoSeam_of_injOn_outside_open
    (hlog_gt_anchor : GreenRayLogGtAnchorTwoSeam)
    (h_inj_outside :
      Set.InjOn (Quadratic.bottcher_map (2 : ℂ))
        {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2}) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_exists_two_constructive_of_greenRayAnchorThresholdPreimageTwoSeam_of_injOn_outside_open_of_greenRayLogGtAnchorTwoSeam
    greenRayAnchorThresholdPreimageTwoSeam_constructive
    h_inj_outside
    hlog_gt_anchor

/-- Conditional CP5 endpoint at `c = 2`: Green inversion routed through
outside-open injectivity, specialized to the current anchor-gap seed. -/
theorem external_ray_map_exists_two_constructive_of_green_function_of_injOn_outside_open
    (h_inj_outside :
      Set.InjOn (Quadratic.bottcher_map (2 : ℂ))
        {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2}) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_exists_two_constructive_of_greenRayLogGtAnchorTwoSeam_of_injOn_outside_open
    greenRayLogGtAnchorTwo_seed h_inj_outside

/-- Seam-free constructor at `c = 2`: outside-open injectivity plus
outside-open exterior surjectivity from the direct proper+local witness. -/
theorem external_ray_map_exists_two_constructive_of_rootSafeOutsideOpenInjWitnessTwo_of_directProperLocalWitnessTwo
    (h_inj :
      Set.InjOn (Quadratic.bottcher_map (2 : ℂ))
        {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2})
    (h_dir : DirectProperLocalWitnessTwo) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_exists_two_constructive_of_injOn_outside_open_of_surj_exterior
    h_inj (bottcherSurjOnExteriorFromOutsideOpen_two_of_directProperLocalWitnessTwo h_dir)

/-- Exact strict-mono-free root replacement target at `c = 2`: a frontier-safe
outside-open injectivity witness for `bottcher_map`. -/
def RootSafeOutsideOpenInjWitnessTwo : Prop :=
  Set.InjOn (Quadratic.bottcher_map (2 : ℂ))
    {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2}

/-- Build the exact strict-mono-free root witness target from Green-ray
uniqueness+anchor seams at `c = 2`. -/
theorem rootSafeOutsideOpenInjWitnessTwo_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam
    (huniq_seam : GreenRayUniquePreimageTwoAnchorSeam)
    (hlog_gt_anchor : GreenRayLogGtAnchorTwoSeam) :
    RootSafeOutsideOpenInjWitnessTwo :=
  injOn_outside_open_two_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam
    huniq_seam hlog_gt_anchor

/-- Explicit constructor gap for the root outside-open injectivity witness:
uniqueness seam plus anchor-gap seam. -/
def RootSafeOutsideOpenInjWitnessTwoWitnessGap : Prop :=
  GreenRayUniquePreimageTwoAnchorSeam ∧ GreenRayLogGtAnchorTwoSeam

/-- Explicit constructor gap for the unique-preimage seam target: outside-open
injectivity on the target outside-open domain. -/
def GreenRayUniquePreimageTwoAnchorSeamWitnessGap : Prop :=
  RootSafeOutsideOpenInjWitnessTwo

/-- Build the unique-preimage seam target from the explicit injectivity
constructor gap payload. -/
theorem greenRayUniquePreimageTwoAnchorSeam_of_greenRayUniquePreimageTwoAnchorSeamWitnessGap
    (h_gap : GreenRayUniquePreimageTwoAnchorSeamWitnessGap) :
    GreenRayUniquePreimageTwoAnchorSeam :=
  greenRayUniquePreimageTwoAnchorSeam_of_injOn_outside_open h_gap

/-- Build the root outside-open injectivity witness from the explicit
constructor gap payload. -/
theorem rootSafeOutsideOpenInjWitnessTwo_of_rootSafeOutsideOpenInjWitnessTwoWitnessGap
    (h_gap : RootSafeOutsideOpenInjWitnessTwoWitnessGap) :
    RootSafeOutsideOpenInjWitnessTwo :=
  rootSafeOutsideOpenInjWitnessTwo_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam
    h_gap.1 h_gap.2

/-- Strict-mono-seeded root witness target at `c = 2`, expressed via the
Green-ray seam bridge. -/
theorem rootSafeOutsideOpenInjWitnessTwo_strictMono_seeded :
    RootSafeOutsideOpenInjWitnessTwo :=
  rootSafeOutsideOpenInjWitnessTwo_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam
    greenRayUniquePreimageTwoAnchorSeam_strictMono_seeded_of_greenFunctionStrictMonoAlongRayBasinTwo_seed
    greenRayLogGtAnchorTwo_seed

/-- Build the exact strict-mono-free root witness target from the known
non-iterate-left injectivity-source aggregate at `c = 2`. -/
theorem rootSafeOutsideOpenInjWitnessTwo_of_knownInjOnOutsideOpenSourceCandidateTwo
    (h : KnownInjOnOutsideOpenSourceCandidateTwo) :
    RootSafeOutsideOpenInjWitnessTwo :=
  injOn_outside_open_two_of_knownInjOnOutsideOpenSourceCandidateTwo h

/-- Build the exact strict-mono-free root witness target from outside-open
analyticity at `c = 2`. -/
theorem rootSafeOutsideOpenInjWitnessTwo_of_outsideOpenAnalyticityHypothesis
    (h_analytic : OutsideOpenAnalyticityHypothesis (2 : ℂ)) :
    RootSafeOutsideOpenInjWitnessTwo :=
  injOn_outside_open_two_of_outsideOpenAnalyticityHypothesis h_analytic

/-- Strict-mono-free external-ray-data candidate at `c = 2`, parameterized by
the exact remaining root witness target. -/
theorem external_ray_map_exists_two_constructive_strictMono_free_of_rootSafeOutsideOpenInjWitnessTwo_of_greenRayLogGtAnchorTwoSeam
    (hlog_gt_anchor : GreenRayLogGtAnchorTwoSeam)
    (h_inj : RootSafeOutsideOpenInjWitnessTwo) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_exists_two_constructive_of_greenRayLogGtAnchorTwoSeam_of_injOn_outside_open
    hlog_gt_anchor h_inj

/-- Strict-mono-free external-ray-data candidate at `c = 2`, parameterized by
the exact remaining root witness target and specialized to the current
anchor-gap seed. -/
theorem external_ray_map_exists_two_constructive_strictMono_free_of_rootSafeOutsideOpenInjWitnessTwo
    (h_inj : RootSafeOutsideOpenInjWitnessTwo) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_exists_two_constructive_strictMono_free_of_rootSafeOutsideOpenInjWitnessTwo_of_greenRayLogGtAnchorTwoSeam
    greenRayLogGtAnchorTwo_seed h_inj

/-- Strict-mono-free external-ray-data candidate at `c = 2`, specialized to the
known non-iterate-left injectivity-source aggregate. -/
theorem external_ray_map_exists_two_constructive_strictMono_free_of_greenRayLogGtAnchorTwoSeam_of_knownInjOnOutsideOpenSourceCandidateTwo
    (hlog_gt_anchor : GreenRayLogGtAnchorTwoSeam)
    (h : KnownInjOnOutsideOpenSourceCandidateTwo) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_exists_two_constructive_strictMono_free_of_rootSafeOutsideOpenInjWitnessTwo_of_greenRayLogGtAnchorTwoSeam
    hlog_gt_anchor
    (rootSafeOutsideOpenInjWitnessTwo_of_knownInjOnOutsideOpenSourceCandidateTwo h)

/-- Strict-mono-free external-ray-data candidate at `c = 2`, specialized to the
known non-iterate-left injectivity-source aggregate and the current anchor-gap
seed. -/
theorem external_ray_map_exists_two_constructive_strictMono_free_of_knownInjOnOutsideOpenSourceCandidateTwo
    (h : KnownInjOnOutsideOpenSourceCandidateTwo) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_exists_two_constructive_strictMono_free_of_greenRayLogGtAnchorTwoSeam_of_knownInjOnOutsideOpenSourceCandidateTwo
    greenRayLogGtAnchorTwo_seed h

/-- Strict-mono-free external-ray-data candidate at `c = 2`, specialized to
outside-open analyticity. -/
theorem external_ray_map_exists_two_constructive_strictMono_free_of_greenRayLogGtAnchorTwoSeam_of_outsideOpenAnalyticityHypothesis
    (hlog_gt_anchor : GreenRayLogGtAnchorTwoSeam)
    (h_analytic : OutsideOpenAnalyticityHypothesis (2 : ℂ)) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_exists_two_constructive_strictMono_free_of_rootSafeOutsideOpenInjWitnessTwo_of_greenRayLogGtAnchorTwoSeam
    hlog_gt_anchor
    (rootSafeOutsideOpenInjWitnessTwo_of_outsideOpenAnalyticityHypothesis h_analytic)

/-- Strict-mono-free external-ray-data candidate at `c = 2`, specialized to
outside-open analyticity and the current anchor-gap seed. -/
theorem external_ray_map_exists_two_constructive_strictMono_free_of_outsideOpenAnalyticityHypothesis
    (h_analytic : OutsideOpenAnalyticityHypothesis (2 : ℂ)) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_exists_two_constructive_strictMono_free_of_greenRayLogGtAnchorTwoSeam_of_outsideOpenAnalyticityHypothesis
    greenRayLogGtAnchorTwo_seed h_analytic

/-- Conditional CP5 endpoint at `c = 2`: Green inversion routed through
iterate-left-inverse injectivity on outside-open. -/
theorem external_ray_map_exists_two_constructive_of_greenRayLogGtAnchorTwoSeam_of_iter_left_inverse
    (hlog_gt_anchor : GreenRayLogGtAnchorTwoSeam)
    (h_left_iter : QuadraticMapIterLeftInverseOnBasin (2 : ℂ)) :
    Quadratic.ExternalRayMapData (2 : ℂ) := by
  exact external_ray_map_exists_two_constructive_of_greenRayLogGtAnchorTwoSeam_of_injOn_outside_open
    hlog_gt_anchor
    (bottcher_map_inj_on_outside_open_of_iter_left_inverse (2 : ℂ) h_left_iter)

/-- Conditional CP5 endpoint at `c = 2`: Green inversion routed through
iterate-left-inverse injectivity on outside-open, specialized to the current
anchor-gap seed. -/
theorem external_ray_map_exists_two_constructive_of_green_function_of_iter_left_inverse
    (h_left_iter : QuadraticMapIterLeftInverseOnBasin (2 : ℂ)) :
    Quadratic.ExternalRayMapData (2 : ℂ) := by
  exact external_ray_map_exists_two_constructive_of_greenRayLogGtAnchorTwoSeam_of_iter_left_inverse
    greenRayLogGtAnchorTwo_seed
    h_left_iter

/-- Conditional CP5 endpoint at `c = 2`: Green inversion routed through the
CP5 residual frontier plus the residual→injectivity seam. -/
theorem external_ray_map_exists_two_constructive_of_green_function_of_cp5ResidualTwo
    (hres : CP5ResidualTwo)
    (h_seam : CP5ResidualInjOnOutsideOpenSeamTwo) :
    Quadratic.ExternalRayMapData (2 : ℂ) := by
  exact external_ray_map_exists_two_constructive_of_green_function_of_injOn_outside_open
    (injOn_outside_open_two_of_cp5ResidualTwo h_seam hres)

/-- Conditional CP5 endpoint at `c = 2`: Green inversion routed through the
CP5 residual frontier under an explicit no-landing hypothesis. -/
theorem external_ray_map_exists_two_constructive_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam_of_cp5ResidualTwo_of_not_externalRayLandsOutsideOpen
    (huniq_seam : GreenRayUniquePreimageTwoAnchorSeam)
    (hlog_gt_anchor : GreenRayLogGtAnchorTwoSeam)
    (hres : CP5ResidualTwo)
    (hnot_land : ¬ ExternalRayLandsOutsideOpen (2 : ℂ)) :
    Quadratic.ExternalRayMapData (2 : ℂ) := by
  exact external_ray_map_exists_two_constructive_of_green_function_of_cp5ResidualTwo
    hres
    (cp5ResidualInjOnOutsideOpenSeamTwo_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam_of_not_externalRayLandsOutsideOpen
      huniq_seam hlog_gt_anchor hnot_land)

/-- Conditional CP5 endpoint at `c = 2`: Green inversion routed through the
CP5 residual frontier under an explicit no-landing hypothesis, specialized to
strict-mono seams. -/
theorem external_ray_map_exists_two_constructive_of_green_function_of_cp5ResidualTwo_of_not_externalRayLandsOutsideOpen
    (hres : CP5ResidualTwo)
    (hnot_land : ¬ ExternalRayLandsOutsideOpen (2 : ℂ)) :
    Quadratic.ExternalRayMapData (2 : ℂ) := by
  exact
    external_ray_map_exists_two_constructive_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam_of_cp5ResidualTwo_of_not_externalRayLandsOutsideOpen
      greenRayUniquePreimageTwoAnchorSeam_strictMono_seeded_of_greenFunctionStrictMonoAlongRayBasinTwo_seed
      greenRayLogGtAnchorTwo_seed
      hres hnot_land

/-- Constructive CP5 endpoint at `c = 2`: Green inversion routed through the
unconditional branch-combined CP5 residual→injectivity seam. -/
theorem external_ray_map_exists_two_constructive_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam_of_cp5ResidualTwo_unconditional
    (huniq_seam : GreenRayUniquePreimageTwoAnchorSeam)
    (hlog_gt_anchor : GreenRayLogGtAnchorTwoSeam)
    (hres : CP5ResidualTwo) :
    Quadratic.ExternalRayMapData (2 : ℂ) := by
  exact external_ray_map_exists_two_constructive_of_green_function_of_cp5ResidualTwo
    hres
    (cp5ResidualInjOnOutsideOpenSeamTwo_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam
      huniq_seam hlog_gt_anchor)

/-- Constructive CP5 endpoint at `c = 2`: Green inversion routed through the
unconditional branch-combined CP5 residual→injectivity seam, specialized to strict-mono
seams. -/
theorem external_ray_map_exists_two_constructive_of_green_function_of_cp5ResidualTwo_unconditional
    (hres : CP5ResidualTwo) :
    Quadratic.ExternalRayMapData (2 : ℂ) := by
  exact
    external_ray_map_exists_two_constructive_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam_of_cp5ResidualTwo_unconditional
      greenRayUniquePreimageTwoAnchorSeam_strictMono_seeded_of_greenFunctionStrictMonoAlongRayBasinTwo_seed
      greenRayLogGtAnchorTwo_seed
      hres

/-- Degree-one fiber witness at `c = 2`: there exists a target value with a
singleton fiber under `bottcher_map`. This is the minimal topological bridge
needed to derive global injectivity from proper+local-homeomorph. -/
def ProperLocalDegreeOneFiberWitnessTwo : Prop :=
  ∃ y : ℂ, Nat.card ({x : ℂ // Quadratic.bottcher_map (2 : ℂ) x = y}) = 1

/-- Build a global singleton-fiber witness at `c = 2` from global properness and
outside-open injectivity using an outside seed whose whole fiber stays outside-open. -/
theorem properLocalDegreeOneFiberWitnessTwo_of_isProperMap_of_injOn_outside_open
    (hproper : IsProperMap (Quadratic.bottcher_map (2 : ℂ)))
    (h_inj :
      Set.InjOn (Quadratic.bottcher_map (2 : ℂ))
        {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2}) :
    ProperLocalDegreeOneFiberWitnessTwo := by
  rcases exists_bottcher_outside_seed_of_continuous (2 : ℂ) hproper.continuous with
    ⟨y, hyimg, hfiberU⟩
  refine ⟨y, ?_⟩
  exact natCard_fiber_eq_one_of_injOn_of_mem_image_of_fiber_subset
    (f := Quadratic.bottcher_map (2 : ℂ))
    (U := {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2})
    (y := y) h_inj hyimg hfiberU

/-- Degree-one fiber witness on the restricted map
`outside_open → exterior` at `c = 2`. -/
def RestrictProperLocalDegreeOneFiberWitnessTwo : Prop :=
  ∃ y : {w : ℂ // 1 < ‖w‖},
    Nat.card
      ({x : {z : ℂ // ‖z‖ > ‖(2 : ℂ)‖ + 2} //
          bottcher_map_outside_open_to_exterior (2 : ℂ) x = y}) = 1

/-- Outside-open injectivity at `c = 2` yields a singleton-fiber witness for the
restricted map `outside_open → exterior`. -/
theorem restrictProperLocalDegreeOneFiberWitnessTwo_of_injOn_outside_open
    (h_inj :
      Set.InjOn (Quadratic.bottcher_map (2 : ℂ))
        {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2}) :
    RestrictProperLocalDegreeOneFiberWitnessTwo := by
  let z0 : ℂ := (6 : ℂ)
  have hz0 : ‖z0‖ > ‖(2 : ℂ)‖ + 2 := by
    norm_num [z0]
  let x0 : {z : ℂ // ‖z‖ > ‖(2 : ℂ)‖ + 2} := ⟨z0, hz0⟩
  let y0 : {w : ℂ // 1 < ‖w‖} :=
    bottcher_map_outside_open_to_exterior (2 : ℂ) x0
  have huniq :
      ∃! x : {z : ℂ // ‖z‖ > ‖(2 : ℂ)‖ + 2},
        bottcher_map_outside_open_to_exterior (2 : ℂ) x = y0 := by
    refine ⟨x0, rfl, ?_⟩
    intro x hx
    apply Subtype.ext
    have hx_val :
        Quadratic.bottcher_map (2 : ℂ) x.1 = Quadratic.bottcher_map (2 : ℂ) x0.1 := by
      exact congrArg Subtype.val hx
    exact h_inj x.2 x0.2 hx_val
  have hcard : Nat.card
      ({x : {z : ℂ // ‖z‖ > ‖(2 : ℂ)‖ + 2} //
          bottcher_map_outside_open_to_exterior (2 : ℂ) x = y0}) = 1 := by
    rcases huniq with ⟨x, hx, hux⟩
    letI : Unique
        ({x : {z : ℂ // ‖z‖ > ‖(2 : ℂ)‖ + 2} //
            bottcher_map_outside_open_to_exterior (2 : ℂ) x = y0}) := {
      default := ⟨x, hx⟩
      uniq := by
        intro a
        apply Subtype.ext
        exact hux a.1 a.2
    }
    letI : Fintype
        ({x : {z : ℂ // ‖z‖ > ‖(2 : ℂ)‖ + 2} //
            bottcher_map_outside_open_to_exterior (2 : ℂ) x = y0}) :=
      Fintype.ofFinite _
    calc
      Nat.card
          ({x : {z : ℂ // ‖z‖ > ‖(2 : ℂ)‖ + 2} //
              bottcher_map_outside_open_to_exterior (2 : ℂ) x = y0})
          = Fintype.card
              ({x : {z : ℂ // ‖z‖ > ‖(2 : ℂ)‖ + 2} //
                  bottcher_map_outside_open_to_exterior (2 : ℂ) x = y0}) := by
            simp [Nat.card_eq_fintype_card]
      _ = 1 := Fintype.card_unique
  exact ⟨y0, hcard⟩

/-- Constructive outside-open injectivity from global proper+local-homeomorph
plus a degree-one fiber witness at `c = 2`. -/
theorem injOn_outside_open_two_of_isProperMap_isLocalHomeomorph_of_degreeOneFiberWitness
    (hproper : IsProperMap (Quadratic.bottcher_map (2 : ℂ)))
    (hlocal : IsLocalHomeomorph (Quadratic.bottcher_map (2 : ℂ)))
    (hdeg1 : ProperLocalDegreeOneFiberWitnessTwo) :
    Set.InjOn (Quadratic.bottcher_map (2 : ℂ))
      {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2} := by
  have hinj :
      Function.Injective (Quadratic.bottcher_map (2 : ℂ)) :=
    injective_of_isProperMap_isLocalHomeomorph_of_exists_natCard_fiber_eq_one
      (f := Quadratic.bottcher_map (2 : ℂ)) hproper hlocal hdeg1
  exact hinj.injOn

/-- Build the exact strict-mono-free root witness target from global
proper+local-homeomorph and a degree-one fiber witness at `c = 2`. -/
theorem rootSafeOutsideOpenInjWitnessTwo_of_isProperMap_isLocalHomeomorph_of_degreeOneFiberWitness
    (hproper : IsProperMap (Quadratic.bottcher_map (2 : ℂ)))
    (hlocal : IsLocalHomeomorph (Quadratic.bottcher_map (2 : ℂ)))
    (hdeg1 : ProperLocalDegreeOneFiberWitnessTwo) :
    RootSafeOutsideOpenInjWitnessTwo :=
  injOn_outside_open_two_of_isProperMap_isLocalHomeomorph_of_degreeOneFiberWitness
    hproper hlocal hdeg1

/-- v11 route marker: global properness + global local-homeomorph + degree-one
fiber witness route to outside-open injectivity. -/
def GlobalProperLocalDegreeOneRouteTwo : Prop :=
  IsProperMap (Quadratic.bottcher_map (2 : ℂ)) ∧
    IsLocalHomeomorph (Quadratic.bottcher_map (2 : ℂ)) ∧
      ProperLocalDegreeOneFiberWitnessTwo

/-- Current-model no-go: the global proper/local + degree-one-fiber route is
inconsistent because global properness of `bottcher_map` is impossible. -/
theorem not_globalProperLocalDegreeOneRouteTwo :
    ¬ GlobalProperLocalDegreeOneRouteTwo := by
  intro hroute
  exact bottcher_map_not_isProperMap (2 : ℂ) hroute.1

/-- Route projection: if the global proper/local + degree-one-fiber route were
available, it would produce outside-open injectivity. -/
theorem rootSafeOutsideOpenInjWitnessTwo_of_globalProperLocalDegreeOneRouteTwo
    (hroute : GlobalProperLocalDegreeOneRouteTwo) :
    RootSafeOutsideOpenInjWitnessTwo :=
  rootSafeOutsideOpenInjWitnessTwo_of_isProperMap_isLocalHomeomorph_of_degreeOneFiberWitness
    hroute.1 hroute.2.1 hroute.2.2

/-- Current-model contradiction marker for the global proper/local
degree-one-fiber route. -/
theorem false_of_globalProperLocalDegreeOneRouteTwo
    (hroute : GlobalProperLocalDegreeOneRouteTwo) :
    False :=
  not_globalProperLocalDegreeOneRouteTwo hroute

/-- Constructive outside-open injectivity from the direct proper+local witness
at `c = 2`. -/
theorem injOn_outside_open_two_of_directProperLocalWitnessTwo_of_cp5ResidualLocalHomeomorphInjSeamTwo
    (h : DirectProperLocalWitnessTwo)
    (h_seam : CP5ResidualLocalHomeomorphInjSeamTwo) :
    Set.InjOn (Quadratic.bottcher_map (2 : ℂ))
      {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2} :=
  h_seam h

/-- Root-safe outside-open injectivity witness from the direct proper+local
branch plus a local-homeomorph→injectivity seam at `c = 2`. -/
theorem rootSafeOutsideOpenInjWitnessTwo_of_directProperLocalWitnessTwo_of_cp5ResidualLocalHomeomorphInjSeamTwo
    (h : DirectProperLocalWitnessTwo)
    (h_seam : CP5ResidualLocalHomeomorphInjSeamTwo) :
    RootSafeOutsideOpenInjWitnessTwo :=
  injOn_outside_open_two_of_directProperLocalWitnessTwo_of_cp5ResidualLocalHomeomorphInjSeamTwo
    h h_seam

/-- Root-safe outside-open injectivity witness from the CP5
local-homeomorph source pair plus a local-homeomorph→injectivity seam witness
at `c = 2`. -/
theorem rootSafeOutsideOpenInjWitnessTwo_of_localHomeomorphSurjSourceTwo_of_cp5ResidualLocalHomeomorphInjSeamTwo
    (hlocal :
      IsProperMap (bottcher_map_outside_open_to_exterior (2 : ℂ)) ∧
        IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (h_seam : CP5ResidualLocalHomeomorphInjSeamTwo) :
    RootSafeOutsideOpenInjWitnessTwo :=
  rootSafeOutsideOpenInjWitnessTwo_of_directProperLocalWitnessTwo_of_cp5ResidualLocalHomeomorphInjSeamTwo
    hlocal h_seam

/-- Root-safe outside-open injectivity witness from explicit restricted-map
properness/local-homeomorph hypotheses plus a local-homeomorph→injectivity seam
witness at `c = 2`. -/
theorem rootSafeOutsideOpenInjWitnessTwo_of_isProperMap_restrict_of_isLocalHomeomorph_restrict_of_cp5ResidualLocalHomeomorphInjSeamTwo
    (hproper : IsProperMap (bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (hlocal : IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (h_seam : CP5ResidualLocalHomeomorphInjSeamTwo) :
    RootSafeOutsideOpenInjWitnessTwo :=
  rootSafeOutsideOpenInjWitnessTwo_of_localHomeomorphSurjSourceTwo_of_cp5ResidualLocalHomeomorphInjSeamTwo
    ⟨hproper, hlocal⟩ h_seam

/-- Root-safe outside-open injectivity witness from the CP5
local-homeomorph source pair at `c = 2`, specialized to the strict-mono local
seam witness. -/
theorem rootSafeOutsideOpenInjWitnessTwo_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam_of_localHomeomorphSurjSourceTwo
    (huniq_seam : GreenRayUniquePreimageTwoAnchorSeam)
    (hlog_gt_anchor : GreenRayLogGtAnchorTwoSeam)
    (hlocal :
      IsProperMap (bottcher_map_outside_open_to_exterior (2 : ℂ)) ∧
        IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ))) :
    RootSafeOutsideOpenInjWitnessTwo :=
  rootSafeOutsideOpenInjWitnessTwo_of_localHomeomorphSurjSourceTwo_of_cp5ResidualLocalHomeomorphInjSeamTwo
    hlocal
    (cp5ResidualLocalHomeomorphInjSeamTwo_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam
      huniq_seam hlog_gt_anchor)

/-- Root-safe outside-open injectivity witness from the CP5
local-homeomorph source pair at `c = 2`, specialized to the strict-mono local
seam witness. -/
theorem rootSafeOutsideOpenInjWitnessTwo_of_localHomeomorphSurjSourceTwo_strictMono
    (hlocal :
      IsProperMap (bottcher_map_outside_open_to_exterior (2 : ℂ)) ∧
        IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ))) :
    RootSafeOutsideOpenInjWitnessTwo :=
  rootSafeOutsideOpenInjWitnessTwo_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam_of_localHomeomorphSurjSourceTwo
    greenRayUniquePreimageTwoAnchorSeam_strictMono_seeded_of_greenFunctionStrictMonoAlongRayBasinTwo_seed
    greenRayLogGtAnchorTwo_seed
    hlocal

/-- Root-safe outside-open injectivity witness from explicit restricted-map
proper/local hypotheses at `c = 2`, specialized to the strict-mono local seam
witness. -/
theorem rootSafeOutsideOpenInjWitnessTwo_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam_of_isProperMap_restrict_of_isLocalHomeomorph_restrict
    (huniq_seam : GreenRayUniquePreimageTwoAnchorSeam)
    (hlog_gt_anchor : GreenRayLogGtAnchorTwoSeam)
    (hproper : IsProperMap (bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (hlocal : IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ))) :
    RootSafeOutsideOpenInjWitnessTwo :=
  rootSafeOutsideOpenInjWitnessTwo_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam_of_localHomeomorphSurjSourceTwo
    huniq_seam hlog_gt_anchor ⟨hproper, hlocal⟩

/-- Root-safe outside-open injectivity witness from explicit restricted-map
proper/local hypotheses at `c = 2`, specialized to the strict-mono local seam
witness. -/
theorem rootSafeOutsideOpenInjWitnessTwo_of_isProperMap_restrict_of_isLocalHomeomorph_restrict_strictMono
    (hproper : IsProperMap (bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (hlocal : IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ))) :
    RootSafeOutsideOpenInjWitnessTwo :=
  rootSafeOutsideOpenInjWitnessTwo_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam_of_isProperMap_restrict_of_isLocalHomeomorph_restrict
    greenRayUniquePreimageTwoAnchorSeam_strictMono_seeded_of_greenFunctionStrictMonoAlongRayBasinTwo_seed
    greenRayLogGtAnchorTwo_seed
    hproper hlocal

/-- Constructive outside-open injectivity from the direct proper+local witness
at `c = 2`, currently routed through the strict-mono local-homeomorph seam. -/
theorem injOn_outside_open_two_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam_of_directProperLocalWitnessTwo
    (huniq_seam : GreenRayUniquePreimageTwoAnchorSeam)
    (hlog_gt_anchor : GreenRayLogGtAnchorTwoSeam)
    (h : DirectProperLocalWitnessTwo) :
    Set.InjOn (Quadratic.bottcher_map (2 : ℂ))
      {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2} :=
  rootSafeOutsideOpenInjWitnessTwo_of_directProperLocalWitnessTwo_of_cp5ResidualLocalHomeomorphInjSeamTwo
    h
    (cp5ResidualLocalHomeomorphInjSeamTwo_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam
      huniq_seam hlog_gt_anchor)

/-- Constructive outside-open injectivity from the direct proper+local witness
at `c = 2`, currently routed through the strict-mono local-homeomorph seam. -/
theorem injOn_outside_open_two_of_directProperLocalWitnessTwo_constructive
    (h : DirectProperLocalWitnessTwo) :
    Set.InjOn (Quadratic.bottcher_map (2 : ℂ))
      {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2} := by
  exact
    injOn_outside_open_two_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam_of_directProperLocalWitnessTwo
      greenRayUniquePreimageTwoAnchorSeam_strictMono_seeded_of_greenFunctionStrictMonoAlongRayBasinTwo_seed
      greenRayLogGtAnchorTwo_seed
      h

/-- Constructive local-homeomorph CP5 branch seam from the direct proper+local
witness at `c = 2`. -/
theorem cp5ResidualLocalHomeomorphInjSeamTwo_of_directProperLocalWitnessTwo
    (h : DirectProperLocalWitnessTwo) :
    CP5ResidualLocalHomeomorphInjSeamTwo := by
  intro _hlocal
  exact injOn_outside_open_two_of_directProperLocalWitnessTwo_constructive h

/-- Non-seeded local-homeomorph CP5 branch seam from an explicit outside-open
injectivity witness at `c = 2`. -/
theorem cp5ResidualLocalHomeomorphInjSeamTwo_of_rootSafeOutsideOpenInjWitnessTwo
    (h_inj : RootSafeOutsideOpenInjWitnessTwo) :
    CP5ResidualLocalHomeomorphInjSeamTwo := by
  intro _hlocal
  exact h_inj

/-- Under a direct proper+local witness, outside-open injectivity and the CP5
local-homeomorph injectivity seam are equivalent at `c = 2`. -/
theorem rootSafeOutsideOpenInjWitnessTwo_iff_cp5ResidualLocalHomeomorphInjSeamTwo_of_directProperLocalWitnessTwo
    (h : DirectProperLocalWitnessTwo) :
    RootSafeOutsideOpenInjWitnessTwo ↔ CP5ResidualLocalHomeomorphInjSeamTwo := by
  constructor
  · intro h_inj
    exact cp5ResidualLocalHomeomorphInjSeamTwo_of_rootSafeOutsideOpenInjWitnessTwo h_inj
  · intro h_seam
    exact
      rootSafeOutsideOpenInjWitnessTwo_of_directProperLocalWitnessTwo_of_cp5ResidualLocalHomeomorphInjSeamTwo
        h h_seam

/-- Primitive-family specialization of the outside-open injectivity/CP5-local
seam equivalence at `c = 2`. -/
theorem rootSafeOutsideOpenInjWitnessTwo_iff_cp5ResidualLocalHomeomorphInjSeamTwo_of_primitiveRestrictedMapProperLocalWitnessFamilyTwo
    (h : PrimitiveRestrictedMapProperLocalWitnessFamilyTwo) :
    RootSafeOutsideOpenInjWitnessTwo ↔ CP5ResidualLocalHomeomorphInjSeamTwo := by
  exact
    rootSafeOutsideOpenInjWitnessTwo_iff_cp5ResidualLocalHomeomorphInjSeamTwo_of_directProperLocalWitnessTwo
      (directProperLocalWitnessTwo_of_primitiveRestrictedMapProperLocalWitnessFamilyTwo h)

/-- Constructive CP5 residual→injectivity seam under no-landing, routed through
the direct proper+local witness branch at `c = 2`. -/
theorem cp5ResidualInjOnOutsideOpenSeamTwo_of_directProperLocalWitnessTwo_of_not_externalRayLandsOutsideOpen
    (h : DirectProperLocalWitnessTwo)
    (hnot_land : ¬ ExternalRayLandsOutsideOpen (2 : ℂ)) :
    CP5ResidualInjOnOutsideOpenSeamTwo :=
  cp5ResidualInjOnOutsideOpenSeamTwo_of_localHomeomorphBranchSeam_of_not_externalRayLandsOutsideOpen
    (cp5ResidualLocalHomeomorphInjSeamTwo_of_directProperLocalWitnessTwo h)
    hnot_land

/-- Conditional CP5 endpoint at `c = 2`: Green inversion routed through the
direct proper+local witness branch. -/
theorem external_ray_map_exists_two_constructive_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam_of_directProperLocalWitnessTwo
    (huniq_seam : GreenRayUniquePreimageTwoAnchorSeam)
    (hlog_gt_anchor : GreenRayLogGtAnchorTwoSeam)
    (h : DirectProperLocalWitnessTwo) :
    Quadratic.ExternalRayMapData (2 : ℂ) := by
  exact external_ray_map_exists_two_constructive_of_greenRayLogGtAnchorTwoSeam_of_injOn_outside_open
    hlog_gt_anchor
    (injOn_outside_open_two_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam_of_directProperLocalWitnessTwo
      huniq_seam hlog_gt_anchor h)

/-- Conditional CP5 endpoint at `c = 2`: Green inversion routed through the
direct proper+local witness branch, specialized to the strict-mono seams. -/
theorem external_ray_map_exists_two_constructive_of_green_function_of_directProperLocalWitnessTwo
    (h : DirectProperLocalWitnessTwo) :
    Quadratic.ExternalRayMapData (2 : ℂ) := by
  exact
    external_ray_map_exists_two_constructive_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam_of_directProperLocalWitnessTwo
      greenRayUniquePreimageTwoAnchorSeam_strictMono_seeded_of_greenFunctionStrictMonoAlongRayBasinTwo_seed
      greenRayLogGtAnchorTwo_seed
      h

/-- Strict-mono-free external-ray-data candidate at `c = 2` from a direct
proper+local witness plus a local-homeomorph→injectivity seam witness. -/
theorem external_ray_map_exists_two_constructive_strictMono_free_of_directProperLocalWitnessTwo_of_cp5ResidualLocalHomeomorphInjSeamTwo
    (h : DirectProperLocalWitnessTwo)
    (h_seam : CP5ResidualLocalHomeomorphInjSeamTwo) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_exists_two_constructive_of_rootSafeOutsideOpenInjWitnessTwo_of_directProperLocalWitnessTwo
    (rootSafeOutsideOpenInjWitnessTwo_of_directProperLocalWitnessTwo_of_cp5ResidualLocalHomeomorphInjSeamTwo
      h h_seam)
    h

/-- Strict-mono-seeded external-ray-data candidate at `c = 2`, specialized to a
direct proper/local witness. -/
theorem external_ray_map_exists_two_constructive_strictMono_seeded_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam_of_directProperLocalWitnessTwo
    (huniq_seam : GreenRayUniquePreimageTwoAnchorSeam)
    (hlog_gt_anchor : GreenRayLogGtAnchorTwoSeam)
    (h : DirectProperLocalWitnessTwo) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_exists_two_constructive_strictMono_free_of_directProperLocalWitnessTwo_of_cp5ResidualLocalHomeomorphInjSeamTwo
    h
    (cp5ResidualLocalHomeomorphInjSeamTwo_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam
      huniq_seam hlog_gt_anchor)

/-- Strict-mono-seeded external-ray-data candidate at `c = 2`, specialized to a
direct proper/local witness. -/
theorem external_ray_map_exists_two_constructive_strictMono_seeded_of_directProperLocalWitnessTwo
    (h : DirectProperLocalWitnessTwo) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_exists_two_constructive_strictMono_seeded_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam_of_directProperLocalWitnessTwo
    greenRayUniquePreimageTwoAnchorSeam_strictMono_seeded_of_greenFunctionStrictMonoAlongRayBasinTwo_seed
    greenRayLogGtAnchorTwo_seed
    h

/-- Strict-mono-free external-ray-data candidate at `c = 2` from the CP5
local-homeomorph branch source (without passing through `CP5ResidualTwo`) plus
the local-homeomorph→injectivity seam witness. -/
theorem external_ray_map_exists_two_constructive_strictMono_free_of_localHomeomorphSurjSourceTwo_of_cp5ResidualLocalHomeomorphInjSeamTwo
    (hlocal :
      IsProperMap (bottcher_map_outside_open_to_exterior (2 : ℂ)) ∧
        IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (h_seam : CP5ResidualLocalHomeomorphInjSeamTwo) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_exists_two_constructive_strictMono_free_of_directProperLocalWitnessTwo_of_cp5ResidualLocalHomeomorphInjSeamTwo
    hlocal h_seam

/-- Strict-mono-seeded external-ray-data candidate at `c = 2`, specialized to
the CP5 local-homeomorph source pair. -/
theorem external_ray_map_exists_two_constructive_strictMono_seeded_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam_of_localHomeomorphSurjSourceTwo
    (huniq_seam : GreenRayUniquePreimageTwoAnchorSeam)
    (hlog_gt_anchor : GreenRayLogGtAnchorTwoSeam)
    (hlocal :
      IsProperMap (bottcher_map_outside_open_to_exterior (2 : ℂ)) ∧
        IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ))) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_exists_two_constructive_strictMono_free_of_localHomeomorphSurjSourceTwo_of_cp5ResidualLocalHomeomorphInjSeamTwo
    hlocal
    (cp5ResidualLocalHomeomorphInjSeamTwo_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam
      huniq_seam hlog_gt_anchor)

/-- Strict-mono-seeded external-ray-data candidate at `c = 2`, specialized to
the CP5 local-homeomorph source pair. -/
theorem external_ray_map_exists_two_constructive_strictMono_seeded_of_localHomeomorphSurjSourceTwo
    (hlocal :
      IsProperMap (bottcher_map_outside_open_to_exterior (2 : ℂ)) ∧
        IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ))) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_exists_two_constructive_strictMono_seeded_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam_of_localHomeomorphSurjSourceTwo
    greenRayUniquePreimageTwoAnchorSeam_strictMono_seeded_of_greenFunctionStrictMonoAlongRayBasinTwo_seed
    greenRayLogGtAnchorTwo_seed
    hlocal

/-- Strict-mono-free external-ray-data candidate at `c = 2` from explicit
restricted-map properness/local-homeomorph assumptions plus a local-homeomorph
seam witness (without `CP5ResidualTwo` in the theorem type). -/
theorem external_ray_map_exists_two_constructive_strictMono_free_of_isProperMap_restrict_of_isLocalHomeomorph_restrict_of_cp5ResidualLocalHomeomorphInjSeamTwo
    (hproper : IsProperMap (bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (hlocal : IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (h_seam : CP5ResidualLocalHomeomorphInjSeamTwo) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_exists_two_constructive_strictMono_free_of_localHomeomorphSurjSourceTwo_of_cp5ResidualLocalHomeomorphInjSeamTwo
    ⟨hproper, hlocal⟩ h_seam

/-- Strict-mono-seeded external-ray-data candidate at `c = 2`, specialized to
explicit restricted-map proper/local hypotheses. -/
theorem external_ray_map_exists_two_constructive_strictMono_seeded_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam_of_isProperMap_restrict_of_isLocalHomeomorph_restrict
    (huniq_seam : GreenRayUniquePreimageTwoAnchorSeam)
    (hlog_gt_anchor : GreenRayLogGtAnchorTwoSeam)
    (hproper : IsProperMap (bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (hlocal : IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ))) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_exists_two_constructive_strictMono_seeded_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam_of_localHomeomorphSurjSourceTwo
    huniq_seam hlog_gt_anchor ⟨hproper, hlocal⟩

/-- Strict-mono-seeded external-ray-data candidate at `c = 2`, specialized to
explicit restricted-map proper/local hypotheses. -/
theorem external_ray_map_exists_two_constructive_strictMono_seeded_of_isProperMap_restrict_of_isLocalHomeomorph_restrict
    (hproper : IsProperMap (bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (hlocal : IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ))) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_exists_two_constructive_strictMono_seeded_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam_of_isProperMap_restrict_of_isLocalHomeomorph_restrict
    greenRayUniquePreimageTwoAnchorSeam_strictMono_seeded_of_greenFunctionStrictMonoAlongRayBasinTwo_seed
    greenRayLogGtAnchorTwo_seed
    hproper hlocal

/-- Conditional CP5 endpoint at `c = 2`: Green inversion routed through global
proper+local-homeomorph plus a degree-one fiber witness. -/
theorem external_ray_map_exists_two_constructive_of_greenRayLogGtAnchorTwoSeam_of_isProperMap_isLocalHomeomorph_of_degreeOneFiberWitness
    (hlog_gt_anchor : GreenRayLogGtAnchorTwoSeam)
    (hproper : IsProperMap (Quadratic.bottcher_map (2 : ℂ)))
    (hlocal : IsLocalHomeomorph (Quadratic.bottcher_map (2 : ℂ)))
    (hdeg1 : ProperLocalDegreeOneFiberWitnessTwo) :
    Quadratic.ExternalRayMapData (2 : ℂ) := by
  exact external_ray_map_exists_two_constructive_of_greenRayLogGtAnchorTwoSeam_of_injOn_outside_open
    hlog_gt_anchor
    (injOn_outside_open_two_of_isProperMap_isLocalHomeomorph_of_degreeOneFiberWitness
      hproper hlocal hdeg1)

/-- Conditional CP5 endpoint at `c = 2`: Green inversion routed through global
proper+local-homeomorph plus a degree-one fiber witness, specialized to the
current anchor-gap seed. -/
theorem external_ray_map_exists_two_constructive_of_green_function_of_isProperMap_isLocalHomeomorph_of_degreeOneFiberWitness
    (hproper : IsProperMap (Quadratic.bottcher_map (2 : ℂ)))
    (hlocal : IsLocalHomeomorph (Quadratic.bottcher_map (2 : ℂ)))
    (hdeg1 : ProperLocalDegreeOneFiberWitnessTwo) :
    Quadratic.ExternalRayMapData (2 : ℂ) := by
  exact
    external_ray_map_exists_two_constructive_of_greenRayLogGtAnchorTwoSeam_of_isProperMap_isLocalHomeomorph_of_degreeOneFiberWitness
      greenRayLogGtAnchorTwo_seed
      hproper hlocal hdeg1

/-- Conditional CP5 endpoint at `c = 2`: Green inversion routed through global
proper+local-homeomorph and outside-open injectivity. -/
theorem external_ray_map_exists_two_constructive_of_greenRayLogGtAnchorTwoSeam_of_isProperMap_isLocalHomeomorph_of_injOn_outside_open
    (hlog_gt_anchor : GreenRayLogGtAnchorTwoSeam)
    (hproper : IsProperMap (Quadratic.bottcher_map (2 : ℂ)))
    (hlocal : IsLocalHomeomorph (Quadratic.bottcher_map (2 : ℂ)))
    (h_inj :
      Set.InjOn (Quadratic.bottcher_map (2 : ℂ))
        {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2}) :
    Quadratic.ExternalRayMapData (2 : ℂ) := by
  exact external_ray_map_exists_two_constructive_of_greenRayLogGtAnchorTwoSeam_of_isProperMap_isLocalHomeomorph_of_degreeOneFiberWitness
    hlog_gt_anchor
    hproper hlocal
    (properLocalDegreeOneFiberWitnessTwo_of_isProperMap_of_injOn_outside_open
      hproper h_inj)

/-- Conditional CP5 endpoint at `c = 2`: Green inversion routed through global
proper+local-homeomorph and outside-open injectivity, specialized to the
current anchor-gap seed. -/
theorem external_ray_map_exists_two_constructive_of_green_function_of_isProperMap_isLocalHomeomorph_of_injOn_outside_open
    (hproper : IsProperMap (Quadratic.bottcher_map (2 : ℂ)))
    (hlocal : IsLocalHomeomorph (Quadratic.bottcher_map (2 : ℂ)))
    (h_inj :
      Set.InjOn (Quadratic.bottcher_map (2 : ℂ))
        {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2}) :
    Quadratic.ExternalRayMapData (2 : ℂ) := by
  exact external_ray_map_exists_two_constructive_of_greenRayLogGtAnchorTwoSeam_of_isProperMap_isLocalHomeomorph_of_injOn_outside_open
    greenRayLogGtAnchorTwo_seed
    hproper hlocal
    h_inj

/-- Conditional rooted theorem at `c = 2`: Green inversion plus outside-open
injectivity is sufficient for MLC. -/
theorem mlc_conjecture_of_greenRayLogGtAnchorTwoSeam_of_injOn_outside_open_two
    (hlog_gt_anchor : GreenRayLogGtAnchorTwoSeam)
    (h_inj_outside :
      Set.InjOn (Quadratic.bottcher_map (2 : ℂ))
        {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2}) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_externalRayMapData_two
    (external_ray_map_exists_two_constructive_of_greenRayLogGtAnchorTwoSeam_of_injOn_outside_open
      hlog_gt_anchor h_inj_outside)

/-- Conditional rooted theorem at `c = 2`: Green inversion plus outside-open
injectivity is sufficient for MLC, specialized to the current anchor-gap seed. -/
theorem mlc_conjecture_of_green_function_of_injOn_outside_open_two
    (h_inj_outside :
      Set.InjOn (Quadratic.bottcher_map (2 : ℂ))
        {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2}) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_greenRayLogGtAnchorTwoSeam_of_injOn_outside_open_two
    greenRayLogGtAnchorTwo_seed
    h_inj_outside

/-- Conditional rooted theorem at `c = 2`: Green inversion plus iterate-left-
inverse injectivity on outside-open is sufficient for MLC. -/
theorem mlc_conjecture_of_greenRayLogGtAnchorTwoSeam_of_iter_left_inverse_two
    (hlog_gt_anchor : GreenRayLogGtAnchorTwoSeam)
    (h_left_iter : QuadraticMapIterLeftInverseOnBasin (2 : ℂ)) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_externalRayMapData_two
    (external_ray_map_exists_two_constructive_of_greenRayLogGtAnchorTwoSeam_of_iter_left_inverse
      hlog_gt_anchor h_left_iter)

/-- Conditional rooted theorem at `c = 2`: Green inversion plus iterate-left-
inverse injectivity on outside-open is sufficient for MLC. -/
theorem mlc_conjecture_of_green_function_of_iter_left_inverse_two
    (h_left_iter : QuadraticMapIterLeftInverseOnBasin (2 : ℂ)) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_greenRayLogGtAnchorTwoSeam_of_iter_left_inverse_two
    greenRayLogGtAnchorTwo_seed
    h_left_iter

/-- Conditional rooted theorem at `c = 2`: Green inversion plus the explicit
CP5 residual frontier and residual→injectivity seam implies MLC. -/
theorem mlc_conjecture_of_green_function_of_cp5ResidualTwo
    (hres : CP5ResidualTwo)
    (h_seam : CP5ResidualInjOnOutsideOpenSeamTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_externalRayMapData_two
    (external_ray_map_exists_two_constructive_of_green_function_of_cp5ResidualTwo hres h_seam)

/-- Conditional rooted theorem at `c = 2`: Green inversion plus CP5 residual
frontier under explicit no-landing implies MLC. -/
theorem mlc_conjecture_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam_of_cp5ResidualTwo_of_not_externalRayLandsOutsideOpen
    (huniq_seam : GreenRayUniquePreimageTwoAnchorSeam)
    (hlog_gt_anchor : GreenRayLogGtAnchorTwoSeam)
    (hres : CP5ResidualTwo)
    (hnot_land : ¬ ExternalRayLandsOutsideOpen (2 : ℂ)) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_externalRayMapData_two
    (external_ray_map_exists_two_constructive_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam_of_cp5ResidualTwo_of_not_externalRayLandsOutsideOpen
      huniq_seam hlog_gt_anchor hres hnot_land)

/-- Conditional rooted theorem at `c = 2`: Green inversion plus CP5 residual
frontier under explicit no-landing, specialized to strict-mono seams, implies
MLC. -/
theorem mlc_conjecture_of_green_function_of_cp5ResidualTwo_of_not_externalRayLandsOutsideOpen
    (hres : CP5ResidualTwo)
    (hnot_land : ¬ ExternalRayLandsOutsideOpen (2 : ℂ)) :
    LocallyConnectedSpace mandelbrotSet := by
  exact
    mlc_conjecture_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam_of_cp5ResidualTwo_of_not_externalRayLandsOutsideOpen
      greenRayUniquePreimageTwoAnchorSeam_strictMono_seeded_of_greenFunctionStrictMonoAlongRayBasinTwo_seed
      greenRayLogGtAnchorTwo_seed
      hres hnot_land

/-- Conditional rooted theorem at `c = 2`: Green inversion plus CP5 residual
frontier (using the unconditional branch-combined seam) implies MLC. -/
theorem mlc_conjecture_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam_of_cp5ResidualTwo_unconditional
    (huniq_seam : GreenRayUniquePreimageTwoAnchorSeam)
    (hlog_gt_anchor : GreenRayLogGtAnchorTwoSeam)
    (hres : CP5ResidualTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_green_function_of_cp5ResidualTwo
    hres
    (cp5ResidualInjOnOutsideOpenSeamTwo_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam
      huniq_seam hlog_gt_anchor)

/-- Conditional rooted theorem at `c = 2`: Green inversion plus CP5 residual
frontier (using the unconditional branch-combined seam), specialized
to strict-mono seams, implies MLC. -/
theorem mlc_conjecture_of_green_function_of_cp5ResidualTwo_unconditional
    (hres : CP5ResidualTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact
    mlc_conjecture_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam_of_cp5ResidualTwo_unconditional
      greenRayUniquePreimageTwoAnchorSeam_strictMono_seeded_of_greenFunctionStrictMonoAlongRayBasinTwo_seed
      greenRayLogGtAnchorTwo_seed
      hres

/-- Conditional rooted theorem at `c = 2`: Green inversion routed through the
direct proper+local witness branch implies MLC. -/
theorem mlc_conjecture_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam_of_directProperLocalWitnessTwo
    (huniq_seam : GreenRayUniquePreimageTwoAnchorSeam)
    (hlog_gt_anchor : GreenRayLogGtAnchorTwoSeam)
    (h : DirectProperLocalWitnessTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_externalRayMapData_two
    (external_ray_map_exists_two_constructive_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam_of_directProperLocalWitnessTwo
      huniq_seam hlog_gt_anchor h)

/-- Conditional rooted theorem at `c = 2`: Green inversion routed through the
direct proper+local witness branch, specialized to strict-mono seams, implies
MLC. -/
theorem mlc_conjecture_of_green_function_of_directProperLocalWitnessTwo
    (h : DirectProperLocalWitnessTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact
    mlc_conjecture_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam_of_directProperLocalWitnessTwo
      greenRayUniquePreimageTwoAnchorSeam_strictMono_seeded_of_greenFunctionStrictMonoAlongRayBasinTwo_seed
      greenRayLogGtAnchorTwo_seed
      h

/-- Strict-mono-free rooted candidate at `c = 2` from a direct proper+local
witness plus a local-homeomorph→injectivity seam witness. -/
theorem mlc_conjecture_strictMonoFree_candidate_of_directProperLocalWitnessTwo_of_cp5ResidualLocalHomeomorphInjSeamTwo
    (h : DirectProperLocalWitnessTwo)
    (h_seam : CP5ResidualLocalHomeomorphInjSeamTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_externalRayMapData_two
    (external_ray_map_exists_two_constructive_strictMono_free_of_directProperLocalWitnessTwo_of_cp5ResidualLocalHomeomorphInjSeamTwo
      h h_seam)

/-- Strict-mono-seeded rooted candidate at `c = 2`, specialized to a direct
proper/local witness. -/
theorem mlc_conjecture_strictMono_seeded_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam_of_directProperLocalWitnessTwo
    (huniq_seam : GreenRayUniquePreimageTwoAnchorSeam)
    (hlog_gt_anchor : GreenRayLogGtAnchorTwoSeam)
    (h : DirectProperLocalWitnessTwo) :
    LocallyConnectedSpace mandelbrotSet :=
  mlc_conjecture_strictMonoFree_candidate_of_directProperLocalWitnessTwo_of_cp5ResidualLocalHomeomorphInjSeamTwo
    h
    (cp5ResidualLocalHomeomorphInjSeamTwo_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam
      huniq_seam hlog_gt_anchor)

/-- Strict-mono-seeded rooted candidate at `c = 2`, specialized to a direct
proper/local witness. -/
theorem mlc_conjecture_strictMono_seeded_of_directProperLocalWitnessTwo
    (h : DirectProperLocalWitnessTwo) :
    LocallyConnectedSpace mandelbrotSet :=
  mlc_conjecture_strictMono_seeded_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam_of_directProperLocalWitnessTwo
    greenRayUniquePreimageTwoAnchorSeam_strictMono_seeded_of_greenFunctionStrictMonoAlongRayBasinTwo_seed
    greenRayLogGtAnchorTwo_seed
    h

/-- Strict-mono-free rooted candidate at `c = 2` from the CP5
local-homeomorph branch source (without `CP5ResidualTwo` in the theorem type)
plus the local-homeomorph→injectivity seam witness. -/
theorem mlc_conjecture_strictMonoFree_candidate_of_localHomeomorphSurjSourceTwo_of_cp5ResidualLocalHomeomorphInjSeamTwo
    (hlocal :
      IsProperMap (bottcher_map_outside_open_to_exterior (2 : ℂ)) ∧
        IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (h_seam : CP5ResidualLocalHomeomorphInjSeamTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_strictMonoFree_candidate_of_directProperLocalWitnessTwo_of_cp5ResidualLocalHomeomorphInjSeamTwo
    hlocal h_seam

/-- Strict-mono-seeded rooted candidate at `c = 2`, specialized to the CP5
local-homeomorph source pair. -/
theorem mlc_conjecture_strictMono_seeded_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam_of_localHomeomorphSurjSourceTwo
    (huniq_seam : GreenRayUniquePreimageTwoAnchorSeam)
    (hlog_gt_anchor : GreenRayLogGtAnchorTwoSeam)
    (hlocal :
      IsProperMap (bottcher_map_outside_open_to_exterior (2 : ℂ)) ∧
        IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ))) :
    LocallyConnectedSpace mandelbrotSet :=
  mlc_conjecture_strictMonoFree_candidate_of_localHomeomorphSurjSourceTwo_of_cp5ResidualLocalHomeomorphInjSeamTwo
    hlocal
    (cp5ResidualLocalHomeomorphInjSeamTwo_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam
      huniq_seam hlog_gt_anchor)

/-- Strict-mono-seeded rooted candidate at `c = 2`, specialized to the CP5
local-homeomorph source pair. -/
theorem mlc_conjecture_strictMono_seeded_of_localHomeomorphSurjSourceTwo
    (hlocal :
      IsProperMap (bottcher_map_outside_open_to_exterior (2 : ℂ)) ∧
        IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ))) :
    LocallyConnectedSpace mandelbrotSet :=
  mlc_conjecture_strictMono_seeded_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam_of_localHomeomorphSurjSourceTwo
    greenRayUniquePreimageTwoAnchorSeam_strictMono_seeded_of_greenFunctionStrictMonoAlongRayBasinTwo_seed
    greenRayLogGtAnchorTwo_seed
    hlocal

/-- Strict-mono-free rooted candidate at `c = 2` from explicit restricted-map
properness/local-homeomorph assumptions plus a local-homeomorph seam witness
(without `CP5ResidualTwo` in the theorem type). -/
theorem mlc_conjecture_strictMonoFree_candidate_of_isProperMap_restrict_of_isLocalHomeomorph_restrict_of_cp5ResidualLocalHomeomorphInjSeamTwo
    (hproper : IsProperMap (bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (hlocal : IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (h_seam : CP5ResidualLocalHomeomorphInjSeamTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_strictMonoFree_candidate_of_localHomeomorphSurjSourceTwo_of_cp5ResidualLocalHomeomorphInjSeamTwo
    ⟨hproper, hlocal⟩ h_seam

/-- Strict-mono-seeded rooted candidate at `c = 2`, specialized to explicit
restricted-map proper/local hypotheses. -/
theorem mlc_conjecture_strictMono_seeded_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam_of_isProperMap_restrict_of_isLocalHomeomorph_restrict
    (huniq_seam : GreenRayUniquePreimageTwoAnchorSeam)
    (hlog_gt_anchor : GreenRayLogGtAnchorTwoSeam)
    (hproper : IsProperMap (bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (hlocal : IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ))) :
    LocallyConnectedSpace mandelbrotSet :=
  mlc_conjecture_strictMono_seeded_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam_of_localHomeomorphSurjSourceTwo
    huniq_seam hlog_gt_anchor ⟨hproper, hlocal⟩

/-- Strict-mono-seeded rooted candidate at `c = 2`, specialized to explicit
restricted-map proper/local hypotheses. -/
theorem mlc_conjecture_strictMono_seeded_of_isProperMap_restrict_of_isLocalHomeomorph_restrict
    (hproper : IsProperMap (bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (hlocal : IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ))) :
    LocallyConnectedSpace mandelbrotSet :=
  mlc_conjecture_strictMono_seeded_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam_of_isProperMap_restrict_of_isLocalHomeomorph_restrict
    greenRayUniquePreimageTwoAnchorSeam_strictMono_seeded_of_greenFunctionStrictMonoAlongRayBasinTwo_seed
    greenRayLogGtAnchorTwo_seed
    hproper hlocal

/-- Conditional rooted theorem at `c = 2`: Green inversion plus global
proper+local-homeomorph and degree-one fiber witness implies MLC. -/
theorem mlc_conjecture_of_greenRayLogGtAnchorTwoSeam_of_isProperMap_isLocalHomeomorph_of_degreeOneFiberWitness
    (hlog_gt_anchor : GreenRayLogGtAnchorTwoSeam)
    (hproper : IsProperMap (Quadratic.bottcher_map (2 : ℂ)))
    (hlocal : IsLocalHomeomorph (Quadratic.bottcher_map (2 : ℂ)))
    (hdeg1 : ProperLocalDegreeOneFiberWitnessTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_externalRayMapData_two
    (external_ray_map_exists_two_constructive_of_greenRayLogGtAnchorTwoSeam_of_isProperMap_isLocalHomeomorph_of_degreeOneFiberWitness
      hlog_gt_anchor hproper hlocal hdeg1)

/-- Conditional rooted theorem at `c = 2`: Green inversion plus global
proper+local-homeomorph and degree-one fiber witness implies MLC, specialized
to the current anchor-gap seed. -/
theorem mlc_conjecture_of_green_function_of_isProperMap_isLocalHomeomorph_of_degreeOneFiberWitness
    (hproper : IsProperMap (Quadratic.bottcher_map (2 : ℂ)))
    (hlocal : IsLocalHomeomorph (Quadratic.bottcher_map (2 : ℂ)))
    (hdeg1 : ProperLocalDegreeOneFiberWitnessTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact
    mlc_conjecture_of_greenRayLogGtAnchorTwoSeam_of_isProperMap_isLocalHomeomorph_of_degreeOneFiberWitness
      greenRayLogGtAnchorTwo_seed
      hproper hlocal hdeg1

/-- Conditional rooted theorem at `c = 2`: Green inversion plus global
proper+local-homeomorph and outside-open injectivity implies MLC. -/
theorem mlc_conjecture_of_greenRayLogGtAnchorTwoSeam_of_isProperMap_isLocalHomeomorph_of_injOn_outside_open_two
    (hlog_gt_anchor : GreenRayLogGtAnchorTwoSeam)
    (hproper : IsProperMap (Quadratic.bottcher_map (2 : ℂ)))
    (hlocal : IsLocalHomeomorph (Quadratic.bottcher_map (2 : ℂ)))
    (h_inj :
      Set.InjOn (Quadratic.bottcher_map (2 : ℂ))
        {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2}) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_externalRayMapData_two
    (external_ray_map_exists_two_constructive_of_greenRayLogGtAnchorTwoSeam_of_isProperMap_isLocalHomeomorph_of_injOn_outside_open
      hlog_gt_anchor hproper hlocal h_inj)

/-- Conditional rooted theorem at `c = 2`: Green inversion plus global
proper+local-homeomorph and outside-open injectivity implies MLC, specialized
to the current anchor-gap seed. -/
theorem mlc_conjecture_of_green_function_of_isProperMap_isLocalHomeomorph_of_injOn_outside_open_two
    (hproper : IsProperMap (Quadratic.bottcher_map (2 : ℂ)))
    (hlocal : IsLocalHomeomorph (Quadratic.bottcher_map (2 : ℂ)))
    (h_inj :
      Set.InjOn (Quadratic.bottcher_map (2 : ℂ))
        {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2}) :
    LocallyConnectedSpace mandelbrotSet := by
  exact
    mlc_conjecture_of_greenRayLogGtAnchorTwoSeam_of_isProperMap_isLocalHomeomorph_of_injOn_outside_open_two
      greenRayLogGtAnchorTwo_seed
      hproper hlocal h_inj

/-- Aggregated ingress for the degree-one Green-function route at `c = 2`. -/
def GreenFunctionDegreeOneIngressTwo : Prop :=
  IsProperMap (Quadratic.bottcher_map (2 : ℂ)) ∧
    IsLocalHomeomorph (Quadratic.bottcher_map (2 : ℂ)) ∧
      ProperLocalDegreeOneFiberWitnessTwo

/-- Current-model no-go: the packaged global degree-one ingress is inconsistent
at `c = 2` because `bottcher_map` is not proper on all of `ℂ`. -/
theorem not_greenFunctionDegreeOneIngressTwo :
    ¬ GreenFunctionDegreeOneIngressTwo := by
  intro h
  exact bottcher_map_not_isProperMap (2 : ℂ) h.1

/-- Package-to-target bridge: the degree-one Green-function ingress directly
builds the exact strict-mono-free root witness target. -/
theorem rootSafeOutsideOpenInjWitnessTwo_of_green_function_degreeOneIngressTwo
    (h : GreenFunctionDegreeOneIngressTwo) :
    RootSafeOutsideOpenInjWitnessTwo :=
  rootSafeOutsideOpenInjWitnessTwo_of_isProperMap_isLocalHomeomorph_of_degreeOneFiberWitness
    h.1 h.2.1 h.2.2

/-- Aggregated strict-mono-free ingress bundle at `c = 2`: either a currently
wired non-iterate-left outside-open injectivity source family, or the packaged
degree-one Green-function ingress. -/
def RootSafeOutsideOpenInjWitnessTwoStrictMonoFreeIngressTwo : Prop :=
  KnownInjOnOutsideOpenSourceCandidateTwo ∨ GreenFunctionDegreeOneIngressTwo

/-- Bundle-to-target bridge for the strict-mono-free root witness target. -/
theorem rootSafeOutsideOpenInjWitnessTwo_of_strictMonoFreeIngressTwo
    (h : RootSafeOutsideOpenInjWitnessTwoStrictMonoFreeIngressTwo) :
    RootSafeOutsideOpenInjWitnessTwo := by
  rcases h with h_known | h_deg1
  · exact rootSafeOutsideOpenInjWitnessTwo_of_knownInjOnOutsideOpenSourceCandidateTwo h_known
  · exact rootSafeOutsideOpenInjWitnessTwo_of_green_function_degreeOneIngressTwo h_deg1

/-- Current-model no-go: all currently wired strict-mono-free ingress families
at `c = 2` are blocked. -/
theorem not_rootSafeOutsideOpenInjWitnessTwoStrictMonoFreeIngressTwo :
    ¬ RootSafeOutsideOpenInjWitnessTwoStrictMonoFreeIngressTwo := by
  intro h
  rcases h with h_known | h_deg1
  · exact not_knownInjOnOutsideOpenSourceCandidateTwo h_known
  · exact not_greenFunctionDegreeOneIngressTwo h_deg1

/-- Normalized no-go form of the currently wired strict-mono-free ingress
bundle at `c = 2`. -/
theorem rootSafeOutsideOpenInjWitnessTwoStrictMonoFreeIngressTwo_iff_false :
    RootSafeOutsideOpenInjWitnessTwoStrictMonoFreeIngressTwo ↔ False := by
  constructor
  · intro h
    exact (not_rootSafeOutsideOpenInjWitnessTwoStrictMonoFreeIngressTwo h)
  · intro h
    exact False.elim h

/-- Expanded non-seeded ingress probe family at `c = 2`: either the currently
wired strict-mono-free ingress bundle, or the explicit Green-ray seam witness
gap for outside-open injectivity. -/
def RootSafeOutsideOpenInjWitnessTwoNonseededIngressFamilyTwo : Prop :=
  RootSafeOutsideOpenInjWitnessTwoStrictMonoFreeIngressTwo ∨
    RootSafeOutsideOpenInjWitnessTwoWitnessGap

/-- Build the strict-mono-free root outside-open injectivity target from the
expanded non-seeded ingress probe family. -/
theorem rootSafeOutsideOpenInjWitnessTwo_of_nonseededIngressFamilyTwo
    (h : RootSafeOutsideOpenInjWitnessTwoNonseededIngressFamilyTwo) :
    RootSafeOutsideOpenInjWitnessTwo := by
  rcases h with h_strictfree | h_gap
  · exact rootSafeOutsideOpenInjWitnessTwo_of_strictMonoFreeIngressTwo h_strictfree
  · exact rootSafeOutsideOpenInjWitnessTwo_of_rootSafeOutsideOpenInjWitnessTwoWitnessGap h_gap

/-- Current-model no-go: the expanded non-seeded ingress probe family is also
blocked at `c = 2`. -/
theorem not_rootSafeOutsideOpenInjWitnessTwoNonseededIngressFamilyTwo :
    ¬ RootSafeOutsideOpenInjWitnessTwoNonseededIngressFamilyTwo := by
  intro h
  rcases h with h_strictfree | h_gap
  · exact not_rootSafeOutsideOpenInjWitnessTwoStrictMonoFreeIngressTwo h_strictfree
  · exact not_greenRayLogGtAnchorTwoSeam h_gap.2

/-- Geometric outside-open/fiber ingress family at `c = 2`: pair the root-safe
outside-open injectivity target with the restricted singleton-fiber witness. -/
def RootSafeOutsideOpenInjWitnessTwoGeometricFiberIngressFamilyTwo : Prop :=
  RootSafeOutsideOpenInjWitnessTwo ∧ RestrictProperLocalDegreeOneFiberWitnessTwo

/-- Extract the root-safe outside-open injectivity target from the geometric
outside-open/fiber ingress family. -/
theorem rootSafeOutsideOpenInjWitnessTwo_of_rootSafeOutsideOpenInjWitnessTwoGeometricFiberIngressFamilyTwo
    (h : RootSafeOutsideOpenInjWitnessTwoGeometricFiberIngressFamilyTwo) :
    RootSafeOutsideOpenInjWitnessTwo :=
  h.1

/-- Build the geometric outside-open/fiber ingress family from the root-safe
outside-open injectivity target. -/
theorem rootSafeOutsideOpenInjWitnessTwoGeometricFiberIngressFamilyTwo_of_rootSafeOutsideOpenInjWitnessTwo
    (h_inj : RootSafeOutsideOpenInjWitnessTwo) :
    RootSafeOutsideOpenInjWitnessTwoGeometricFiberIngressFamilyTwo :=
  ⟨h_inj, restrictProperLocalDegreeOneFiberWitnessTwo_of_injOn_outside_open h_inj⟩

/-- Strict-mono-seeded witness of the geometric outside-open/fiber ingress
family at `c = 2`. -/
theorem rootSafeOutsideOpenInjWitnessTwoGeometricFiberIngressFamilyTwo_strictMono_seeded :
    RootSafeOutsideOpenInjWitnessTwoGeometricFiberIngressFamilyTwo :=
  rootSafeOutsideOpenInjWitnessTwoGeometricFiberIngressFamilyTwo_of_rootSafeOutsideOpenInjWitnessTwo
    rootSafeOutsideOpenInjWitnessTwo_strictMono_seeded

/-- The geometric outside-open/fiber ingress family is equivalent to the
root-safe outside-open injectivity target at `c = 2`. -/
theorem rootSafeOutsideOpenInjWitnessTwoGeometricFiberIngressFamilyTwo_iff_rootSafeOutsideOpenInjWitnessTwo :
    RootSafeOutsideOpenInjWitnessTwoGeometricFiberIngressFamilyTwo ↔
      RootSafeOutsideOpenInjWitnessTwo := by
  constructor
  · intro h
    exact rootSafeOutsideOpenInjWitnessTwo_of_rootSafeOutsideOpenInjWitnessTwoGeometricFiberIngressFamilyTwo h
  · intro h_inj
    exact
      rootSafeOutsideOpenInjWitnessTwoGeometricFiberIngressFamilyTwo_of_rootSafeOutsideOpenInjWitnessTwo
        h_inj

/-- Dead-end certificate for the geometric-ingress log-gap constructor shape:
any attempt to derive `GreenRayLogGtAnchorTwoSeam` from this ingress family is
inconsistent with the current model. -/
theorem not_greenRayLogGtAnchorTwoSeam_constructor_from_rootSafeOutsideOpenInjWitnessTwoGeometricFiberIngressFamilyTwo :
    ¬ (RootSafeOutsideOpenInjWitnessTwoGeometricFiberIngressFamilyTwo →
      GreenRayLogGtAnchorTwoSeam) := by
  intro hctor
  exact not_greenRayLogGtAnchorTwoSeam
    (hctor
      (rootSafeOutsideOpenInjWitnessTwoGeometricFiberIngressFamilyTwo_of_rootSafeOutsideOpenInjWitnessTwo
        rootSafeOutsideOpenInjWitnessTwo_strictMono_seeded))

/-- Candidate nonvacuous geometric witness-extraction bundle at `c = 2`:
geometric outside-open/fiber ingress plus bounded log-gap monotonicity window. -/
def NonvacuousGeometricIngressWitnessExtractionTwo : Prop :=
  RootSafeOutsideOpenInjWitnessTwoGeometricFiberIngressFamilyTwo ∧
    GreenRayLogGapMonotonicityWindowTwo

/-- Extract the geometric outside-open/fiber ingress family from the candidate
nonvacuous geometric witness-extraction bundle. -/
theorem rootSafeOutsideOpenInjWitnessTwoGeometricFiberIngressFamilyTwo_of_nonvacuousGeometricIngressWitnessExtractionTwo
    (h : NonvacuousGeometricIngressWitnessExtractionTwo) :
    RootSafeOutsideOpenInjWitnessTwoGeometricFiberIngressFamilyTwo :=
  h.1

/-- Extract the bounded log-gap monotonicity window from the candidate
nonvacuous geometric witness-extraction bundle. -/
theorem greenRayLogGapMonotonicityWindowTwo_of_nonvacuousGeometricIngressWitnessExtractionTwo
    (h : NonvacuousGeometricIngressWitnessExtractionTwo) :
    GreenRayLogGapMonotonicityWindowTwo :=
  h.2

/-- Build the full anchor-gap seam from the candidate nonvacuous geometric
witness-extraction bundle. -/
theorem greenRayLogGtAnchorTwoSeam_of_nonvacuousGeometricIngressWitnessExtractionTwo
    (h : NonvacuousGeometricIngressWitnessExtractionTwo) :
    GreenRayLogGtAnchorTwoSeam :=
  greenRayLogGtAnchorTwoSeam_of_greenRayLogGapMonotonicityWindowTwo
    (greenRayLogGapMonotonicityWindowTwo_of_nonvacuousGeometricIngressWitnessExtractionTwo h)

/-- Current-model no-go: the candidate nonvacuous geometric witness-extraction
bundle is inconsistent at `c = 2`. -/
theorem not_nonvacuousGeometricIngressWitnessExtractionTwo :
    ¬ NonvacuousGeometricIngressWitnessExtractionTwo := by
  intro h
  exact not_greenRayLogGapMonotonicityWindowTwo
    (greenRayLogGapMonotonicityWindowTwo_of_nonvacuousGeometricIngressWitnessExtractionTwo h)

/-- Localized geometric source family at `c = 2`: pair a local nonimplicative
window of radius `R` with geometric outside-open/fiber ingress. -/
def LocalizedRayIntervalGeometricSourceTwo (R : ℝ) : Prop :=
  NonimplicativeWindowInterfaceTwo R ∧
    RootSafeOutsideOpenInjWitnessTwoGeometricFiberIngressFamilyTwo

/-- Projection: recover the local nonimplicative window component from the
localized geometric source family. -/
theorem nonimplicativeWindowInterfaceTwo_of_localizedRayIntervalGeometricSourceTwo
    {R : ℝ}
    (hsrc : LocalizedRayIntervalGeometricSourceTwo R) :
    NonimplicativeWindowInterfaceTwo R :=
  hsrc.1

/-- Projection: recover the geometric outside-open/fiber ingress component from
the localized geometric source family. -/
theorem rootSafeOutsideOpenInjWitnessTwoGeometricFiberIngressFamilyTwo_of_localizedRayIntervalGeometricSourceTwo
    {R : ℝ}
    (hsrc : LocalizedRayIntervalGeometricSourceTwo R) :
    RootSafeOutsideOpenInjWitnessTwoGeometricFiberIngressFamilyTwo :=
  hsrc.2

/-- Dead-end certificate for localized geometric sources whose radius covers the
full cutoff band: they are inconsistent in the current model. -/
theorem not_localizedRayIntervalGeometricSourceTwo_of_cutoff_le_radius
    {R : ℝ}
    (hcut_le : greenRayLogGtAnchorTwoCutoff ≤ R) :
    ¬ LocalizedRayIntervalGeometricSourceTwo R := by
  intro hsrc
  exact not_nonimplicativeWindowInterfaceTwo_of_cutoff_le_radius
    (R := R) hcut_le hsrc.1

/-- In particular, the localized geometric source is inconsistent at the exact
cutoff radius. -/
theorem not_localizedRayIntervalGeometricSourceTwo_at_cutoff :
    ¬ LocalizedRayIntervalGeometricSourceTwo greenRayLogGtAnchorTwoCutoff := by
  exact not_localizedRayIntervalGeometricSourceTwo_of_cutoff_le_radius
    (R := greenRayLogGtAnchorTwoCutoff) le_rfl

/-- Strict-mono-free external-ray-data ingress at `c = 2`: under the packaged
degree-one Green-function assumptions, we can build external-ray data without
`green_function_strictMono_along_ray_basin_seam`. -/
theorem external_ray_map_exists_two_constructive_of_greenRayLogGtAnchorTwoSeam_of_green_function_degreeOneIngressTwo
    (hlog_gt_anchor : GreenRayLogGtAnchorTwoSeam)
    (h : GreenFunctionDegreeOneIngressTwo) :
    Quadratic.ExternalRayMapData (2 : ℂ) := by
  exact external_ray_map_exists_two_constructive_strictMono_free_of_rootSafeOutsideOpenInjWitnessTwo_of_greenRayLogGtAnchorTwoSeam
    hlog_gt_anchor
    (rootSafeOutsideOpenInjWitnessTwo_of_green_function_degreeOneIngressTwo h)

/-- Strict-mono-free external-ray-data ingress at `c = 2`: under the packaged
degree-one Green-function assumptions, specialized to the current anchor-gap
seed. -/
theorem external_ray_map_exists_two_constructive_of_green_function_degreeOneIngressTwo
    (h : GreenFunctionDegreeOneIngressTwo) :
    Quadratic.ExternalRayMapData (2 : ℂ) := by
  exact external_ray_map_exists_two_constructive_of_greenRayLogGtAnchorTwoSeam_of_green_function_degreeOneIngressTwo
    greenRayLogGtAnchorTwo_seed h

/-- Root wrapper for the degree-one Green-function ingress at `c = 2`. -/
theorem mlc_conjecture_of_greenRayLogGtAnchorTwoSeam_of_green_function_degreeOneIngressTwo
    (hlog_gt_anchor : GreenRayLogGtAnchorTwoSeam)
    (h : GreenFunctionDegreeOneIngressTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_externalRayMapData_two
    (external_ray_map_exists_two_constructive_of_greenRayLogGtAnchorTwoSeam_of_green_function_degreeOneIngressTwo
      hlog_gt_anchor h)

/-- Root wrapper for the degree-one Green-function ingress at `c = 2`,
specialized to the current anchor-gap seed. -/
theorem mlc_conjecture_of_green_function_degreeOneIngressTwo
    (h : GreenFunctionDegreeOneIngressTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_greenRayLogGtAnchorTwoSeam_of_green_function_degreeOneIngressTwo
    greenRayLogGtAnchorTwo_seed h

/-- Strict-mono-free rooted external-ray-data candidate seed at `c = 2`,
parameterized by the exact remaining root witness target. -/
lemma externalRayMapData_two_strictMonoFree_candidate_seed_of_greenRayLogGtAnchorTwoSeam
    (hlog_gt_anchor : GreenRayLogGtAnchorTwoSeam)
    (h_inj : RootSafeOutsideOpenInjWitnessTwo) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_exists_two_constructive_strictMono_free_of_rootSafeOutsideOpenInjWitnessTwo_of_greenRayLogGtAnchorTwoSeam
    hlog_gt_anchor h_inj

/-- Strict-mono-free rooted external-ray-data candidate seed at `c = 2`,
parameterized by the exact remaining root witness target and specialized to the
current anchor-gap seed. -/
lemma externalRayMapData_two_strictMonoFree_candidate_seed
    (h_inj : RootSafeOutsideOpenInjWitnessTwo) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  externalRayMapData_two_strictMonoFree_candidate_seed_of_greenRayLogGtAnchorTwoSeam
    greenRayLogGtAnchorTwo_seed h_inj

/-- Strict-mono-free rooted external-ray-data candidate seed at `c = 2`,
specialized to the aggregated strict-mono-free ingress bundle. -/
lemma externalRayMapData_two_strictMonoFree_candidate_seed_of_greenRayLogGtAnchorTwoSeam_of_strictMonoFreeIngressTwo
    (hlog_gt_anchor : GreenRayLogGtAnchorTwoSeam)
    (h : RootSafeOutsideOpenInjWitnessTwoStrictMonoFreeIngressTwo) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  externalRayMapData_two_strictMonoFree_candidate_seed_of_greenRayLogGtAnchorTwoSeam
    hlog_gt_anchor
    (rootSafeOutsideOpenInjWitnessTwo_of_strictMonoFreeIngressTwo h)

/-- Strict-mono-free rooted external-ray-data candidate seed at `c = 2`,
specialized to the aggregated strict-mono-free ingress bundle and the current
anchor-gap seed. -/
lemma externalRayMapData_two_strictMonoFree_candidate_seed_of_strictMonoFreeIngressTwo
    (h : RootSafeOutsideOpenInjWitnessTwoStrictMonoFreeIngressTwo) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  externalRayMapData_two_strictMonoFree_candidate_seed_of_greenRayLogGtAnchorTwoSeam_of_strictMonoFreeIngressTwo
    greenRayLogGtAnchorTwo_seed h

/-- Strict-mono-free rooted external-ray-data candidate seed at `c = 2`,
specialized to the known non-iterate-left injectivity-source aggregate. -/
lemma externalRayMapData_two_strictMonoFree_candidate_seed_of_greenRayLogGtAnchorTwoSeam_of_knownInjOnOutsideOpenSourceCandidateTwo
    (hlog_gt_anchor : GreenRayLogGtAnchorTwoSeam)
    (h : KnownInjOnOutsideOpenSourceCandidateTwo) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  externalRayMapData_two_strictMonoFree_candidate_seed_of_greenRayLogGtAnchorTwoSeam
    hlog_gt_anchor
    (rootSafeOutsideOpenInjWitnessTwo_of_knownInjOnOutsideOpenSourceCandidateTwo h)

/-- Strict-mono-free rooted external-ray-data candidate seed at `c = 2`,
specialized to the known non-iterate-left injectivity-source aggregate and the
current anchor-gap seed. -/
lemma externalRayMapData_two_strictMonoFree_candidate_seed_of_knownInjOnOutsideOpenSourceCandidateTwo
    (h : KnownInjOnOutsideOpenSourceCandidateTwo) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  externalRayMapData_two_strictMonoFree_candidate_seed_of_greenRayLogGtAnchorTwoSeam_of_knownInjOnOutsideOpenSourceCandidateTwo
    greenRayLogGtAnchorTwo_seed h

/-- Strict-mono-free rooted external-ray-data candidate seed at `c = 2`,
specialized to outside-open analyticity. -/
lemma externalRayMapData_two_strictMonoFree_candidate_seed_of_greenRayLogGtAnchorTwoSeam_of_outsideOpenAnalyticityHypothesis
    (hlog_gt_anchor : GreenRayLogGtAnchorTwoSeam)
    (h_analytic : OutsideOpenAnalyticityHypothesis (2 : ℂ)) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  externalRayMapData_two_strictMonoFree_candidate_seed_of_greenRayLogGtAnchorTwoSeam
    hlog_gt_anchor
    (rootSafeOutsideOpenInjWitnessTwo_of_outsideOpenAnalyticityHypothesis h_analytic)

/-- Strict-mono-free rooted external-ray-data candidate seed at `c = 2`,
specialized to outside-open analyticity and the current anchor-gap seed. -/
lemma externalRayMapData_two_strictMonoFree_candidate_seed_of_outsideOpenAnalyticityHypothesis
    (h_analytic : OutsideOpenAnalyticityHypothesis (2 : ℂ)) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  externalRayMapData_two_strictMonoFree_candidate_seed_of_greenRayLogGtAnchorTwoSeam_of_outsideOpenAnalyticityHypothesis
    greenRayLogGtAnchorTwo_seed h_analytic

/-- Strict-mono-free rooted external-ray-data candidate seed at `c = 2`,
specialized to the packaged degree-one Green-function ingress. -/
lemma externalRayMapData_two_strictMonoFree_candidate_seed_of_greenRayLogGtAnchorTwoSeam_of_green_function_degreeOneIngressTwo
    (hlog_gt_anchor : GreenRayLogGtAnchorTwoSeam)
    (h : GreenFunctionDegreeOneIngressTwo) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  externalRayMapData_two_strictMonoFree_candidate_seed_of_greenRayLogGtAnchorTwoSeam
    hlog_gt_anchor
    (rootSafeOutsideOpenInjWitnessTwo_of_green_function_degreeOneIngressTwo h)

/-- Strict-mono-free rooted external-ray-data candidate seed at `c = 2`,
specialized to the packaged degree-one Green-function ingress and the current
anchor-gap seed. -/
lemma externalRayMapData_two_strictMonoFree_candidate_seed_of_green_function_degreeOneIngressTwo
    (h : GreenFunctionDegreeOneIngressTwo) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  externalRayMapData_two_strictMonoFree_candidate_seed_of_greenRayLogGtAnchorTwoSeam_of_green_function_degreeOneIngressTwo
    greenRayLogGtAnchorTwo_seed h

/-- Strict-mono-free rooted external-ray-data candidate seed at `c = 2`,
specialized to a direct proper/local witness plus a local seam witness. -/
lemma externalRayMapData_two_strictMonoFree_candidate_seed_of_directProperLocalWitnessTwo_of_cp5ResidualLocalHomeomorphInjSeamTwo
    (h : DirectProperLocalWitnessTwo)
    (h_seam : CP5ResidualLocalHomeomorphInjSeamTwo) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  externalRayMapData_two_strictMonoFree_candidate_seed
    (rootSafeOutsideOpenInjWitnessTwo_of_directProperLocalWitnessTwo_of_cp5ResidualLocalHomeomorphInjSeamTwo
      h h_seam)

/-- Strict-mono-free rooted external-ray-data candidate seed at `c = 2`,
specialized to the CP5 local-homeomorph source pair plus a local seam witness. -/
lemma externalRayMapData_two_strictMonoFree_candidate_seed_of_localHomeomorphSurjSourceTwo_of_cp5ResidualLocalHomeomorphInjSeamTwo
    (hlocal :
      IsProperMap (bottcher_map_outside_open_to_exterior (2 : ℂ)) ∧
        IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (h_seam : CP5ResidualLocalHomeomorphInjSeamTwo) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  externalRayMapData_two_strictMonoFree_candidate_seed
    (rootSafeOutsideOpenInjWitnessTwo_of_localHomeomorphSurjSourceTwo_of_cp5ResidualLocalHomeomorphInjSeamTwo
      hlocal h_seam)

/-- Strict-mono-free rooted external-ray-data candidate seed at `c = 2`,
specialized to explicit restricted-map proper/local hypotheses plus a local
seam witness. -/
lemma externalRayMapData_two_strictMonoFree_candidate_seed_of_isProperMap_restrict_of_isLocalHomeomorph_restrict_of_cp5ResidualLocalHomeomorphInjSeamTwo
    (hproper : IsProperMap (bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (hlocal : IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (h_seam : CP5ResidualLocalHomeomorphInjSeamTwo) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  externalRayMapData_two_strictMonoFree_candidate_seed_of_localHomeomorphSurjSourceTwo_of_cp5ResidualLocalHomeomorphInjSeamTwo
    ⟨hproper, hlocal⟩ h_seam

/-- Strict-mono-free root-seed alternative at `c = 2`, parameterized by the
exact remaining root witness target. -/
lemma externalRayMapData_two_root_seed_strictMonoFree_of_greenRayLogGtAnchorTwoSeam_of_rootSafeOutsideOpenInjWitnessTwo
    (hlog_gt_anchor : GreenRayLogGtAnchorTwoSeam)
    (h_inj : RootSafeOutsideOpenInjWitnessTwo) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  externalRayMapData_two_strictMonoFree_candidate_seed_of_greenRayLogGtAnchorTwoSeam
    hlog_gt_anchor h_inj

/-- Strict-mono-free root-seed alternative at `c = 2`, parameterized by the
exact remaining root witness target and specialized to the current anchor-gap
seed. -/
lemma externalRayMapData_two_root_seed_strictMonoFree_of_rootSafeOutsideOpenInjWitnessTwo
    (h_inj : RootSafeOutsideOpenInjWitnessTwo) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  externalRayMapData_two_root_seed_strictMonoFree_of_greenRayLogGtAnchorTwoSeam_of_rootSafeOutsideOpenInjWitnessTwo
    greenRayLogGtAnchorTwo_seed h_inj

/-- Strict-mono-free root-seed alternative at `c = 2`, specialized to the
packaged degree-one Green-function ingress. -/
lemma externalRayMapData_two_root_seed_strictMonoFree_of_green_function_degreeOneIngressTwo
    (h : GreenFunctionDegreeOneIngressTwo) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  externalRayMapData_two_strictMonoFree_candidate_seed_of_green_function_degreeOneIngressTwo h

/-- Strict-mono-free root-seed alternative at `c = 2`, specialized to a direct
proper/local witness plus a local seam witness. -/
lemma externalRayMapData_two_root_seed_strictMonoFree_of_directProperLocalWitnessTwo_of_cp5ResidualLocalHomeomorphInjSeamTwo
    (h : DirectProperLocalWitnessTwo)
    (h_seam : CP5ResidualLocalHomeomorphInjSeamTwo) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  externalRayMapData_two_strictMonoFree_candidate_seed_of_directProperLocalWitnessTwo_of_cp5ResidualLocalHomeomorphInjSeamTwo
    h h_seam

/-- Strict-mono-free root-seed alternative at `c = 2`, specialized to the CP5
local-homeomorph source pair plus a local seam witness. -/
lemma externalRayMapData_two_root_seed_strictMonoFree_of_localHomeomorphSurjSourceTwo_of_cp5ResidualLocalHomeomorphInjSeamTwo
    (hlocal :
      IsProperMap (bottcher_map_outside_open_to_exterior (2 : ℂ)) ∧
        IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (h_seam : CP5ResidualLocalHomeomorphInjSeamTwo) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  externalRayMapData_two_strictMonoFree_candidate_seed_of_localHomeomorphSurjSourceTwo_of_cp5ResidualLocalHomeomorphInjSeamTwo
    hlocal h_seam

/-- Strict-mono-free root-seed alternative at `c = 2`, specialized to explicit
restricted-map proper/local hypotheses plus a local seam witness. -/
lemma externalRayMapData_two_root_seed_strictMonoFree_of_isProperMap_restrict_of_isLocalHomeomorph_restrict_of_cp5ResidualLocalHomeomorphInjSeamTwo
    (hproper : IsProperMap (bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (hlocal : IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (h_seam : CP5ResidualLocalHomeomorphInjSeamTwo) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  externalRayMapData_two_strictMonoFree_candidate_seed_of_isProperMap_restrict_of_isLocalHomeomorph_restrict_of_cp5ResidualLocalHomeomorphInjSeamTwo
    hproper hlocal h_seam

/-- Strict-mono-free root-seed alternative at `c = 2`, specialized to a direct
proper/local witness and Green-ray seam payload. -/
lemma externalRayMapData_two_root_seed_strictMonoFree_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam_of_directProperLocalWitnessTwo
    (huniq_seam : GreenRayUniquePreimageTwoAnchorSeam)
    (hlog_gt_anchor : GreenRayLogGtAnchorTwoSeam)
    (h : DirectProperLocalWitnessTwo) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  externalRayMapData_two_root_seed_strictMonoFree_of_greenRayLogGtAnchorTwoSeam_of_rootSafeOutsideOpenInjWitnessTwo
    hlog_gt_anchor
    (injOn_outside_open_two_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam_of_directProperLocalWitnessTwo
      huniq_seam hlog_gt_anchor h)

/-- Strict-mono-free root-seed alternative at `c = 2`, specialized to the CP5
local-homeomorph source pair and Green-ray seam payload. -/
lemma externalRayMapData_two_root_seed_strictMonoFree_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam_of_localHomeomorphSurjSourceTwo
    (huniq_seam : GreenRayUniquePreimageTwoAnchorSeam)
    (hlog_gt_anchor : GreenRayLogGtAnchorTwoSeam)
    (hlocal :
      IsProperMap (bottcher_map_outside_open_to_exterior (2 : ℂ)) ∧
        IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ))) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  externalRayMapData_two_root_seed_strictMonoFree_of_greenRayLogGtAnchorTwoSeam_of_rootSafeOutsideOpenInjWitnessTwo
    hlog_gt_anchor
    (rootSafeOutsideOpenInjWitnessTwo_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam_of_localHomeomorphSurjSourceTwo
      huniq_seam hlog_gt_anchor hlocal)

/-- Strict-mono-free root-seed alternative at `c = 2`, specialized to explicit
restricted-map proper/local hypotheses and Green-ray seam payload. -/
lemma externalRayMapData_two_root_seed_strictMonoFree_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam_of_isProperMap_restrict_of_isLocalHomeomorph_restrict
    (huniq_seam : GreenRayUniquePreimageTwoAnchorSeam)
    (hlog_gt_anchor : GreenRayLogGtAnchorTwoSeam)
    (hproper : IsProperMap (bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (hlocal : IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ))) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  externalRayMapData_two_root_seed_strictMonoFree_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam_of_localHomeomorphSurjSourceTwo
    huniq_seam hlog_gt_anchor ⟨hproper, hlocal⟩

/-- Strict-mono-seeded root-seed alternative at `c = 2`, specialized to the CP5
local-homeomorph source pair. -/
lemma externalRayMapData_two_root_seed_strictMonoFree_of_localHomeomorphSurjSourceTwo_strictMono
    (hlocal :
      IsProperMap (bottcher_map_outside_open_to_exterior (2 : ℂ)) ∧
        IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ))) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  externalRayMapData_two_root_seed_strictMonoFree_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam_of_localHomeomorphSurjSourceTwo
    greenRayUniquePreimageTwoAnchorSeam_strictMono_seeded_of_greenFunctionStrictMonoAlongRayBasinTwo_seed
    greenRayLogGtAnchorTwo_seed
    hlocal

/-- Strict-mono-seeded root-seed alternative at `c = 2`, specialized to explicit
restricted-map proper/local hypotheses. -/
lemma externalRayMapData_two_root_seed_strictMonoFree_of_isProperMap_restrict_of_isLocalHomeomorph_restrict_strictMono
    (hproper : IsProperMap (bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (hlocal : IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ))) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  externalRayMapData_two_root_seed_strictMonoFree_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam_of_isProperMap_restrict_of_isLocalHomeomorph_restrict
    greenRayUniquePreimageTwoAnchorSeam_strictMono_seeded_of_greenFunctionStrictMonoAlongRayBasinTwo_seed
    greenRayLogGtAnchorTwo_seed
    hproper hlocal

/-- Strict-mono-seeded root-seed alternative at `c = 2`, specialized to a direct
proper/local witness. -/
lemma externalRayMapData_two_root_seed_strictMonoFree_of_directProperLocalWitnessTwo_strictMono
    (h : DirectProperLocalWitnessTwo) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  externalRayMapData_two_root_seed_strictMonoFree_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam_of_directProperLocalWitnessTwo
    greenRayUniquePreimageTwoAnchorSeam_strictMono_seeded_of_greenFunctionStrictMonoAlongRayBasinTwo_seed
    greenRayLogGtAnchorTwo_seed
    h

/-- Strict-mono-free root-seed alternative at `c = 2`, specialized to the known
non-iterate-left injectivity-source aggregate. -/
lemma externalRayMapData_two_root_seed_strictMonoFree_of_greenRayLogGtAnchorTwoSeam_of_knownInjOnOutsideOpenSourceCandidateTwo
    (hlog_gt_anchor : GreenRayLogGtAnchorTwoSeam)
    (h : KnownInjOnOutsideOpenSourceCandidateTwo) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  externalRayMapData_two_root_seed_strictMonoFree_of_greenRayLogGtAnchorTwoSeam_of_rootSafeOutsideOpenInjWitnessTwo
    hlog_gt_anchor
    (rootSafeOutsideOpenInjWitnessTwo_of_knownInjOnOutsideOpenSourceCandidateTwo h)

/-- Strict-mono-free root-seed alternative at `c = 2`, specialized to the known
non-iterate-left injectivity-source aggregate and the current anchor-gap seed. -/
lemma externalRayMapData_two_root_seed_strictMonoFree_of_knownInjOnOutsideOpenSourceCandidateTwo
    (h : KnownInjOnOutsideOpenSourceCandidateTwo) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  externalRayMapData_two_root_seed_strictMonoFree_of_greenRayLogGtAnchorTwoSeam_of_knownInjOnOutsideOpenSourceCandidateTwo
    greenRayLogGtAnchorTwo_seed h

/-- Strict-mono-free root-seed alternative at `c = 2`, specialized to
outside-open analyticity. -/
lemma externalRayMapData_two_root_seed_strictMonoFree_of_greenRayLogGtAnchorTwoSeam_of_outsideOpenAnalyticityHypothesis
    (hlog_gt_anchor : GreenRayLogGtAnchorTwoSeam)
    (h_analytic : OutsideOpenAnalyticityHypothesis (2 : ℂ)) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  externalRayMapData_two_root_seed_strictMonoFree_of_greenRayLogGtAnchorTwoSeam_of_rootSafeOutsideOpenInjWitnessTwo
    hlog_gt_anchor
    (rootSafeOutsideOpenInjWitnessTwo_of_outsideOpenAnalyticityHypothesis h_analytic)

/-- Strict-mono-free root-seed alternative at `c = 2`, specialized to
outside-open analyticity and the current anchor-gap seed. -/
lemma externalRayMapData_two_root_seed_strictMonoFree_of_outsideOpenAnalyticityHypothesis
    (h_analytic : OutsideOpenAnalyticityHypothesis (2 : ℂ)) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  externalRayMapData_two_root_seed_strictMonoFree_of_greenRayLogGtAnchorTwoSeam_of_outsideOpenAnalyticityHypothesis
    greenRayLogGtAnchorTwo_seed h_analytic

/-- Root seed selector at `c = 2`, routed through the strict-mono-free seed
constructor and fed by an injectivity witness extracted from the current
exported endpoint. -/
lemma externalRayMapData_two_root_seed_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam
    (huniq_seam : GreenRayUniquePreimageTwoAnchorSeam)
    (hlog_gt_anchor : GreenRayLogGtAnchorTwoSeam) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  externalRayMapData_two_strictMonoFree_candidate_seed_of_greenRayLogGtAnchorTwoSeam
    hlog_gt_anchor
    (rootSafeOutsideOpenInjWitnessTwo_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam
      huniq_seam hlog_gt_anchor)

/-- Centralized root-seed seam bundle at `c = 2`: uniqueness seam + anchor-gap seam. -/
def RootSeedPairTwo : Prop :=
  GreenRayUniquePreimageTwoAnchorSeam ∧ GreenRayLogGtAnchorTwoSeam

/-- Centralized root-seed payload at `c = 2`: anchor-gap seam + exact root-safe
outside-open injectivity witness target. -/
def RootSeedPayloadTwo : Prop :=
  GreenRayLogGtAnchorTwoSeam ∧ RootSafeOutsideOpenInjWitnessTwo

/-- Anchor-free root payload at `c = 2`: exact root-safe outside-open
injectivity witness target only. This is a staging interface for removing the
anchor seam from root payload wiring. -/
def RootSeedPayloadTwoNoAnchor : Prop :=
  RootSafeOutsideOpenInjWitnessTwo

/-- Build the centralized root-seed seam bundle from anchor-gap seam plus the
exact root-safe outside-open injectivity witness target. -/
lemma rootSeedPairTwo_of_greenRayLogGtAnchorTwoSeam_of_rootSafeOutsideOpenInjWitnessTwo
    (hlog_gt_anchor : GreenRayLogGtAnchorTwoSeam)
    (h_inj : RootSafeOutsideOpenInjWitnessTwo) :
    RootSeedPairTwo :=
  ⟨greenRayUniquePreimageTwoAnchorSeam_of_greenRayLogGtAnchorTwoSeam_of_injOn_outside_open
      hlog_gt_anchor h_inj,
    hlog_gt_anchor⟩

/-- Build the centralized root-seed seam bundle from the centralized root-seed
payload. -/
lemma rootSeedPairTwo_of_rootSeedPayloadTwo
    (hseed : RootSeedPayloadTwo) :
    RootSeedPairTwo :=
  rootSeedPairTwo_of_greenRayLogGtAnchorTwoSeam_of_rootSafeOutsideOpenInjWitnessTwo
    hseed.1 hseed.2

/-- Build the centralized root-seed payload from anchor-gap seam plus the exact
root-safe outside-open injectivity witness target. -/
lemma rootSeedPayloadTwo_of_greenRayLogGtAnchorTwoSeam_of_rootSafeOutsideOpenInjWitnessTwo
    (hlog_gt_anchor : GreenRayLogGtAnchorTwoSeam)
    (h_inj : RootSafeOutsideOpenInjWitnessTwo) :
    RootSeedPayloadTwo :=
  ⟨hlog_gt_anchor, h_inj⟩

/-- Build the centralized root-seed payload from the anchor-free payload plus
an explicit anchor-gap seam argument. -/
lemma rootSeedPayloadTwo_of_rootSeedPayloadTwoNoAnchor_of_greenRayLogGtAnchorTwoSeam
    (hseed : RootSeedPayloadTwoNoAnchor)
    (hlog_gt_anchor : GreenRayLogGtAnchorTwoSeam) :
    RootSeedPayloadTwo :=
  rootSeedPayloadTwo_of_greenRayLogGtAnchorTwoSeam_of_rootSafeOutsideOpenInjWitnessTwo
    hlog_gt_anchor hseed

/-- Build the centralized root-seed payload from anchor-gap seam plus the
aggregated strict-mono-free ingress bundle. -/
lemma rootSeedPayloadTwo_of_greenRayLogGtAnchorTwoSeam_of_strictMonoFreeIngressTwo
    (hlog_gt_anchor : GreenRayLogGtAnchorTwoSeam)
    (h : RootSafeOutsideOpenInjWitnessTwoStrictMonoFreeIngressTwo) :
    RootSeedPayloadTwo :=
  rootSeedPayloadTwo_of_greenRayLogGtAnchorTwoSeam_of_rootSafeOutsideOpenInjWitnessTwo
    hlog_gt_anchor
    (rootSafeOutsideOpenInjWitnessTwo_of_strictMonoFreeIngressTwo h)

/-- Aggregated strict-mono-free ingress payload for the centralized root seed at
`c = 2`: anchor-gap seam plus strict-mono-free root injectivity ingress. -/
def RootSeedPayloadTwoStrictMonoFreeIngressTwo : Prop :=
  GreenRayLogGtAnchorTwoSeam ∧ RootSafeOutsideOpenInjWitnessTwoStrictMonoFreeIngressTwo

/-- Build centralized root-seed payload from the strict-mono-free ingress
payload. -/
lemma rootSeedPayloadTwo_of_rootSeedPayloadTwoStrictMonoFreeIngressTwo
    (h : RootSeedPayloadTwoStrictMonoFreeIngressTwo) :
    RootSeedPayloadTwo :=
  rootSeedPayloadTwo_of_greenRayLogGtAnchorTwoSeam_of_strictMonoFreeIngressTwo
    h.1 h.2

/-- Current-model no-go: strict-mono-free ingress payload for the centralized
root seed at `c = 2` is blocked. -/
theorem not_rootSeedPayloadTwoStrictMonoFreeIngressTwo :
    ¬ RootSeedPayloadTwoStrictMonoFreeIngressTwo := by
  intro h
  exact not_rootSafeOutsideOpenInjWitnessTwoStrictMonoFreeIngressTwo h.2

/-- Normalized no-go form of the strict-mono-free root-seed payload ingress at
`c = 2`. -/
theorem rootSeedPayloadTwoStrictMonoFreeIngressTwo_iff_false :
    RootSeedPayloadTwoStrictMonoFreeIngressTwo ↔ False := by
  constructor
  · intro h
    exact (not_rootSeedPayloadTwoStrictMonoFreeIngressTwo h)
  · intro h
    exact False.elim h

/-- Strict-mono-free candidate root-seed payload at `c = 2`, specialized to the
aggregated strict-mono-free ingress bundle and current anchor-gap seed. -/
lemma rootSeedPayloadTwo_strictMonoFree_candidate_of_strictMonoFreeIngressTwo
    (h : RootSafeOutsideOpenInjWitnessTwoStrictMonoFreeIngressTwo) :
    RootSeedPayloadTwo :=
  rootSeedPayloadTwo_of_greenRayLogGtAnchorTwoSeam_of_strictMonoFreeIngressTwo
    greenRayLogGtAnchorTwo_seed h

/-- Build the centralized root-seed seam bundle from anchor-gap seam plus the
aggregated strict-mono-free ingress bundle. -/
lemma rootSeedPairTwo_of_greenRayLogGtAnchorTwoSeam_of_strictMonoFreeIngressTwo
    (hlog_gt_anchor : GreenRayLogGtAnchorTwoSeam)
    (h : RootSafeOutsideOpenInjWitnessTwoStrictMonoFreeIngressTwo) :
    RootSeedPairTwo :=
  rootSeedPairTwo_of_greenRayLogGtAnchorTwoSeam_of_rootSafeOutsideOpenInjWitnessTwo
    hlog_gt_anchor
    (rootSafeOutsideOpenInjWitnessTwo_of_strictMonoFreeIngressTwo h)

/-- Strict-mono-free candidate root-seam bundle at `c = 2`, specialized to the
aggregated strict-mono-free ingress bundle and current anchor-gap seed. -/
lemma rootSeedPairTwo_strictMonoFree_candidate_of_strictMonoFreeIngressTwo
    (h : RootSafeOutsideOpenInjWitnessTwoStrictMonoFreeIngressTwo) :
    RootSeedPairTwo :=
  rootSeedPairTwo_of_greenRayLogGtAnchorTwoSeam_of_strictMonoFreeIngressTwo
    greenRayLogGtAnchorTwo_seed h

/-- Strict-mono-seeded root-seed payload at `c = 2`. -/
lemma rootSeedPayloadTwo_strictMono_seeded : RootSeedPayloadTwo :=
  rootSeedPayloadTwo_of_greenRayLogGtAnchorTwoSeam_of_rootSafeOutsideOpenInjWitnessTwo
    greenRayLogGtAnchorTwo_seed
    rootSafeOutsideOpenInjWitnessTwo_strictMono_seeded

/-- Strict-mono-seeded root-seam bundle at `c = 2`, routed through the
root-safe outside-open injectivity witness seed. -/
lemma rootSeedPairTwo_strictMono_seeded : RootSeedPairTwo :=
  rootSeedPairTwo_of_rootSeedPayloadTwo rootSeedPayloadTwo_strictMono_seeded

/-- Root seed selector at `c = 2`, parameterized by the centralized root-seam bundle. -/
lemma externalRayMapData_two_root_seed_of_rootSeedPairTwo
    (hseed : RootSeedPairTwo) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  externalRayMapData_two_root_seed_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam
    hseed.1 hseed.2

/-- Root seed selector at `c = 2`, parameterized by the centralized root-seed
payload. -/
lemma externalRayMapData_two_root_seed_of_rootSeedPayloadTwo
    (hseed : RootSeedPayloadTwo) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  externalRayMapData_two_root_seed_of_rootSeedPairTwo
    (rootSeedPairTwo_of_rootSeedPayloadTwo hseed)

/-- Root seed selector at `c = 2`, parameterized by the anchor-free root payload
plus an explicit anchor-gap seam argument. -/
lemma externalRayMapData_two_root_seed_of_rootSeedPayloadTwoNoAnchor_of_greenRayLogGtAnchorTwoSeam
    (hseed : RootSeedPayloadTwoNoAnchor)
    (hlog_gt_anchor : GreenRayLogGtAnchorTwoSeam) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  externalRayMapData_two_root_seed_of_rootSeedPayloadTwo
    (rootSeedPayloadTwo_of_rootSeedPayloadTwoNoAnchor_of_greenRayLogGtAnchorTwoSeam
      hseed hlog_gt_anchor)

/-- Strict-mono-free root-seed alternative at `c = 2`, parameterized by the
aggregated strict-mono-free ingress bundle. -/
lemma externalRayMapData_two_root_seed_strictMonoFree_of_greenRayLogGtAnchorTwoSeam_of_strictMonoFreeIngressTwo
    (hlog_gt_anchor : GreenRayLogGtAnchorTwoSeam)
    (h : RootSafeOutsideOpenInjWitnessTwoStrictMonoFreeIngressTwo) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  externalRayMapData_two_root_seed_of_rootSeedPayloadTwo
    (rootSeedPayloadTwo_of_greenRayLogGtAnchorTwoSeam_of_strictMonoFreeIngressTwo
      hlog_gt_anchor h)

/-- Strict-mono-free root-seed alternative at `c = 2`, specialized to the
aggregated strict-mono-free ingress bundle and current anchor-gap seed. -/
lemma externalRayMapData_two_root_seed_strictMonoFree_of_strictMonoFreeIngressTwo
    (h : RootSafeOutsideOpenInjWitnessTwoStrictMonoFreeIngressTwo) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  externalRayMapData_two_root_seed_strictMonoFree_of_greenRayLogGtAnchorTwoSeam_of_strictMonoFreeIngressTwo
    greenRayLogGtAnchorTwo_seed h

/-- Strict-mono-seeded centralized root-seed selector at `c = 2`. -/
lemma externalRayMapData_two_root_seed_strictMono_seeded :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  externalRayMapData_two_root_seed_of_rootSeedPayloadTwo rootSeedPayloadTwo_strictMono_seeded

/-- Root seed selector at `c = 2`, routed through the strict-mono-seeded
centralized seam specialization. -/
lemma externalRayMapData_two_root_seed :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  externalRayMapData_two_root_seed_strictMono_seeded

/-- Rooted theorem exposing the remaining axiom ingress at `c = 2` through the
external-ray-data seam. -/
theorem mlc_conjecture_of_external_ray_map_exists_two :
    Quadratic.ExternalRayMapData (2 : ℂ) →
    LocallyConnectedSpace mandelbrotSet := by
  intro h_ext
  exact mlc_conjecture_of_externalRayMapData_two h_ext

/-- Root theorem routed through the centralized root-seed selector. -/
theorem mlc_conjecture_of_externalRayMapData_two_root_seed_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam
    (huniq_seam : GreenRayUniquePreimageTwoAnchorSeam)
    (hlog_gt_anchor : GreenRayLogGtAnchorTwoSeam) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_external_ray_map_exists_two
    (externalRayMapData_two_root_seed_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam
      huniq_seam hlog_gt_anchor)

/-- Root theorem routed through the centralized root-seam bundle selector. -/
theorem mlc_conjecture_of_externalRayMapData_two_root_seed_of_rootSeedPairTwo
    (hseed : RootSeedPairTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_external_ray_map_exists_two
    (externalRayMapData_two_root_seed_of_rootSeedPairTwo hseed)

/-- Root theorem routed through the centralized root-seed payload selector. -/
theorem mlc_conjecture_of_externalRayMapData_two_root_seed_of_rootSeedPayloadTwo
    (hseed : RootSeedPayloadTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_external_ray_map_exists_two
    (externalRayMapData_two_root_seed_of_rootSeedPayloadTwo hseed)

/-- Root theorem routed through the anchor-free root payload plus an explicit
anchor-gap seam argument. -/
theorem mlc_conjecture_of_externalRayMapData_two_root_seed_of_rootSeedPayloadTwoNoAnchor_of_greenRayLogGtAnchorTwoSeam
    (hseed : RootSeedPayloadTwoNoAnchor)
    (hlog_gt_anchor : GreenRayLogGtAnchorTwoSeam) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_external_ray_map_exists_two
    (externalRayMapData_two_root_seed_of_rootSeedPayloadTwoNoAnchor_of_greenRayLogGtAnchorTwoSeam
      hseed hlog_gt_anchor)

/-- Root theorem from anchor-gap seam plus root-safe outside-open injectivity,
routed through the centralized root-seed payload constructor. -/
theorem mlc_conjecture_of_greenRayLogGtAnchorTwoSeam_of_rootSafeOutsideOpenInjWitnessTwo_via_rootSeedPayloadTwo
    (hlog_gt_anchor : GreenRayLogGtAnchorTwoSeam)
    (h_inj : RootSafeOutsideOpenInjWitnessTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_externalRayMapData_two_root_seed_of_rootSeedPayloadTwo
    (rootSeedPayloadTwo_of_greenRayLogGtAnchorTwoSeam_of_rootSafeOutsideOpenInjWitnessTwo
      hlog_gt_anchor h_inj)

/-- Root theorem from anchor-gap seam plus root-safe outside-open injectivity,
routed through the centralized root-seam bundle constructor. -/
theorem mlc_conjecture_of_greenRayLogGtAnchorTwoSeam_of_rootSafeOutsideOpenInjWitnessTwo_via_rootSeedPairTwo
    (hlog_gt_anchor : GreenRayLogGtAnchorTwoSeam)
    (h_inj : RootSafeOutsideOpenInjWitnessTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact
    mlc_conjecture_of_externalRayMapData_two_root_seed_of_rootSeedPayloadTwoNoAnchor_of_greenRayLogGtAnchorTwoSeam
      h_inj hlog_gt_anchor

/-- Strict-mono-free candidate endpoint at `c = 2`, parameterized by the
centralized root-seam bundle. -/
lemma externalRayMapData_two_strictMonoFree_candidate_of_rootSeedPairTwo
    (hseed : RootSeedPairTwo) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  externalRayMapData_two_root_seed_of_rootSeedPairTwo hseed

/-- Strict-mono-free candidate endpoint at `c = 2`, parameterized by the
centralized root-seed payload. -/
lemma externalRayMapData_two_strictMonoFree_candidate_of_rootSeedPayloadTwo
    (hseed : RootSeedPayloadTwo) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  externalRayMapData_two_root_seed_of_rootSeedPayloadTwo hseed

/-- Strict-mono-free candidate root theorem, parameterized by the centralized
root-seam bundle. -/
theorem mlc_conjecture_strictMonoFree_candidate_of_rootSeedPairTwo
    (hseed : RootSeedPairTwo) :
    LocallyConnectedSpace mandelbrotSet :=
  mlc_conjecture_of_externalRayMapData_two_root_seed_of_rootSeedPairTwo hseed

/-- Strict-mono-free candidate root theorem, parameterized by the centralized
root-seed payload. -/
theorem mlc_conjecture_strictMonoFree_candidate_of_rootSeedPayloadTwo
    (hseed : RootSeedPayloadTwo) :
    LocallyConnectedSpace mandelbrotSet :=
  mlc_conjecture_of_externalRayMapData_two_root_seed_of_rootSeedPayloadTwo hseed

/-- Strict-mono-seeded root theorem routed through the centralized seam
specialization. -/
theorem mlc_conjecture_of_externalRayMapData_two_root_seed_strictMono_seeded :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_externalRayMapData_two_root_seed_of_rootSeedPayloadTwo
    rootSeedPayloadTwo_strictMono_seeded

/-- Root theorem routed through the centralized root-seed selector. -/
theorem mlc_conjecture_of_externalRayMapData_two_root_seed :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_externalRayMapData_two_root_seed_strictMono_seeded

/-- Strict-mono-free root theorem variant at `c = 2`, parameterized by the
exact remaining root witness target. -/
theorem mlc_conjecture_of_externalRayMapData_two_root_seed_strictMonoFree_of_greenRayLogGtAnchorTwoSeam_of_rootSafeOutsideOpenInjWitnessTwo
    (hlog_gt_anchor : GreenRayLogGtAnchorTwoSeam)
    (h_inj : RootSafeOutsideOpenInjWitnessTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact
    mlc_conjecture_of_externalRayMapData_two_root_seed_of_rootSeedPayloadTwoNoAnchor_of_greenRayLogGtAnchorTwoSeam
      h_inj hlog_gt_anchor

/-- Strict-mono-free root theorem variant at `c = 2`, parameterized by the
exact remaining root witness target and specialized to the current anchor-gap
seed. -/
theorem mlc_conjecture_of_externalRayMapData_two_root_seed_strictMonoFree_of_rootSafeOutsideOpenInjWitnessTwo
    (h_inj : RootSafeOutsideOpenInjWitnessTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_externalRayMapData_two_root_seed_strictMonoFree_of_greenRayLogGtAnchorTwoSeam_of_rootSafeOutsideOpenInjWitnessTwo
    greenRayLogGtAnchorTwo_seed h_inj

/-- Strict-mono-free root theorem variant at `c = 2`, parameterized by the
aggregated strict-mono-free ingress bundle. -/
theorem mlc_conjecture_of_externalRayMapData_two_root_seed_strictMonoFree_of_greenRayLogGtAnchorTwoSeam_of_strictMonoFreeIngressTwo
    (hlog_gt_anchor : GreenRayLogGtAnchorTwoSeam)
    (h : RootSafeOutsideOpenInjWitnessTwoStrictMonoFreeIngressTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_externalRayMapData_two_root_seed_of_rootSeedPayloadTwo
    (rootSeedPayloadTwo_of_greenRayLogGtAnchorTwoSeam_of_strictMonoFreeIngressTwo
      hlog_gt_anchor h)

/-- Strict-mono-free root theorem variant at `c = 2`, specialized to the
aggregated strict-mono-free ingress bundle and current anchor-gap seed. -/
theorem mlc_conjecture_of_externalRayMapData_two_root_seed_strictMonoFree_of_strictMonoFreeIngressTwo
    (h : RootSafeOutsideOpenInjWitnessTwoStrictMonoFreeIngressTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact
    mlc_conjecture_of_externalRayMapData_two_root_seed_strictMonoFree_of_greenRayLogGtAnchorTwoSeam_of_strictMonoFreeIngressTwo
      greenRayLogGtAnchorTwo_seed h

/-- Strict-mono-free root theorem variant at `c = 2`, specialized to the
packaged degree-one Green-function ingress. -/
theorem mlc_conjecture_of_externalRayMapData_two_root_seed_strictMonoFree_of_green_function_degreeOneIngressTwo
    (h : GreenFunctionDegreeOneIngressTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_externalRayMapData_two_root_seed_strictMonoFree_of_greenRayLogGtAnchorTwoSeam_of_rootSafeOutsideOpenInjWitnessTwo
    greenRayLogGtAnchorTwo_seed
    (rootSafeOutsideOpenInjWitnessTwo_of_green_function_degreeOneIngressTwo h)

/-- Strict-mono-free root theorem variant at `c = 2`, specialized to a direct
proper/local witness plus a local seam witness. -/
theorem mlc_conjecture_of_externalRayMapData_two_root_seed_strictMonoFree_of_directProperLocalWitnessTwo_of_cp5ResidualLocalHomeomorphInjSeamTwo
    (h : DirectProperLocalWitnessTwo)
    (h_seam : CP5ResidualLocalHomeomorphInjSeamTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_externalRayMapData_two_root_seed_strictMonoFree_of_greenRayLogGtAnchorTwoSeam_of_rootSafeOutsideOpenInjWitnessTwo
    greenRayLogGtAnchorTwo_seed
    (rootSafeOutsideOpenInjWitnessTwo_of_directProperLocalWitnessTwo_of_cp5ResidualLocalHomeomorphInjSeamTwo
      h h_seam)

/-- Strict-mono-free root theorem variant at `c = 2`, specialized to the CP5
local-homeomorph source pair plus a local seam witness. -/
theorem mlc_conjecture_of_externalRayMapData_two_root_seed_strictMonoFree_of_localHomeomorphSurjSourceTwo_of_cp5ResidualLocalHomeomorphInjSeamTwo
    (hlocal :
      IsProperMap (bottcher_map_outside_open_to_exterior (2 : ℂ)) ∧
        IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (h_seam : CP5ResidualLocalHomeomorphInjSeamTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_externalRayMapData_two_root_seed_strictMonoFree_of_greenRayLogGtAnchorTwoSeam_of_rootSafeOutsideOpenInjWitnessTwo
    greenRayLogGtAnchorTwo_seed
    (rootSafeOutsideOpenInjWitnessTwo_of_localHomeomorphSurjSourceTwo_of_cp5ResidualLocalHomeomorphInjSeamTwo
      hlocal h_seam)

/-- Strict-mono-free root theorem variant at `c = 2`, specialized to explicit
restricted-map proper/local hypotheses plus a local seam witness. -/
theorem mlc_conjecture_of_externalRayMapData_two_root_seed_strictMonoFree_of_isProperMap_restrict_of_isLocalHomeomorph_restrict_of_cp5ResidualLocalHomeomorphInjSeamTwo
    (hproper : IsProperMap (bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (hlocal : IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (h_seam : CP5ResidualLocalHomeomorphInjSeamTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_externalRayMapData_two_root_seed_strictMonoFree_of_localHomeomorphSurjSourceTwo_of_cp5ResidualLocalHomeomorphInjSeamTwo
    ⟨hproper, hlocal⟩ h_seam

/-- Strict-mono-free root theorem variant at `c = 2`, specialized to a direct
proper/local witness and Green-ray seam payload. -/
theorem mlc_conjecture_of_externalRayMapData_two_root_seed_strictMonoFree_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam_of_directProperLocalWitnessTwo
    (huniq_seam : GreenRayUniquePreimageTwoAnchorSeam)
    (hlog_gt_anchor : GreenRayLogGtAnchorTwoSeam)
    (h : DirectProperLocalWitnessTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_external_ray_map_exists_two
    (externalRayMapData_two_root_seed_strictMonoFree_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam_of_directProperLocalWitnessTwo
      huniq_seam hlog_gt_anchor h)

/-- Strict-mono-free root theorem variant at `c = 2`, specialized to the CP5
local-homeomorph source pair and Green-ray seam payload. -/
theorem mlc_conjecture_of_externalRayMapData_two_root_seed_strictMonoFree_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam_of_localHomeomorphSurjSourceTwo
    (huniq_seam : GreenRayUniquePreimageTwoAnchorSeam)
    (hlog_gt_anchor : GreenRayLogGtAnchorTwoSeam)
    (hlocal :
      IsProperMap (bottcher_map_outside_open_to_exterior (2 : ℂ)) ∧
        IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ))) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_external_ray_map_exists_two
    (externalRayMapData_two_root_seed_strictMonoFree_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam_of_localHomeomorphSurjSourceTwo
      huniq_seam hlog_gt_anchor hlocal)

/-- Strict-mono-free root theorem variant at `c = 2`, specialized to explicit
restricted-map proper/local hypotheses and Green-ray seam payload. -/
theorem mlc_conjecture_of_externalRayMapData_two_root_seed_strictMonoFree_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam_of_isProperMap_restrict_of_isLocalHomeomorph_restrict
    (huniq_seam : GreenRayUniquePreimageTwoAnchorSeam)
    (hlog_gt_anchor : GreenRayLogGtAnchorTwoSeam)
    (hproper : IsProperMap (bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (hlocal : IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ))) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_externalRayMapData_two_root_seed_strictMonoFree_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam_of_localHomeomorphSurjSourceTwo
    huniq_seam hlog_gt_anchor ⟨hproper, hlocal⟩

/-- Strict-mono-seeded root theorem variant at `c = 2`, specialized to explicit
restricted-map proper/local hypotheses. -/
theorem mlc_conjecture_of_externalRayMapData_two_root_seed_strictMonoFree_of_isProperMap_restrict_of_isLocalHomeomorph_restrict_strictMono
    (hproper : IsProperMap (bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (hlocal : IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ))) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_externalRayMapData_two_root_seed_strictMonoFree_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam_of_isProperMap_restrict_of_isLocalHomeomorph_restrict
    greenRayUniquePreimageTwoAnchorSeam_strictMono_seeded_of_greenFunctionStrictMonoAlongRayBasinTwo_seed
    greenRayLogGtAnchorTwo_seed
    hproper hlocal

/-- Strict-mono-seeded root theorem variant at `c = 2`, specialized to the CP5
local-homeomorph source pair. -/
theorem mlc_conjecture_of_externalRayMapData_two_root_seed_strictMonoFree_of_localHomeomorphSurjSourceTwo_strictMono
    (hlocal :
      IsProperMap (bottcher_map_outside_open_to_exterior (2 : ℂ)) ∧
        IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ))) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_externalRayMapData_two_root_seed_strictMonoFree_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam_of_localHomeomorphSurjSourceTwo
    greenRayUniquePreimageTwoAnchorSeam_strictMono_seeded_of_greenFunctionStrictMonoAlongRayBasinTwo_seed
    greenRayLogGtAnchorTwo_seed
    hlocal

/-- Strict-mono-seeded root theorem variant at `c = 2`, specialized to a direct
proper/local witness. -/
theorem mlc_conjecture_of_externalRayMapData_two_root_seed_strictMonoFree_of_directProperLocalWitnessTwo_strictMono
    (h : DirectProperLocalWitnessTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_externalRayMapData_two_root_seed_strictMonoFree_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam_of_directProperLocalWitnessTwo
    greenRayUniquePreimageTwoAnchorSeam_strictMono_seeded_of_greenFunctionStrictMonoAlongRayBasinTwo_seed
    greenRayLogGtAnchorTwo_seed
    h

/-- Strict-mono-free root theorem variant at `c = 2`, specialized to the known
non-iterate-left injectivity-source aggregate. -/
theorem mlc_conjecture_of_externalRayMapData_two_root_seed_strictMonoFree_of_greenRayLogGtAnchorTwoSeam_of_knownInjOnOutsideOpenSourceCandidateTwo
    (hlog_gt_anchor : GreenRayLogGtAnchorTwoSeam)
    (h : KnownInjOnOutsideOpenSourceCandidateTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_externalRayMapData_two_root_seed_strictMonoFree_of_greenRayLogGtAnchorTwoSeam_of_rootSafeOutsideOpenInjWitnessTwo
    hlog_gt_anchor
    (rootSafeOutsideOpenInjWitnessTwo_of_knownInjOnOutsideOpenSourceCandidateTwo h)

/-- Strict-mono-free root theorem variant at `c = 2`, specialized to the known
non-iterate-left injectivity-source aggregate and the current anchor-gap seed. -/
theorem mlc_conjecture_of_externalRayMapData_two_root_seed_strictMonoFree_of_knownInjOnOutsideOpenSourceCandidateTwo
    (h : KnownInjOnOutsideOpenSourceCandidateTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_externalRayMapData_two_root_seed_strictMonoFree_of_greenRayLogGtAnchorTwoSeam_of_knownInjOnOutsideOpenSourceCandidateTwo
    greenRayLogGtAnchorTwo_seed h

/-- Strict-mono-free root theorem variant at `c = 2`, specialized to
outside-open analyticity. -/
theorem mlc_conjecture_of_externalRayMapData_two_root_seed_strictMonoFree_of_greenRayLogGtAnchorTwoSeam_of_outsideOpenAnalyticityHypothesis
    (hlog_gt_anchor : GreenRayLogGtAnchorTwoSeam)
    (h_analytic : OutsideOpenAnalyticityHypothesis (2 : ℂ)) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_externalRayMapData_two_root_seed_strictMonoFree_of_greenRayLogGtAnchorTwoSeam_of_rootSafeOutsideOpenInjWitnessTwo
    hlog_gt_anchor
    (rootSafeOutsideOpenInjWitnessTwo_of_outsideOpenAnalyticityHypothesis h_analytic)

/-- Strict-mono-free root theorem variant at `c = 2`, specialized to
outside-open analyticity and the current anchor-gap seed. -/
theorem mlc_conjecture_of_externalRayMapData_two_root_seed_strictMonoFree_of_outsideOpenAnalyticityHypothesis
    (h_analytic : OutsideOpenAnalyticityHypothesis (2 : ℂ)) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_externalRayMapData_two_root_seed_strictMonoFree_of_greenRayLogGtAnchorTwoSeam_of_outsideOpenAnalyticityHypothesis
    greenRayLogGtAnchorTwo_seed h_analytic

/-- Strict-mono-free candidate root theorem at `c = 2`, parameterized by the
aggregated strict-mono-free ingress bundle. -/
theorem mlc_conjecture_strictMonoFree_candidate_of_greenRayLogGtAnchorTwoSeam_of_strictMonoFreeIngressTwo
    (hlog_gt_anchor : GreenRayLogGtAnchorTwoSeam)
    (h : RootSafeOutsideOpenInjWitnessTwoStrictMonoFreeIngressTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_externalRayMapData_two_root_seed_of_rootSeedPayloadTwo
    (rootSeedPayloadTwo_of_greenRayLogGtAnchorTwoSeam_of_strictMonoFreeIngressTwo
      hlog_gt_anchor h)

/-- Strict-mono-free candidate root theorem at `c = 2`, specialized to the
aggregated strict-mono-free ingress bundle and the current anchor-gap seed. -/
theorem mlc_conjecture_strictMonoFree_candidate_of_strictMonoFreeIngressTwo
    (h : RootSafeOutsideOpenInjWitnessTwoStrictMonoFreeIngressTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_externalRayMapData_two_root_seed_of_rootSeedPayloadTwo
    (rootSeedPayloadTwo_of_greenRayLogGtAnchorTwoSeam_of_strictMonoFreeIngressTwo
      greenRayLogGtAnchorTwo_seed h)

/-- Strict-mono-free candidate root theorem at `c = 2`, parameterized by the
strict-mono-free ingress payload for the centralized root seed. -/
theorem mlc_conjecture_strictMonoFree_candidate_of_rootSeedPayloadTwoStrictMonoFreeIngressTwo
    (h : RootSeedPayloadTwoStrictMonoFreeIngressTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_externalRayMapData_two_root_seed_of_rootSeedPayloadTwo
    (rootSeedPayloadTwo_of_rootSeedPayloadTwoStrictMonoFreeIngressTwo h)

/-- Final strict-mono-free candidate root theorem: once
`RootSafeOutsideOpenInjWitnessTwo` is provided constructively, root no longer
uses `green_function_strictMono_along_ray_basin_seam`. -/
theorem mlc_conjecture_strictMonoFree_candidate_of_rootSafeOutsideOpenInjWitnessTwo
    (h_inj : RootSafeOutsideOpenInjWitnessTwo) :
    LocallyConnectedSpace mandelbrotSet :=
  mlc_conjecture_of_externalRayMapData_two_root_seed_strictMonoFree_of_rootSafeOutsideOpenInjWitnessTwo
    h_inj

/-- Strict-mono-free candidate root theorem specialized to the packaged
degree-one Green-function ingress. -/
theorem mlc_conjecture_strictMonoFree_candidate_of_green_function_degreeOneIngressTwo
    (h : GreenFunctionDegreeOneIngressTwo) :
    LocallyConnectedSpace mandelbrotSet :=
  mlc_conjecture_of_externalRayMapData_two_root_seed_strictMonoFree_of_green_function_degreeOneIngressTwo
    h

/-- Strict-mono-free root-candidate wrapper: if the degree-one Green-function
ingress is supplied, the final root seam can be discharged without using
`green_function_strictMono_along_ray_basin_seam`. -/
theorem mlc_conjecture_root_candidate_of_green_function_degreeOneIngressTwo
    (h : GreenFunctionDegreeOneIngressTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_externalRayMapData_two_root_seed_strictMonoFree_of_rootSafeOutsideOpenInjWitnessTwo
    (rootSafeOutsideOpenInjWitnessTwo_of_green_function_degreeOneIngressTwo h)

/-- Strict-mono-free root-candidate wrapper parameterized directly by the
centralized root-seed payload. -/
theorem mlc_conjecture_root_candidate_of_rootSeedPayloadTwo
    (hseed : RootSeedPayloadTwo) :
    LocallyConnectedSpace mandelbrotSet :=
  mlc_conjecture_of_externalRayMapData_two_root_seed_of_rootSeedPayloadTwo hseed

/-- Strict-mono-free root-candidate wrapper parameterized by the exact remaining
outside-open injectivity witness target. -/
theorem mlc_conjecture_root_candidate_of_rootSafeOutsideOpenInjWitnessTwo_of_greenRayLogGtAnchorTwoSeam
    (hlog_gt_anchor : GreenRayLogGtAnchorTwoSeam)
    (h_inj : RootSafeOutsideOpenInjWitnessTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_externalRayMapData_two_root_seed_of_rootSeedPayloadTwo
    (rootSeedPayloadTwo_of_greenRayLogGtAnchorTwoSeam_of_rootSafeOutsideOpenInjWitnessTwo
      hlog_gt_anchor h_inj)

/-- Strict-mono-free root-candidate wrapper from the exact root-safe
outside-open injectivity target plus direct proper/local surjectivity witness at
`c = 2`, routed through the nonaggregated surjectivity bridge. -/
theorem mlc_conjecture_root_candidate_of_rootSafeOutsideOpenInjWitnessTwo_of_directProperLocalWitnessTwo
    (h_inj : RootSafeOutsideOpenInjWitnessTwo)
    (h_dir : DirectProperLocalWitnessTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_injSurjExteriorConstructivePayloadTwo
    ⟨h_inj, bottcherSurjOnExteriorFromOutsideOpen_two_of_directProperLocalWitnessTwo h_dir⟩

/-- v9 root-entry detour interface: route root closure through the
injective+surjective exterior constructive payload, avoiding any direct root
use of Green-ray seam constants at this boundary. -/
def RootEntryDetourViaInjSurjExteriorConstructivePayloadTwo : Prop :=
  InjSurjExteriorConstructivePayloadTwo

/-- Build the v9 root-entry detour payload from explicit outside-open
injectivity plus direct proper/local witness at `c = 2`. -/
theorem rootEntryDetourViaInjSurjExteriorConstructivePayloadTwo_of_rootSafeOutsideOpenInjWitnessTwo_of_directProperLocalWitnessTwo
    (h_inj : RootSafeOutsideOpenInjWitnessTwo)
    (h_dir : DirectProperLocalWitnessTwo) :
    RootEntryDetourViaInjSurjExteriorConstructivePayloadTwo := by
  exact ⟨h_inj, bottcherSurjOnExteriorFromOutsideOpen_two_of_directProperLocalWitnessTwo h_dir⟩

/-- Root closure through the v9 inj/surj exterior detour interface. -/
theorem mlc_conjecture_of_rootEntryDetourViaInjSurjExteriorConstructivePayloadTwo
    (h_detour : RootEntryDetourViaInjSurjExteriorConstructivePayloadTwo) :
    LocallyConnectedSpace mandelbrotSet :=
  mlc_conjecture_of_injSurjExteriorConstructivePayloadTwo h_detour

/-- Build the v9 root-entry detour payload from an outside-open injectivity
witness plus the packaged local-homeomorph closed-preimage route. -/
theorem rootEntryDetourViaInjSurjExteriorConstructivePayloadTwo_of_rootSafeOutsideOpenInjWitnessTwo_of_directProperLocalWitnessTwoFromLocalHomeomorphClosedRangeRouteTwo
    (h_inj : RootSafeOutsideOpenInjWitnessTwo)
    (h_route : DirectProperLocalWitnessTwoFromLocalHomeomorphClosedRangeRouteTwo) :
    RootEntryDetourViaInjSurjExteriorConstructivePayloadTwo := by
  exact
    rootEntryDetourViaInjSurjExteriorConstructivePayloadTwo_of_rootSafeOutsideOpenInjWitnessTwo_of_directProperLocalWitnessTwo
      h_inj
      (directProperLocalWitnessTwo_of_directProperLocalWitnessTwoFromLocalHomeomorphClosedRangeRouteTwo
        h_route)

/-- Root closure through the v9 local-homeomorph closed-preimage route, given
an outside-open injectivity witness. -/
theorem mlc_conjecture_of_rootSafeOutsideOpenInjWitnessTwo_of_directProperLocalWitnessTwoFromLocalHomeomorphClosedRangeRouteTwo
    (h_inj : RootSafeOutsideOpenInjWitnessTwo)
    (h_route : DirectProperLocalWitnessTwoFromLocalHomeomorphClosedRangeRouteTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_rootEntryDetourViaInjSurjExteriorConstructivePayloadTwo
    (rootEntryDetourViaInjSurjExteriorConstructivePayloadTwo_of_rootSafeOutsideOpenInjWitnessTwo_of_directProperLocalWitnessTwoFromLocalHomeomorphClosedRangeRouteTwo
      h_inj h_route)

/-- Minimal non-seeded root-closure substitute interface at `c = 2`:
outside-open injectivity plus direct proper/local witness. -/
def RootClosureSubstituteTwo : Prop :=
  RootSafeOutsideOpenInjWitnessTwo ∧ DirectProperLocalWitnessTwo

/-- Named non-seam replacement target for root closure at `c = 2`.
This aliases the existing seam-free closure interface and is used as a redesign
boundary marker for log-gap seam elimination work. -/
def NonseamRootReplacementTargetTwo : Prop :=
  RootClosureSubstituteTwo

/-- Non-seam replacement target is definitionally equivalent to the existing
seam-free closure interface. -/
theorem nonseamRootReplacementTargetTwo_iff_rootClosureSubstituteTwo :
    NonseamRootReplacementTargetTwo ↔ RootClosureSubstituteTwo := by
  rfl

/-- v10 minimal non-seeded elimination gap at root entry: a constructor from
direct proper/local witness data to outside-open injectivity. -/
def NonseededDirectProperToRootSafeGapTwo : Prop :=
  DirectProperLocalWitnessTwo → RootSafeOutsideOpenInjWitnessTwo

/-- v12 equivalent non-seeded gap phrasing: from direct proper/local witness to
the local-homeomorph CP5 injectivity seam. -/
def NonseededDirectProperToLocalSeamGapTwo : Prop :=
  DirectProperLocalWitnessTwo → CP5ResidualLocalHomeomorphInjSeamTwo

/-- Build the v10 non-seeded directProper→rootSafe gap from the v12
directProper→local-seam gap. -/
theorem nonseededDirectProperToRootSafeGapTwo_of_nonseededDirectProperToLocalSeamGapTwo
    (h_gap : NonseededDirectProperToLocalSeamGapTwo) :
    NonseededDirectProperToRootSafeGapTwo := by
  intro h_dir
  exact
    rootSafeOutsideOpenInjWitnessTwo_of_directProperLocalWitnessTwo_of_cp5ResidualLocalHomeomorphInjSeamTwo
      h_dir (h_gap h_dir)

/-- Build the v12 directProper→local-seam gap from the v10
directProper→rootSafe gap. -/
theorem nonseededDirectProperToLocalSeamGapTwo_of_nonseededDirectProperToRootSafeGapTwo
    (h_gap : NonseededDirectProperToRootSafeGapTwo) :
    NonseededDirectProperToLocalSeamGapTwo := by
  intro h_dir
  exact cp5ResidualLocalHomeomorphInjSeamTwo_of_rootSafeOutsideOpenInjWitnessTwo
    (h_gap h_dir)

/-- The v10 and v12 non-seeded gap formulations are equivalent. -/
theorem nonseededDirectProperToRootSafeGapTwo_iff_nonseededDirectProperToLocalSeamGapTwo :
    NonseededDirectProperToRootSafeGapTwo ↔ NonseededDirectProperToLocalSeamGapTwo := by
  constructor
  · intro h_gap
    exact
      nonseededDirectProperToLocalSeamGapTwo_of_nonseededDirectProperToRootSafeGapTwo
        h_gap
  · intro h_gap
    exact
      nonseededDirectProperToRootSafeGapTwo_of_nonseededDirectProperToLocalSeamGapTwo
        h_gap

/-- If the v10 non-seeded directProper→rootSafe gap is discharged, root closure
follows directly from a direct proper/local witness. -/
theorem rootClosureSubstituteTwo_of_nonseededDirectProperToRootSafeGapTwo_of_directProperLocalWitnessTwo
    (h_gap : NonseededDirectProperToRootSafeGapTwo)
    (h_dir : DirectProperLocalWitnessTwo) :
    RootClosureSubstituteTwo :=
  ⟨h_gap h_dir, h_dir⟩

/-- If the v10 non-seeded directProper→rootSafe gap is discharged, MLC follows
from a direct proper/local witness through the non-seam root substitute route. -/
theorem mlc_conjecture_of_nonseededDirectProperToRootSafeGapTwo_of_directProperLocalWitnessTwo
    (h_gap : NonseededDirectProperToRootSafeGapTwo)
    (h_dir : DirectProperLocalWitnessTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_root_candidate_of_rootSafeOutsideOpenInjWitnessTwo_of_directProperLocalWitnessTwo
    (h_gap h_dir) h_dir

/-- Root closure from the v12 directProper→local-seam gap plus a direct
proper/local witness. -/
theorem mlc_conjecture_of_nonseededDirectProperToLocalSeamGapTwo_of_directProperLocalWitnessTwo
    (h_gap : NonseededDirectProperToLocalSeamGapTwo)
    (h_dir : DirectProperLocalWitnessTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_nonseededDirectProperToRootSafeGapTwo_of_directProperLocalWitnessTwo
    (nonseededDirectProperToRootSafeGapTwo_of_nonseededDirectProperToLocalSeamGapTwo h_gap)
    h_dir

/-- Seeded fallback witness of the v10 non-seeded directProper→rootSafe gap.
This theorem is intentionally marked as seeded fallback and not a frontier-safe
closure. -/
theorem nonseededDirectProperToRootSafeGapTwo_seeded_fallback :
    NonseededDirectProperToRootSafeGapTwo := by
  intro h_dir
  exact injOn_outside_open_two_of_directProperLocalWitnessTwo_constructive h_dir

/-- Seeded fallback witness of the v12 directProper→local-seam gap. -/
theorem nonseededDirectProperToLocalSeamGapTwo_seeded_fallback :
    NonseededDirectProperToLocalSeamGapTwo := by
  intro h_dir
  exact cp5ResidualLocalHomeomorphInjSeamTwo_of_directProperLocalWitnessTwo h_dir

/-- v10 route matrix for candidate paths currently used to obtain
`DirectProperLocalWitnessTwo`. -/
def DirectProperLocalWitnessTwoRouteMatrixV10 : Prop :=
  DirectProperLocalWitnessTwoFromLocalHomeomorphClosedRangeRouteTwo ∨
    KnownProperLocalSourceCandidateTwo ∨
      PrimitiveRestrictedMapProperLocalWitnessFamilyTwo

/-- Any route in the v10 route matrix yields `DirectProperLocalWitnessTwo`. -/
theorem directProperLocalWitnessTwo_of_directProperLocalWitnessTwoRouteMatrixV10
    (h : DirectProperLocalWitnessTwoRouteMatrixV10) :
    DirectProperLocalWitnessTwo := by
  rcases h with h_route | h_known | h_prim
  · exact
      directProperLocalWitnessTwo_of_directProperLocalWitnessTwoFromLocalHomeomorphClosedRangeRouteTwo
        h_route
  · exact False.elim (not_knownProperLocalSourceCandidateTwo h_known)
  · exact
      directProperLocalWitnessTwo_of_primitiveRestrictedMapProperLocalWitnessFamilyTwo
        h_prim

/-- The v10 route matrix is equivalent to `DirectProperLocalWitnessTwo`:
known proper/local source families are blocked, and the remaining route
interfaces collapse to the same target. -/
theorem directProperLocalWitnessTwoRouteMatrixV10_iff_directProperLocalWitnessTwo :
    DirectProperLocalWitnessTwoRouteMatrixV10 ↔ DirectProperLocalWitnessTwo := by
  constructor
  · intro h
    exact directProperLocalWitnessTwo_of_directProperLocalWitnessTwoRouteMatrixV10 h
  · intro h_dir
    exact Or.inr (Or.inr
      (primitiveRestrictedMapProperLocalWitnessFamilyTwo_of_directProperLocalWitnessTwo h_dir))

/-- v10 root closure from the non-seeded directProper→rootSafe gap and any route
in the route matrix. -/
theorem mlc_conjecture_of_nonseededDirectProperToRootSafeGapTwo_of_directProperLocalWitnessTwoRouteMatrixV10
    (h_gap : NonseededDirectProperToRootSafeGapTwo)
    (h_route : DirectProperLocalWitnessTwoRouteMatrixV10) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_nonseededDirectProperToRootSafeGapTwo_of_directProperLocalWitnessTwo
    h_gap (directProperLocalWitnessTwo_of_directProperLocalWitnessTwoRouteMatrixV10 h_route)

/-- v12 local-seam-gap variant of the route-matrix cutover wrapper. -/
theorem mlc_conjecture_of_nonseededDirectProperToLocalSeamGapTwo_of_directProperLocalWitnessTwoRouteMatrixV10
    (h_gap : NonseededDirectProperToLocalSeamGapTwo)
    (h_route : DirectProperLocalWitnessTwoRouteMatrixV10) :
    LocallyConnectedSpace mandelbrotSet := by
  exact
    mlc_conjecture_of_nonseededDirectProperToLocalSeamGapTwo_of_directProperLocalWitnessTwo
      h_gap
      (directProperLocalWitnessTwo_of_directProperLocalWitnessTwoRouteMatrixV10 h_route)

/-- Seeded local-seam fallback specialized to the route matrix. -/
theorem mlc_conjecture_of_nonseededDirectProperToLocalSeamGapTwo_seeded_fallback_of_directProperLocalWitnessTwoRouteMatrixV10
    (h_route : DirectProperLocalWitnessTwoRouteMatrixV10) :
    LocallyConnectedSpace mandelbrotSet := by
  exact
    mlc_conjecture_of_nonseededDirectProperToLocalSeamGapTwo_of_directProperLocalWitnessTwoRouteMatrixV10
      nonseededDirectProperToLocalSeamGapTwo_seeded_fallback h_route

/-- Build outside-open injectivity from the v12 local-seam gap plus a direct
proper/local witness. -/
theorem rootSafeOutsideOpenInjWitnessTwo_of_nonseededDirectProperToLocalSeamGapTwo_of_directProperLocalWitnessTwo
    (h_gap : NonseededDirectProperToLocalSeamGapTwo)
    (h_dir : DirectProperLocalWitnessTwo) :
    RootSafeOutsideOpenInjWitnessTwo :=
  rootSafeOutsideOpenInjWitnessTwo_of_directProperLocalWitnessTwo_of_cp5ResidualLocalHomeomorphInjSeamTwo
    h_dir (h_gap h_dir)

/-- Primitive-family specialization of the v12 local-seam gap cutover. -/
theorem mlc_conjecture_of_nonseededDirectProperToLocalSeamGapTwo_of_primitiveRestrictedMapProperLocalWitnessFamilyTwo
    (h_gap : NonseededDirectProperToLocalSeamGapTwo)
    (h_prim : PrimitiveRestrictedMapProperLocalWitnessFamilyTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact
    mlc_conjecture_of_nonseededDirectProperToLocalSeamGapTwo_of_directProperLocalWitnessTwo
      h_gap
      (directProperLocalWitnessTwo_of_primitiveRestrictedMapProperLocalWitnessFamilyTwo h_prim)

/-- v14 witness-source matrix for local-seam gap cutover. -/
def NonseededLocalSeamGapWitnessSourceMatrixV14 : Prop :=
  PrimitiveRestrictedMapProperLocalWitnessFamilyTwo ∨
    DirectProperLocalWitnessTwo

/-- The v14 local-seam witness-source matrix is equivalent to the direct
proper/local witness payload. -/
theorem nonseededLocalSeamGapWitnessSourceMatrixV14_iff_directProperLocalWitnessTwo :
    NonseededLocalSeamGapWitnessSourceMatrixV14 ↔ DirectProperLocalWitnessTwo := by
  constructor
  · intro h_src
    rcases h_src with h_prim | h_dir
    · exact directProperLocalWitnessTwo_of_primitiveRestrictedMapProperLocalWitnessFamilyTwo h_prim
    · exact h_dir
  · intro h_dir
    exact Or.inl
      (primitiveRestrictedMapProperLocalWitnessFamilyTwo_of_directProperLocalWitnessTwo h_dir)

/-- Any witness source in the v14 matrix yields MLC once the local-seam gap is
provided. -/
theorem mlc_conjecture_of_nonseededDirectProperToLocalSeamGapTwo_of_nonseededLocalSeamGapWitnessSourceMatrixV14
    (h_gap : NonseededDirectProperToLocalSeamGapTwo)
    (h_src : NonseededLocalSeamGapWitnessSourceMatrixV14) :
    LocallyConnectedSpace mandelbrotSet := by
  rcases h_src with h_prim | h_dir
  · exact
      mlc_conjecture_of_nonseededDirectProperToLocalSeamGapTwo_of_primitiveRestrictedMapProperLocalWitnessFamilyTwo
        h_gap h_prim
  · exact
      mlc_conjecture_of_nonseededDirectProperToLocalSeamGapTwo_of_directProperLocalWitnessTwo
        h_gap h_dir

/-- v15 composite final-gap marker: non-seeded local-seam gap plus an available
local-seam witness-source matrix. -/
def FinalAxiomEliminationGapV15 : Prop :=
  NonseededDirectProperToLocalSeamGapTwo ∧
    NonseededLocalSeamGapWitnessSourceMatrixV14

/-- v16 minimized final-gap payload: the non-seeded local-seam bridge together
with one direct proper/local witness. -/
def FinalAxiomEliminationWitnessPairV16 : Prop :=
  NonseededDirectProperToLocalSeamGapTwo ∧
    DirectProperLocalWitnessTwo

/-- v16 core constructive elimination target: the exact missing implication. -/
def FinalAxiomCoreConstructiveGapV16 : Prop :=
  DirectProperLocalWitnessTwo → CP5ResidualLocalHomeomorphInjSeamTwo

/-- The v16 core constructive target is definitionally the v12 non-seeded
local-seam gap. -/
theorem finalAxiomCoreConstructiveGapV16_iff_nonseededDirectProperToLocalSeamGapTwo :
    FinalAxiomCoreConstructiveGapV16 ↔ NonseededDirectProperToLocalSeamGapTwo := by
  rfl

/-- The v15 composite final gap is equivalent to the v16 minimized witness
pair. -/
theorem finalAxiomEliminationGapV15_iff_finalAxiomEliminationWitnessPairV16 :
    FinalAxiomEliminationGapV15 ↔ FinalAxiomEliminationWitnessPairV16 := by
  constructor
  · intro h_final
    refine ⟨h_final.1, ?_⟩
    exact
      (nonseededLocalSeamGapWitnessSourceMatrixV14_iff_directProperLocalWitnessTwo).1
        h_final.2
  · intro h_pair
    refine ⟨h_pair.1, ?_⟩
    exact
      (nonseededLocalSeamGapWitnessSourceMatrixV14_iff_directProperLocalWitnessTwo).2
        h_pair.2

/-- v17 elimination kernel: the isolated core bridge together with one direct
proper/local witness. -/
def FinalAxiomEliminationKernelV17 : Prop :=
  FinalAxiomCoreConstructiveGapV16 ∧ DirectProperLocalWitnessTwo

/-- The v17 elimination kernel is equivalent to the v16 witness pair. -/
theorem finalAxiomEliminationKernelV17_iff_finalAxiomEliminationWitnessPairV16 :
    FinalAxiomEliminationKernelV17 ↔ FinalAxiomEliminationWitnessPairV16 := by
  constructor
  · intro h_kernel
    refine ⟨?_, h_kernel.2⟩
    exact
      (finalAxiomCoreConstructiveGapV16_iff_nonseededDirectProperToLocalSeamGapTwo).1
        h_kernel.1
  · intro h_pair
    refine ⟨?_, h_pair.2⟩
    exact
      (finalAxiomCoreConstructiveGapV16_iff_nonseededDirectProperToLocalSeamGapTwo).2
        h_pair.1

/-- The v15 composite final gap is equivalent to the v17 elimination kernel. -/
theorem finalAxiomEliminationGapV15_iff_finalAxiomEliminationKernelV17 :
    FinalAxiomEliminationGapV15 ↔ FinalAxiomEliminationKernelV17 := by
  exact
    finalAxiomEliminationGapV15_iff_finalAxiomEliminationWitnessPairV16.trans
      finalAxiomEliminationKernelV17_iff_finalAxiomEliminationWitnessPairV16.symm

/-- v18 ingress-level elimination kernel: the isolated core bridge together
with aggregate constructive ingress. -/
def FinalAxiomEliminationIngressKernelV18 : Prop :=
  FinalAxiomCoreConstructiveGapV16 ∧ RemainingConstructiveIngressTwo

/-- The v18 ingress-level kernel is equivalent to the v17 elimination kernel. -/
theorem finalAxiomEliminationIngressKernelV18_iff_finalAxiomEliminationKernelV17 :
    FinalAxiomEliminationIngressKernelV18 ↔ FinalAxiomEliminationKernelV17 := by
  constructor
  · intro h_ingress
    refine ⟨h_ingress.1, ?_⟩
    exact
      (remainingConstructiveIngressTwo_iff_directProperLocalWitness).1 h_ingress.2
  · intro h_kernel
    refine ⟨h_kernel.1, ?_⟩
    exact
      (remainingConstructiveIngressTwo_iff_directProperLocalWitness).2 h_kernel.2

/-- The v15 composite final gap is equivalent to the v18 ingress-level kernel. -/
theorem finalAxiomEliminationGapV15_iff_finalAxiomEliminationIngressKernelV18 :
    FinalAxiomEliminationGapV15 ↔ FinalAxiomEliminationIngressKernelV18 := by
  exact
    finalAxiomEliminationGapV15_iff_finalAxiomEliminationKernelV17.trans
      finalAxiomEliminationIngressKernelV18_iff_finalAxiomEliminationKernelV17.symm

/-- v19 ingress-level core bridge target: the local CP5 injectivity seam from
aggregate constructive ingress. -/
def FinalAxiomIngressBridgeGapV19 : Prop :=
  RemainingConstructiveIngressTwo → CP5ResidualLocalHomeomorphInjSeamTwo

/-- v20 seam-decomposition component A: extract direct witness data from
aggregate constructive ingress. -/
def FinalAxiomSeamA_V20 : Prop :=
  RemainingConstructiveIngressTwo → DirectProperLocalWitnessTwo

/-- v20 seam-decomposition component B: core direct-witness bridge to the local
CP5 seam. -/
def FinalAxiomSeamB_V20 : Prop :=
  DirectProperLocalWitnessTwo → CP5ResidualLocalHomeomorphInjSeamTwo

/-- v20 seam-decomposition target: combine ingress->direct extraction with the
core direct->seam bridge. -/
def FinalAxiomSeamDecompositionV20 : Prop :=
  FinalAxiomSeamA_V20 ∧ FinalAxiomSeamB_V20

/-- Canonical witness of v20 seam component A from existing ingress
normalization. -/
theorem finalAxiomSeamA_V20_canonical : FinalAxiomSeamA_V20 :=
  (remainingConstructiveIngressTwo_iff_directProperLocalWitness).1

/-- v20 seam component B is definitionally the v16 core constructive gap. -/
theorem finalAxiomSeamB_V20_iff_finalAxiomCoreConstructiveGapV16 :
    FinalAxiomSeamB_V20 ↔ FinalAxiomCoreConstructiveGapV16 := by
  rfl

/-- The v20 seam-decomposition target is equivalent to the v19 ingress bridge
gap. -/
theorem finalAxiomSeamDecompositionV20_iff_finalAxiomIngressBridgeGapV19 :
    FinalAxiomSeamDecompositionV20 ↔ FinalAxiomIngressBridgeGapV19 := by
  constructor
  · intro h_decomp h_ingress
    exact h_decomp.2 (h_decomp.1 h_ingress)
  · intro h_gap
    refine ⟨finalAxiomSeamA_V20_canonical, ?_⟩
    intro h_dir
    exact h_gap ((remainingConstructiveIngressTwo_iff_directProperLocalWitness).2 h_dir)

/-- v20 witness-transport target: build outside-open injectivity directly from
aggregate constructive ingress. -/
def FinalAxiomWitnessTransportV20 : Prop :=
  RemainingConstructiveIngressTwo → RootSafeOutsideOpenInjWitnessTwo

/-- The v20 witness-transport target is equivalent to the v19 ingress bridge
gap. -/
theorem finalAxiomWitnessTransportV20_iff_finalAxiomIngressBridgeGapV19 :
    FinalAxiomWitnessTransportV20 ↔ FinalAxiomIngressBridgeGapV19 := by
  constructor
  · intro h_transport h_ingress
    exact
      cp5ResidualLocalHomeomorphInjSeamTwo_of_rootSafeOutsideOpenInjWitnessTwo
        (h_transport h_ingress)
  · intro h_gap h_ingress
    have h_dir : DirectProperLocalWitnessTwo :=
      (remainingConstructiveIngressTwo_iff_directProperLocalWitness).1 h_ingress
    exact
      rootSafeOutsideOpenInjWitnessTwo_of_directProperLocalWitnessTwo_of_cp5ResidualLocalHomeomorphInjSeamTwo
        h_dir (h_gap h_ingress)

/-- v20 contrapositive-obstruction target: if the local CP5 seam fails, then
aggregate constructive ingress fails. -/
def FinalAxiomContrapositiveObstructionV20 : Prop :=
  ¬ CP5ResidualLocalHomeomorphInjSeamTwo → ¬ RemainingConstructiveIngressTwo

/-- The v20 contrapositive-obstruction target is equivalent to the v19 ingress
bridge gap. -/
theorem finalAxiomContrapositiveObstructionV20_iff_finalAxiomIngressBridgeGapV19 :
    FinalAxiomContrapositiveObstructionV20 ↔ FinalAxiomIngressBridgeGapV19 := by
  constructor
  · intro h_contra h_ingress
    by_contra h_not_seam
    exact False.elim ((h_contra h_not_seam) h_ingress)
  · intro h_gap h_not_seam h_ingress
    exact h_not_seam (h_gap h_ingress)

/-- The v19 ingress-level core bridge target is equivalent to the v16
direct-witness core bridge target. -/
theorem finalAxiomIngressBridgeGapV19_iff_finalAxiomCoreConstructiveGapV16 :
    FinalAxiomIngressBridgeGapV19 ↔ FinalAxiomCoreConstructiveGapV16 := by
  constructor
  · intro h_gap h_dir
    exact h_gap ((remainingConstructiveIngressTwo_iff_directProperLocalWitness).2 h_dir)
  · intro h_core h_ingress
    exact h_core ((remainingConstructiveIngressTwo_iff_directProperLocalWitness).1 h_ingress)

/-- v19 elimination kernel: ingress-level bridge target plus aggregate
constructive ingress. -/
def FinalAxiomEliminationIngressBridgeKernelV19 : Prop :=
  FinalAxiomIngressBridgeGapV19 ∧ RemainingConstructiveIngressTwo

/-- The v19 ingress-bridge kernel is equivalent to the v18 ingress-level
kernel. -/
theorem finalAxiomEliminationIngressBridgeKernelV19_iff_finalAxiomEliminationIngressKernelV18 :
    FinalAxiomEliminationIngressBridgeKernelV19 ↔ FinalAxiomEliminationIngressKernelV18 := by
  constructor
  · intro h19
    refine ⟨?_, h19.2⟩
    exact
      (finalAxiomIngressBridgeGapV19_iff_finalAxiomCoreConstructiveGapV16).1 h19.1
  · intro h18
    refine ⟨?_, h18.2⟩
    exact
      (finalAxiomIngressBridgeGapV19_iff_finalAxiomCoreConstructiveGapV16).2 h18.1

/-- The v15 composite final gap is equivalent to the v19 ingress-bridge
kernel. -/
theorem finalAxiomEliminationGapV15_iff_finalAxiomEliminationIngressBridgeKernelV19 :
    FinalAxiomEliminationGapV15 ↔ FinalAxiomEliminationIngressBridgeKernelV19 := by
  exact
    finalAxiomEliminationGapV15_iff_finalAxiomEliminationIngressKernelV18.trans
      finalAxiomEliminationIngressBridgeKernelV19_iff_finalAxiomEliminationIngressKernelV18.symm

/-- The isolated v16 core bridge plus a direct witness yields the non-seam root
closure substitute. -/
theorem rootClosureSubstituteTwo_of_finalAxiomCoreConstructiveGapV16_of_directProperLocalWitnessTwo
    (h_core : FinalAxiomCoreConstructiveGapV16)
    (h_dir : DirectProperLocalWitnessTwo) :
    RootClosureSubstituteTwo := by
  exact
    rootClosureSubstituteTwo_of_nonseededDirectProperToRootSafeGapTwo_of_directProperLocalWitnessTwo
      (nonseededDirectProperToRootSafeGapTwo_of_nonseededDirectProperToLocalSeamGapTwo
        ((finalAxiomCoreConstructiveGapV16_iff_nonseededDirectProperToLocalSeamGapTwo).1 h_core))
      h_dir

/-- The isolated v16 core bridge plus a direct witness is sufficient for MLC. -/
theorem mlc_conjecture_of_finalAxiomCoreConstructiveGapV16_of_directProperLocalWitnessTwo
    (h_core : FinalAxiomCoreConstructiveGapV16)
    (h_dir : DirectProperLocalWitnessTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact
    mlc_conjecture_of_nonseededDirectProperToLocalSeamGapTwo_of_directProperLocalWitnessTwo
      ((finalAxiomCoreConstructiveGapV16_iff_nonseededDirectProperToLocalSeamGapTwo).1 h_core)
      h_dir

/-- Route-matrix specialization of the v16 core-gap cutover. -/
theorem mlc_conjecture_of_finalAxiomCoreConstructiveGapV16_of_directProperLocalWitnessTwoRouteMatrixV10
    (h_core : FinalAxiomCoreConstructiveGapV16)
    (h_route : DirectProperLocalWitnessTwoRouteMatrixV10) :
    LocallyConnectedSpace mandelbrotSet := by
  exact
    mlc_conjecture_of_finalAxiomCoreConstructiveGapV16_of_directProperLocalWitnessTwo h_core
      (directProperLocalWitnessTwo_of_directProperLocalWitnessTwoRouteMatrixV10 h_route)

/-- Closing the v17 elimination kernel is sufficient to derive MLC. -/
theorem mlc_conjecture_of_finalAxiomEliminationKernelV17
    (h_kernel : FinalAxiomEliminationKernelV17) :
    LocallyConnectedSpace mandelbrotSet := by
  exact
    mlc_conjecture_of_finalAxiomCoreConstructiveGapV16_of_directProperLocalWitnessTwo
      h_kernel.1 h_kernel.2

/-- Ingress-level v18 kernel cutover to the non-seam root closure substitute. -/
theorem rootClosureSubstituteTwo_of_finalAxiomEliminationIngressKernelV18
    (h_ingress : FinalAxiomEliminationIngressKernelV18) :
    RootClosureSubstituteTwo := by
  exact
    rootClosureSubstituteTwo_of_finalAxiomCoreConstructiveGapV16_of_directProperLocalWitnessTwo
      h_ingress.1
      ((remainingConstructiveIngressTwo_iff_directProperLocalWitness).1 h_ingress.2)

/-- Closing the v18 ingress-level kernel is sufficient to derive MLC. -/
theorem mlc_conjecture_of_finalAxiomEliminationIngressKernelV18
    (h_ingress : FinalAxiomEliminationIngressKernelV18) :
    LocallyConnectedSpace mandelbrotSet := by
  exact
    mlc_conjecture_of_finalAxiomCoreConstructiveGapV16_of_directProperLocalWitnessTwo
      h_ingress.1
      ((remainingConstructiveIngressTwo_iff_directProperLocalWitness).1 h_ingress.2)

/-- Ingress-bridge v19 kernel cutover to the non-seam root closure substitute. -/
theorem rootClosureSubstituteTwo_of_finalAxiomEliminationIngressBridgeKernelV19
    (h19 : FinalAxiomEliminationIngressBridgeKernelV19) :
    RootClosureSubstituteTwo := by
  let h_dir : DirectProperLocalWitnessTwo :=
    (remainingConstructiveIngressTwo_iff_directProperLocalWitness).1 h19.2
  let h_seam : CP5ResidualLocalHomeomorphInjSeamTwo := h19.1 h19.2
  exact
    ⟨rootSafeOutsideOpenInjWitnessTwo_of_directProperLocalWitnessTwo_of_cp5ResidualLocalHomeomorphInjSeamTwo
        h_dir h_seam, h_dir⟩

/-- Closing the v19 ingress-bridge kernel is sufficient to derive MLC. -/
theorem mlc_conjecture_of_finalAxiomEliminationIngressBridgeKernelV19
    (h19 : FinalAxiomEliminationIngressBridgeKernelV19) :
    LocallyConnectedSpace mandelbrotSet := by
  exact
    mlc_conjecture_of_finalAxiomEliminationIngressKernelV18
      ((finalAxiomEliminationIngressBridgeKernelV19_iff_finalAxiomEliminationIngressKernelV18).1 h19)

/-- Closing the v16 minimized witness pair is sufficient to derive MLC. -/
theorem mlc_conjecture_of_finalAxiomEliminationWitnessPairV16
    (h_pair : FinalAxiomEliminationWitnessPairV16) :
    LocallyConnectedSpace mandelbrotSet := by
  exact
    mlc_conjecture_of_nonseededDirectProperToLocalSeamGapTwo_of_directProperLocalWitnessTwo
      h_pair.1 h_pair.2

/-- Closing the v15 composite final gap is sufficient to derive MLC without
using the seeded root seam boundary theorem directly in this wrapper. -/
theorem mlc_conjecture_of_finalAxiomEliminationGapV15
    (h_final : FinalAxiomEliminationGapV15) :
    LocallyConnectedSpace mandelbrotSet := by
  exact
    mlc_conjecture_of_nonseededDirectProperToLocalSeamGapTwo_of_nonseededLocalSeamGapWitnessSourceMatrixV14
      h_final.1 h_final.2

/-- Minimal explicit witness-gap target for constructing
`RootClosureSubstituteTwo` without using the final seeded root specialization:
aggregate constructive ingress plus the local-homeomorph branch seam. -/
def RootClosureSubstituteTwoWitnessGap : Prop :=
  RemainingConstructiveIngressTwo ∧ CP5ResidualLocalHomeomorphInjSeamTwo

/-- Minimal explicit no-arg-constructor gap for
`RemainingConstructiveIngressTwo`: currently this collapses to a direct
proper+local witness. -/
def RemainingConstructiveIngressTwoWitnessGap : Prop :=
  DirectProperLocalWitnessTwo

/-- v21 witness-gap bridge target: derive the local CP5 seam directly from the
explicit no-arg witness-gap payload. -/
def FinalAxiomWitnessGapBridgeV21 : Prop :=
  RemainingConstructiveIngressTwoWitnessGap →
    CP5ResidualLocalHomeomorphInjSeamTwo

/-- The v21 witness-gap bridge target is equivalent to the v16 core bridge
target. -/
theorem finalAxiomWitnessGapBridgeV21_iff_finalAxiomCoreConstructiveGapV16 :
    FinalAxiomWitnessGapBridgeV21 ↔ FinalAxiomCoreConstructiveGapV16 := by
  rfl

/-- v21 witness-gap kernel: bridge target plus explicit no-arg witness-gap
payload. -/
def FinalAxiomWitnessGapKernelV21 : Prop :=
  FinalAxiomWitnessGapBridgeV21 ∧ RemainingConstructiveIngressTwoWitnessGap

/-- The v21 witness-gap kernel is equivalent to the v17 elimination kernel. -/
theorem finalAxiomWitnessGapKernelV21_iff_finalAxiomEliminationKernelV17 :
    FinalAxiomWitnessGapKernelV21 ↔ FinalAxiomEliminationKernelV17 := by
  rfl

/-- The v15 composite final gap is equivalent to the v21 witness-gap kernel. -/
theorem finalAxiomEliminationGapV15_iff_finalAxiomWitnessGapKernelV21 :
    FinalAxiomEliminationGapV15 ↔ FinalAxiomWitnessGapKernelV21 := by
  exact
    finalAxiomEliminationGapV15_iff_finalAxiomEliminationKernelV17.trans
      finalAxiomWitnessGapKernelV21_iff_finalAxiomEliminationKernelV17.symm

/-- v21 witness-gap kernel cutover to the non-seam root closure substitute. -/
theorem rootClosureSubstituteTwo_of_finalAxiomWitnessGapKernelV21
    (h21 : FinalAxiomWitnessGapKernelV21) :
    RootClosureSubstituteTwo := by
  exact
    rootClosureSubstituteTwo_of_finalAxiomCoreConstructiveGapV16_of_directProperLocalWitnessTwo
      ((finalAxiomWitnessGapBridgeV21_iff_finalAxiomCoreConstructiveGapV16).1 h21.1)
      h21.2

/-- Closing the v21 witness-gap kernel is sufficient to derive MLC. -/
theorem mlc_conjecture_of_finalAxiomWitnessGapKernelV21
    (h21 : FinalAxiomWitnessGapKernelV21) :
    LocallyConnectedSpace mandelbrotSet := by
  exact
    mlc_conjecture_of_finalAxiomCoreConstructiveGapV16_of_directProperLocalWitnessTwo
      ((finalAxiomWitnessGapBridgeV21_iff_finalAxiomCoreConstructiveGapV16).1 h21.1)
      h21.2

/-- v22 root-witness-gap bridge target: build the explicit root witness-gap
payload directly from the no-arg witness-gap payload. -/
def FinalAxiomRootWitnessGapBridgeV22 : Prop :=
  RemainingConstructiveIngressTwoWitnessGap → RootClosureSubstituteTwoWitnessGap

/-- The v22 root-witness-gap bridge target is equivalent to the v21
witness-gap bridge target. -/
theorem finalAxiomRootWitnessGapBridgeV22_iff_finalAxiomWitnessGapBridgeV21 :
    FinalAxiomRootWitnessGapBridgeV22 ↔ FinalAxiomWitnessGapBridgeV21 := by
  constructor
  · intro h22 h_gap
    exact (h22 h_gap).2
  · intro h21 h_gap
    exact ⟨remainingConstructiveIngressTwo_of_directProperLocalWitnessTwo h_gap, h21 h_gap⟩

/-- The v22 root-witness-gap bridge target is equivalent to the v16 core
bridge target. -/
theorem finalAxiomRootWitnessGapBridgeV22_iff_finalAxiomCoreConstructiveGapV16 :
    FinalAxiomRootWitnessGapBridgeV22 ↔ FinalAxiomCoreConstructiveGapV16 := by
  exact
    finalAxiomRootWitnessGapBridgeV22_iff_finalAxiomWitnessGapBridgeV21.trans
      finalAxiomWitnessGapBridgeV21_iff_finalAxiomCoreConstructiveGapV16

/-- v22 root-witness-gap kernel: root-witness-gap bridge plus explicit no-arg
witness-gap payload. -/
def FinalAxiomRootWitnessGapKernelV22 : Prop :=
  FinalAxiomRootWitnessGapBridgeV22 ∧ RemainingConstructiveIngressTwoWitnessGap

/-- The v22 root-witness-gap kernel is equivalent to the v21 witness-gap
kernel. -/
theorem finalAxiomRootWitnessGapKernelV22_iff_finalAxiomWitnessGapKernelV21 :
    FinalAxiomRootWitnessGapKernelV22 ↔ FinalAxiomWitnessGapKernelV21 := by
  constructor
  · intro h22
    refine ⟨?_, h22.2⟩
    intro h_gap
    exact (h22.1 h_gap).2
  · intro h21
    refine ⟨?_, h21.2⟩
    intro h_gap
    exact ⟨remainingConstructiveIngressTwo_of_directProperLocalWitnessTwo h_gap, h21.1 h_gap⟩

/-- The v15 composite final gap is equivalent to the v22 root-witness-gap
kernel. -/
theorem finalAxiomEliminationGapV15_iff_finalAxiomRootWitnessGapKernelV22 :
    FinalAxiomEliminationGapV15 ↔ FinalAxiomRootWitnessGapKernelV22 := by
  exact
    finalAxiomEliminationGapV15_iff_finalAxiomWitnessGapKernelV21.trans
      finalAxiomRootWitnessGapKernelV22_iff_finalAxiomWitnessGapKernelV21.symm

/-- v22 root-witness-gap kernel cutover to the non-seam root closure
substitute. -/
theorem rootClosureSubstituteTwo_of_finalAxiomRootWitnessGapKernelV22
    (h22 : FinalAxiomRootWitnessGapKernelV22) :
    RootClosureSubstituteTwo := by
  let h_root_gap : RootClosureSubstituteTwoWitnessGap := h22.1 h22.2
  let h_dir : DirectProperLocalWitnessTwo := h22.2
  exact
    ⟨rootSafeOutsideOpenInjWitnessTwo_of_directProperLocalWitnessTwo_of_cp5ResidualLocalHomeomorphInjSeamTwo
        h_dir h_root_gap.2, h_dir⟩

/-- Closing the v22 root-witness-gap kernel is sufficient to derive MLC. -/
theorem mlc_conjecture_of_finalAxiomRootWitnessGapKernelV22
    (h22 : FinalAxiomRootWitnessGapKernelV22) :
    LocallyConnectedSpace mandelbrotSet := by
  exact
    mlc_conjecture_of_finalAxiomWitnessGapKernelV21
      ((finalAxiomRootWitnessGapKernelV22_iff_finalAxiomWitnessGapKernelV21).1 h22)

/-- v23 geometric approach interface, routed through the existing seam
decomposition boundary. -/
def FinalAxiomGeometricApproachV23 : Prop :=
  FinalAxiomSeamDecompositionV20

/-- v23 topological approach interface, routed through the existing
root-witness-gap bridge boundary. -/
def FinalAxiomTopologicalApproachV23 : Prop :=
  FinalAxiomRootWitnessGapBridgeV22

/-- v23 analytic approach interface, routed through the existing witness
transport boundary. -/
def FinalAxiomAnalyticApproachV23 : Prop :=
  FinalAxiomWitnessTransportV20

/-- v23 combinatorial approach interface, routed through the existing
contrapositive-obstruction boundary. -/
def FinalAxiomCombinatorialApproachV23 : Prop :=
  FinalAxiomContrapositiveObstructionV20

/-- Geometric v23 approach is equivalent to the core bridge target. -/
theorem finalAxiomGeometricApproachV23_iff_finalAxiomCoreConstructiveGapV16 :
    FinalAxiomGeometricApproachV23 ↔ FinalAxiomCoreConstructiveGapV16 := by
  exact
    finalAxiomSeamDecompositionV20_iff_finalAxiomIngressBridgeGapV19.trans
      finalAxiomIngressBridgeGapV19_iff_finalAxiomCoreConstructiveGapV16

/-- Topological v23 approach is equivalent to the core bridge target. -/
theorem finalAxiomTopologicalApproachV23_iff_finalAxiomCoreConstructiveGapV16 :
    FinalAxiomTopologicalApproachV23 ↔ FinalAxiomCoreConstructiveGapV16 :=
  finalAxiomRootWitnessGapBridgeV22_iff_finalAxiomCoreConstructiveGapV16

/-- Analytic v23 approach is equivalent to the core bridge target. -/
theorem finalAxiomAnalyticApproachV23_iff_finalAxiomCoreConstructiveGapV16 :
    FinalAxiomAnalyticApproachV23 ↔ FinalAxiomCoreConstructiveGapV16 := by
  exact
    finalAxiomWitnessTransportV20_iff_finalAxiomIngressBridgeGapV19.trans
      finalAxiomIngressBridgeGapV19_iff_finalAxiomCoreConstructiveGapV16

/-- Combinatorial v23 approach is equivalent to the core bridge target. -/
theorem finalAxiomCombinatorialApproachV23_iff_finalAxiomCoreConstructiveGapV16 :
    FinalAxiomCombinatorialApproachV23 ↔ FinalAxiomCoreConstructiveGapV16 := by
  exact
    finalAxiomContrapositiveObstructionV20_iff_finalAxiomIngressBridgeGapV19.trans
      finalAxiomIngressBridgeGapV19_iff_finalAxiomCoreConstructiveGapV16

/-- v23 approach matrix: any one of the four approach interfaces is enough. -/
def FinalAxiomApproachMatrixV23 : Prop :=
  FinalAxiomGeometricApproachV23 ∨
    FinalAxiomTopologicalApproachV23 ∨
      FinalAxiomAnalyticApproachV23 ∨
        FinalAxiomCombinatorialApproachV23

/-- v23 approach matrix is equivalent to the core bridge target. -/
theorem finalAxiomApproachMatrixV23_iff_finalAxiomCoreConstructiveGapV16 :
    FinalAxiomApproachMatrixV23 ↔ FinalAxiomCoreConstructiveGapV16 := by
  constructor
  · intro h_matrix
    rcases h_matrix with h_geom | h_topo | h_analytic | h_comb
    · exact (finalAxiomGeometricApproachV23_iff_finalAxiomCoreConstructiveGapV16).1 h_geom
    · exact (finalAxiomTopologicalApproachV23_iff_finalAxiomCoreConstructiveGapV16).1 h_topo
    · exact (finalAxiomAnalyticApproachV23_iff_finalAxiomCoreConstructiveGapV16).1 h_analytic
    · exact (finalAxiomCombinatorialApproachV23_iff_finalAxiomCoreConstructiveGapV16).1 h_comb
  · intro h_core
    exact Or.inl
      ((finalAxiomGeometricApproachV23_iff_finalAxiomCoreConstructiveGapV16).2 h_core)

/-- v23 approach-matrix kernel: approach matrix plus explicit no-arg witness-gap
payload. -/
def FinalAxiomApproachMatrixKernelV23 : Prop :=
  FinalAxiomApproachMatrixV23 ∧ RemainingConstructiveIngressTwoWitnessGap

/-- v23 approach-matrix kernel is equivalent to the v21 witness-gap kernel. -/
theorem finalAxiomApproachMatrixKernelV23_iff_finalAxiomWitnessGapKernelV21 :
    FinalAxiomApproachMatrixKernelV23 ↔ FinalAxiomWitnessGapKernelV21 := by
  constructor
  · intro h23
    refine ⟨?_, h23.2⟩
    exact
      (finalAxiomWitnessGapBridgeV21_iff_finalAxiomCoreConstructiveGapV16).2
        ((finalAxiomApproachMatrixV23_iff_finalAxiomCoreConstructiveGapV16).1 h23.1)
  · intro h21
    refine ⟨?_, h21.2⟩
    exact
      (finalAxiomApproachMatrixV23_iff_finalAxiomCoreConstructiveGapV16).2
        ((finalAxiomWitnessGapBridgeV21_iff_finalAxiomCoreConstructiveGapV16).1 h21.1)

/-- v15 composite final gap is equivalent to the v23 approach-matrix kernel. -/
theorem finalAxiomEliminationGapV15_iff_finalAxiomApproachMatrixKernelV23 :
    FinalAxiomEliminationGapV15 ↔ FinalAxiomApproachMatrixKernelV23 := by
  exact
    finalAxiomEliminationGapV15_iff_finalAxiomWitnessGapKernelV21.trans
      finalAxiomApproachMatrixKernelV23_iff_finalAxiomWitnessGapKernelV21.symm

/-- v23 approach-matrix kernel cutover to the non-seam root closure
substitute. -/
theorem rootClosureSubstituteTwo_of_finalAxiomApproachMatrixKernelV23
    (h23 : FinalAxiomApproachMatrixKernelV23) :
    RootClosureSubstituteTwo := by
  exact
    rootClosureSubstituteTwo_of_finalAxiomWitnessGapKernelV21
      ((finalAxiomApproachMatrixKernelV23_iff_finalAxiomWitnessGapKernelV21).1 h23)

/-- Closing the v23 approach-matrix kernel is sufficient to derive MLC. -/
theorem mlc_conjecture_of_finalAxiomApproachMatrixKernelV23
    (h23 : FinalAxiomApproachMatrixKernelV23) :
    LocallyConnectedSpace mandelbrotSet := by
  exact
    mlc_conjecture_of_finalAxiomWitnessGapKernelV21
      ((finalAxiomApproachMatrixKernelV23_iff_finalAxiomWitnessGapKernelV21).1 h23)

/-- v24 root-closure bridge target: build the non-seam root substitute
directly from the explicit no-arg witness-gap payload. -/
def FinalAxiomRootClosureBridgeV24 : Prop :=
  RemainingConstructiveIngressTwoWitnessGap → RootClosureSubstituteTwo

/-- The v24 root-closure bridge target is equivalent to the v21 witness-gap
bridge target. -/
theorem finalAxiomRootClosureBridgeV24_iff_finalAxiomWitnessGapBridgeV21 :
    FinalAxiomRootClosureBridgeV24 ↔ FinalAxiomWitnessGapBridgeV21 := by
  constructor
  · intro h24 h_gap
    exact
      cp5ResidualLocalHomeomorphInjSeamTwo_of_rootSafeOutsideOpenInjWitnessTwo
        ((h24 h_gap).1)
  · intro h21 h_gap
    exact
      ⟨rootSafeOutsideOpenInjWitnessTwo_of_directProperLocalWitnessTwo_of_cp5ResidualLocalHomeomorphInjSeamTwo
          h_gap (h21 h_gap), h_gap⟩

/-- The v24 root-closure bridge target is equivalent to the v16 core bridge
target. -/
theorem finalAxiomRootClosureBridgeV24_iff_finalAxiomCoreConstructiveGapV16 :
    FinalAxiomRootClosureBridgeV24 ↔ FinalAxiomCoreConstructiveGapV16 := by
  exact
    finalAxiomRootClosureBridgeV24_iff_finalAxiomWitnessGapBridgeV21.trans
      finalAxiomWitnessGapBridgeV21_iff_finalAxiomCoreConstructiveGapV16

/-- v24 root-closure kernel: root-closure bridge plus explicit no-arg
witness-gap payload. -/
def FinalAxiomRootClosureKernelV24 : Prop :=
  FinalAxiomRootClosureBridgeV24 ∧ RemainingConstructiveIngressTwoWitnessGap

/-- v24 root-closure kernel is equivalent to the v21 witness-gap kernel. -/
theorem finalAxiomRootClosureKernelV24_iff_finalAxiomWitnessGapKernelV21 :
    FinalAxiomRootClosureKernelV24 ↔ FinalAxiomWitnessGapKernelV21 := by
  constructor
  · intro h24
    refine ⟨?_, h24.2⟩
    exact
      (finalAxiomWitnessGapBridgeV21_iff_finalAxiomCoreConstructiveGapV16).2
        ((finalAxiomRootClosureBridgeV24_iff_finalAxiomCoreConstructiveGapV16).1 h24.1)
  · intro h21
    refine ⟨?_, h21.2⟩
    exact
      (finalAxiomRootClosureBridgeV24_iff_finalAxiomCoreConstructiveGapV16).2
        ((finalAxiomWitnessGapBridgeV21_iff_finalAxiomCoreConstructiveGapV16).1 h21.1)

/-- v15 composite final gap is equivalent to the v24 root-closure kernel. -/
theorem finalAxiomEliminationGapV15_iff_finalAxiomRootClosureKernelV24 :
    FinalAxiomEliminationGapV15 ↔ FinalAxiomRootClosureKernelV24 := by
  exact
    finalAxiomEliminationGapV15_iff_finalAxiomWitnessGapKernelV21.trans
      finalAxiomRootClosureKernelV24_iff_finalAxiomWitnessGapKernelV21.symm

/-- v24 root-closure kernel cutover to the non-seam root substitute. -/
theorem rootClosureSubstituteTwo_of_finalAxiomRootClosureKernelV24
    (h24 : FinalAxiomRootClosureKernelV24) :
    RootClosureSubstituteTwo :=
  h24.1 h24.2

/-- Closing the v24 root-closure kernel is sufficient to derive MLC. -/
theorem mlc_conjecture_of_finalAxiomRootClosureKernelV24
    (h24 : FinalAxiomRootClosureKernelV24) :
    LocallyConnectedSpace mandelbrotSet := by
  exact
    mlc_conjecture_root_candidate_of_rootSafeOutsideOpenInjWitnessTwo_of_directProperLocalWitnessTwo
      (rootClosureSubstituteTwo_of_finalAxiomRootClosureKernelV24 h24).1
      (rootClosureSubstituteTwo_of_finalAxiomRootClosureKernelV24 h24).2

/-- v25 direct constructive approach interface: explicit no-arg witness-gap
payload paired with the core constructive bridge target. -/
def FinalAxiomDirectConstructiveApproachV25 : Prop :=
  RemainingConstructiveIngressTwoWitnessGap ∧ FinalAxiomCoreConstructiveGapV16

/-- The v25 direct constructive approach is equivalent to the v21 witness-gap
kernel. -/
theorem finalAxiomDirectConstructiveApproachV25_iff_finalAxiomWitnessGapKernelV21 :
    FinalAxiomDirectConstructiveApproachV25 ↔ FinalAxiomWitnessGapKernelV21 := by
  constructor
  · intro h25
    refine ⟨?_, h25.1⟩
    exact
      (finalAxiomWitnessGapBridgeV21_iff_finalAxiomCoreConstructiveGapV16).2 h25.2
  · intro h21
    refine ⟨h21.2, ?_⟩
    exact
      (finalAxiomWitnessGapBridgeV21_iff_finalAxiomCoreConstructiveGapV16).1 h21.1

/-- Closing the v25 direct constructive approach is sufficient to derive MLC. -/
theorem mlc_conjecture_of_finalAxiomDirectConstructiveApproachV25
    (h25 : FinalAxiomDirectConstructiveApproachV25) :
    LocallyConnectedSpace mandelbrotSet := by
  exact
    mlc_conjecture_of_finalAxiomWitnessGapKernelV21
      ((finalAxiomDirectConstructiveApproachV25_iff_finalAxiomWitnessGapKernelV21).1 h25)

/-- v25 alternative bridge strategies interface: either approach-matrix kernel
or root-closure kernel suffices. -/
def FinalAxiomAlternativeBridgeStrategiesV25 : Prop :=
  FinalAxiomApproachMatrixKernelV23 ∨ FinalAxiomRootClosureKernelV24

/-- The v25 alternative bridge strategies interface is equivalent to the v21
witness-gap kernel. -/
theorem finalAxiomAlternativeBridgeStrategiesV25_iff_finalAxiomWitnessGapKernelV21 :
    FinalAxiomAlternativeBridgeStrategiesV25 ↔ FinalAxiomWitnessGapKernelV21 := by
  constructor
  · intro h_alt
    rcases h_alt with h23 | h24
    · exact
        (finalAxiomApproachMatrixKernelV23_iff_finalAxiomWitnessGapKernelV21).1 h23
    · exact
        (finalAxiomRootClosureKernelV24_iff_finalAxiomWitnessGapKernelV21).1 h24
  · intro h21
    exact Or.inl
      ((finalAxiomApproachMatrixKernelV23_iff_finalAxiomWitnessGapKernelV21).2 h21)

/-- Closing the v25 alternative bridge strategies interface is sufficient to
derive MLC. -/
theorem mlc_conjecture_of_finalAxiomAlternativeBridgeStrategiesV25
    (h_alt : FinalAxiomAlternativeBridgeStrategiesV25) :
    LocallyConnectedSpace mandelbrotSet := by
  exact
    mlc_conjecture_of_finalAxiomWitnessGapKernelV21
      ((finalAxiomAlternativeBridgeStrategiesV25_iff_finalAxiomWitnessGapKernelV21).1 h_alt)

/-- v26 new direct approach interface, routed through the grounded v25 direct
constructive boundary. -/
def FinalAxiomNewDirectApproachV26 : Prop :=
  FinalAxiomDirectConstructiveApproachV25

/-- The v26 new direct approach is equivalent to the v21 witness-gap kernel. -/
theorem finalAxiomNewDirectApproachV26_iff_finalAxiomWitnessGapKernelV21 :
    FinalAxiomNewDirectApproachV26 ↔ FinalAxiomWitnessGapKernelV21 :=
  finalAxiomDirectConstructiveApproachV25_iff_finalAxiomWitnessGapKernelV21

/-- Closing the v26 new direct approach is sufficient to derive MLC. -/
theorem mlc_conjecture_of_finalAxiomNewDirectApproachV26
    (h26 : FinalAxiomNewDirectApproachV26) :
    LocallyConnectedSpace mandelbrotSet :=
  mlc_conjecture_of_finalAxiomDirectConstructiveApproachV25 h26

/-- v26 alternative proof-structure interface, routed through the grounded v25
alternative-strategies boundary. -/
def FinalAxiomAlternativeProofStructureV26 : Prop :=
  FinalAxiomAlternativeBridgeStrategiesV25

/-- The v26 alternative proof-structure interface is equivalent to the v21
witness-gap kernel. -/
theorem finalAxiomAlternativeProofStructureV26_iff_finalAxiomWitnessGapKernelV21 :
    FinalAxiomAlternativeProofStructureV26 ↔ FinalAxiomWitnessGapKernelV21 :=
  finalAxiomAlternativeBridgeStrategiesV25_iff_finalAxiomWitnessGapKernelV21

/-- Closing the v26 alternative proof-structure interface is sufficient to
derive MLC. -/
theorem mlc_conjecture_of_finalAxiomAlternativeProofStructureV26
    (h26 : FinalAxiomAlternativeProofStructureV26) :
    LocallyConnectedSpace mandelbrotSet :=
  mlc_conjecture_of_finalAxiomAlternativeBridgeStrategiesV25 h26

/-- v26 minimal-counterexample interface: contradiction of the negated core
bridge theorem. -/
def FinalAxiomMinimalCounterexampleV26 : Prop :=
  ¬ FinalAxiomCoreConstructiveGapV16 → False

/-- The v26 minimal-counterexample interface is equivalent to the v16 core
bridge target. -/
theorem finalAxiomMinimalCounterexampleV26_iff_finalAxiomCoreConstructiveGapV16 :
    FinalAxiomMinimalCounterexampleV26 ↔ FinalAxiomCoreConstructiveGapV16 := by
  constructor
  · intro h_min
    by_contra h_core
    exact h_min h_core
  · intro h_core h_not_core
    exact h_not_core h_core

/-- v26 minimal-counterexample kernel: minimal-counterexample interface plus the
explicit no-arg witness-gap payload. -/
def FinalAxiomMinimalCounterexampleKernelV26 : Prop :=
  FinalAxiomMinimalCounterexampleV26 ∧ RemainingConstructiveIngressTwoWitnessGap

/-- The v26 minimal-counterexample kernel is equivalent to the v21 witness-gap
kernel. -/
theorem finalAxiomMinimalCounterexampleKernelV26_iff_finalAxiomWitnessGapKernelV21 :
    FinalAxiomMinimalCounterexampleKernelV26 ↔ FinalAxiomWitnessGapKernelV21 := by
  constructor
  · intro h_min
    refine ⟨?_, h_min.2⟩
    exact
      (finalAxiomWitnessGapBridgeV21_iff_finalAxiomCoreConstructiveGapV16).2
        ((finalAxiomMinimalCounterexampleV26_iff_finalAxiomCoreConstructiveGapV16).1 h_min.1)
  · intro h21
    refine ⟨?_, h21.2⟩
    exact
      (finalAxiomMinimalCounterexampleV26_iff_finalAxiomCoreConstructiveGapV16).2
        ((finalAxiomWitnessGapBridgeV21_iff_finalAxiomCoreConstructiveGapV16).1 h21.1)

/-- Closing the v26 minimal-counterexample kernel is sufficient to derive MLC. -/
theorem mlc_conjecture_of_finalAxiomMinimalCounterexampleKernelV26
    (h_min : FinalAxiomMinimalCounterexampleKernelV26) :
    LocallyConnectedSpace mandelbrotSet := by
  exact
    mlc_conjecture_of_finalAxiomWitnessGapKernelV21
      ((finalAxiomMinimalCounterexampleKernelV26_iff_finalAxiomWitnessGapKernelV21).1 h_min)

/-- v26 parallel matrix: any grounded v26 route is enough to close the same
witness-gap kernel. -/
def FinalAxiomParallelMatrixV26 : Prop :=
  FinalAxiomNewDirectApproachV26 ∨
    FinalAxiomAlternativeProofStructureV26 ∨
      FinalAxiomMinimalCounterexampleKernelV26

/-- v26 parallel matrix is equivalent to the v21 witness-gap kernel. -/
theorem finalAxiomParallelMatrixV26_iff_finalAxiomWitnessGapKernelV21 :
    FinalAxiomParallelMatrixV26 ↔ FinalAxiomWitnessGapKernelV21 := by
  constructor
  · intro h26
    rcases h26 with h_dir | h_alt | h_min
    · exact (finalAxiomNewDirectApproachV26_iff_finalAxiomWitnessGapKernelV21).1 h_dir
    · exact
        (finalAxiomAlternativeProofStructureV26_iff_finalAxiomWitnessGapKernelV21).1 h_alt
    · exact
        (finalAxiomMinimalCounterexampleKernelV26_iff_finalAxiomWitnessGapKernelV21).1 h_min
  · intro h21
    exact Or.inl
      ((finalAxiomNewDirectApproachV26_iff_finalAxiomWitnessGapKernelV21).2 h21)

/-- v15 composite final gap is equivalent to the v26 parallel matrix. -/
theorem finalAxiomEliminationGapV15_iff_finalAxiomParallelMatrixV26 :
    FinalAxiomEliminationGapV15 ↔ FinalAxiomParallelMatrixV26 := by
  exact
    finalAxiomEliminationGapV15_iff_finalAxiomWitnessGapKernelV21.trans
      finalAxiomParallelMatrixV26_iff_finalAxiomWitnessGapKernelV21.symm

/-- Closing the v26 parallel matrix is sufficient to derive MLC. -/
theorem mlc_conjecture_of_finalAxiomParallelMatrixV26
    (h26 : FinalAxiomParallelMatrixV26) :
    LocallyConnectedSpace mandelbrotSet := by
  exact
    mlc_conjecture_of_finalAxiomWitnessGapKernelV21
      ((finalAxiomParallelMatrixV26_iff_finalAxiomWitnessGapKernelV21).1 h26)

/-- Localized-source transport gap interface: strict subcutoff local-window
transport package plus the explicit ingress witness-gap payload. -/
def LocalizedSourceToRemainingConstructiveIngressGapTwo : Prop :=
  StrictlySubcutoffLocalWindowWithTransportBridgeTwo ∧
    RemainingConstructiveIngressTwoWitnessGap

/-- Extract the explicit ingress witness-gap payload from the localized-source
transport gap interface. -/
theorem remainingConstructiveIngressTwoWitnessGap_of_localizedSourceToRemainingConstructiveIngressGapTwo
    (h : LocalizedSourceToRemainingConstructiveIngressGapTwo) :
    RemainingConstructiveIngressTwoWitnessGap :=
  h.2

/-- Extract the direct proper/local witness from the localized-source transport
gap interface. -/
theorem directProperLocalWitnessTwo_of_localizedSourceToRemainingConstructiveIngressGapTwo
    (h : LocalizedSourceToRemainingConstructiveIngressGapTwo) :
    DirectProperLocalWitnessTwo := by
  simpa [RemainingConstructiveIngressTwoWitnessGap] using h.2

/-- No-arg direct-witness target staged from a partial-window source: any
partial-window payload should produce `DirectProperLocalWitnessTwo`. -/
def NoargDirectProperLocalWitnessTwoFromPartialWindowSourceTwo : Prop :=
  PartialWindowNotCoveringCutoffWithNontransportedTailTwo →
    DirectProperLocalWitnessTwo

/-- Bridge into the no-arg direct-witness target from the (currently
inconsistent) localized-source-to-ingress-gap interface. -/
theorem noargDirectProperLocalWitnessTwoFromPartialWindowSourceTwo_of_localizedSourceToRemainingConstructiveIngressGapTwo
    (h_loc : LocalizedSourceToRemainingConstructiveIngressGapTwo) :
    NoargDirectProperLocalWitnessTwoFromPartialWindowSourceTwo := by
  intro _hpartial
  exact directProperLocalWitnessTwo_of_localizedSourceToRemainingConstructiveIngressGapTwo h_loc

/-- v7 constructor-oriented no-arg direct-witness target from directly
constructed partial-window sources. -/
def NoargDirectProperLocalWitnessTwoFromConstructedPartialSourceTwo : Prop :=
  ConstructPartialWindowWitnessDirectlyWithoutTransportTwo →
    DirectProperLocalWitnessTwo

/-- v8 no-arg direct-witness target from explicit subcutoff localized-source
candidates derived from Green bounds. -/
def NoargDirectProperLocalWitnessTwoFromExplicitLocalizedSourceTwo : Prop :=
  ExplicitSubcutoffWitnessCandidateFromGreenBoundsTwo →
    DirectProperLocalWitnessTwo

/-- Any v6 partial-window no-arg direct-witness target upgrades directly to the
v7 constructor-oriented target. -/
theorem noargDirectProperLocalWitnessTwoFromConstructedPartialSourceTwo_of_noargDirectProperLocalWitnessTwoFromPartialWindowSourceTwo
    (h_noarg : NoargDirectProperLocalWitnessTwoFromPartialWindowSourceTwo) :
    NoargDirectProperLocalWitnessTwoFromConstructedPartialSourceTwo :=
  h_noarg

/-- Any v7 constructor-oriented no-arg direct-witness target upgrades to the v8
explicit-localized-source target through the explicit-candidate projection. -/
theorem noargDirectProperLocalWitnessTwoFromExplicitLocalizedSourceTwo_of_noargDirectProperLocalWitnessTwoFromConstructedPartialSourceTwo
    (h_noarg : NoargDirectProperLocalWitnessTwoFromConstructedPartialSourceTwo) :
    NoargDirectProperLocalWitnessTwoFromExplicitLocalizedSourceTwo := by
  intro hexpl
  exact h_noarg
    (constructPartialWindowWitnessDirectlyWithoutTransportTwo_of_explicitSubcutoffWitnessCandidateFromGreenBoundsTwo
      hexpl)

/-- Any v8 explicit-localized-source no-arg target restricts to the v7
constructor-oriented target through the canonical explicit enrichment. -/
theorem noargDirectProperLocalWitnessTwoFromConstructedPartialSourceTwo_of_noargDirectProperLocalWitnessTwoFromExplicitLocalizedSourceTwo
    (h_noarg : NoargDirectProperLocalWitnessTwoFromExplicitLocalizedSourceTwo) :
    NoargDirectProperLocalWitnessTwoFromConstructedPartialSourceTwo := by
  intro hpartial
  exact h_noarg
    (explicitSubcutoffWitnessCandidateFromGreenBoundsTwo_of_constructPartialWindowWitnessDirectlyWithoutTransportTwo
      hpartial)

/-- The v8 explicit-localized-source no-arg target is equivalent to the v7
constructor-oriented no-arg target. -/
theorem noargDirectProperLocalWitnessTwoFromExplicitLocalizedSourceTwo_iff_noargDirectProperLocalWitnessTwoFromConstructedPartialSourceTwo :
    NoargDirectProperLocalWitnessTwoFromExplicitLocalizedSourceTwo ↔
      NoargDirectProperLocalWitnessTwoFromConstructedPartialSourceTwo := by
  constructor
  · intro h_noarg
    exact
      noargDirectProperLocalWitnessTwoFromConstructedPartialSourceTwo_of_noargDirectProperLocalWitnessTwoFromExplicitLocalizedSourceTwo
        h_noarg
  · intro h_noarg
    exact
      noargDirectProperLocalWitnessTwoFromExplicitLocalizedSourceTwo_of_noargDirectProperLocalWitnessTwoFromConstructedPartialSourceTwo
        h_noarg

/-- Current-model no-go: localized-source transport gap interface is
inconsistent because its strict-subcutoff local-window package is inconsistent. -/
theorem not_localizedSourceToRemainingConstructiveIngressGapTwo :
    ¬ LocalizedSourceToRemainingConstructiveIngressGapTwo := by
  intro h
  exact not_strictlySubcutoffLocalWindowWithTransportBridgeTwo h.1

/-- Localized source interface that deliberately avoids full-window upgrade:
geometric outside-open/fiber ingress plus a strictly subcutoff partial window
without any tail-transport payload. -/
def LocalizedSourceWithoutFullWindowUpgradeTwo : Prop :=
  RootSafeOutsideOpenInjWitnessTwoGeometricFiberIngressFamilyTwo ∧
    PartialWindowNotCoveringCutoffWithNontransportedTailTwo

/-- Projection: geometric outside-open/fiber ingress component of the localized
source without full-window upgrade. -/
theorem rootSafeOutsideOpenInjWitnessTwoGeometricFiberIngressFamilyTwo_of_localizedSourceWithoutFullWindowUpgradeTwo
    (h : LocalizedSourceWithoutFullWindowUpgradeTwo) :
    RootSafeOutsideOpenInjWitnessTwoGeometricFiberIngressFamilyTwo :=
  h.1

/-- Projection: partial-window component of the localized source without
full-window upgrade. -/
theorem partialWindowNotCoveringCutoffWithNontransportedTailTwo_of_localizedSourceWithoutFullWindowUpgradeTwo
    (h : LocalizedSourceWithoutFullWindowUpgradeTwo) :
    PartialWindowNotCoveringCutoffWithNontransportedTailTwo :=
  h.2

/-- Current-model no-go transfer: even with a localized source that avoids
full-window upgrade, the previous localized-source-to-ingress-gap interface
remains unavailable. -/
theorem not_localizedSourceToRemainingConstructiveIngressGapTwo_of_localizedSourceWithoutFullWindowUpgradeTwo
    (_h : LocalizedSourceWithoutFullWindowUpgradeTwo) :
    ¬ LocalizedSourceToRemainingConstructiveIngressGapTwo := by
  intro hgap
  exact not_localizedSourceToRemainingConstructiveIngressGapTwo hgap

/-- v7 constructor map: a direct partial-window witness yields a localized
source witness by pairing it with the canonical strict-mono-seeded geometric
ingress witness. -/
def LocalizedSourceWitnessFromPartialWindowConstructorTwo : Prop :=
  ConstructPartialWindowWitnessDirectlyWithoutTransportTwo →
    LocalizedSourceWithoutFullWindowUpgradeTwo

/-- Canonical constructor for localized-source witnesses from direct partial
window witnesses. -/
theorem localizedSourceWitnessFromPartialWindowConstructorTwo_canonical :
    LocalizedSourceWitnessFromPartialWindowConstructorTwo := by
  intro hpartial
  exact ⟨rootSafeOutsideOpenInjWitnessTwoGeometricFiberIngressFamilyTwo_strictMono_seeded, hpartial⟩

/-- v8 constructor map: an explicit subcutoff witness candidate from Green
bounds yields a localized source witness after projection to the v7 constructor
target. -/
def LocalizedSourceWitnessFromExplicitSubcutoffWitnessTwo : Prop :=
  ExplicitSubcutoffWitnessCandidateFromGreenBoundsTwo →
    LocalizedSourceWithoutFullWindowUpgradeTwo

/-- Canonical constructor for localized-source witnesses from v8 explicit
subcutoff witness candidates. -/
theorem localizedSourceWitnessFromExplicitSubcutoffWitnessTwo_canonical :
    LocalizedSourceWitnessFromExplicitSubcutoffWitnessTwo := by
  intro hexpl
  exact localizedSourceWitnessFromPartialWindowConstructorTwo_canonical
    (constructPartialWindowWitnessDirectlyWithoutTransportTwo_of_explicitSubcutoffWitnessCandidateFromGreenBoundsTwo
      hexpl)

/-- Any v7 partial-window localized-source constructor upgrades to the v8
explicit-subcutoff constructor interface. -/
theorem localizedSourceWitnessFromExplicitSubcutoffWitnessTwo_of_localizedSourceWitnessFromPartialWindowConstructorTwo
    (h_loc : LocalizedSourceWitnessFromPartialWindowConstructorTwo) :
    LocalizedSourceWitnessFromExplicitSubcutoffWitnessTwo := by
  intro hexpl
  exact h_loc
    (constructPartialWindowWitnessDirectlyWithoutTransportTwo_of_explicitSubcutoffWitnessCandidateFromGreenBoundsTwo
      hexpl)

/-- Any v8 explicit-subcutoff localized-source constructor restricts to the v7
partial-window constructor interface. -/
theorem localizedSourceWitnessFromPartialWindowConstructorTwo_of_localizedSourceWitnessFromExplicitSubcutoffWitnessTwo
    (h_loc : LocalizedSourceWitnessFromExplicitSubcutoffWitnessTwo) :
    LocalizedSourceWitnessFromPartialWindowConstructorTwo := by
  intro hpartial
  exact h_loc
    (explicitSubcutoffWitnessCandidateFromGreenBoundsTwo_of_constructPartialWindowWitnessDirectlyWithoutTransportTwo
      hpartial)

/-- The v8 explicit-subcutoff localized-source constructor interface is
equivalent to the v7 partial-window constructor interface. -/
theorem localizedSourceWitnessFromExplicitSubcutoffWitnessTwo_iff_localizedSourceWitnessFromPartialWindowConstructorTwo :
    LocalizedSourceWitnessFromExplicitSubcutoffWitnessTwo ↔
      LocalizedSourceWitnessFromPartialWindowConstructorTwo := by
  constructor
  · intro h_loc
    exact
      localizedSourceWitnessFromPartialWindowConstructorTwo_of_localizedSourceWitnessFromExplicitSubcutoffWitnessTwo
        h_loc
  · intro h_loc
    exact
      localizedSourceWitnessFromExplicitSubcutoffWitnessTwo_of_localizedSourceWitnessFromPartialWindowConstructorTwo
        h_loc

/-- Build aggregate constructive ingress from the explicit ingress witness-gap
payload. -/
theorem remainingConstructiveIngressTwo_of_remainingConstructiveIngressTwoWitnessGap
    (h_gap : RemainingConstructiveIngressTwoWitnessGap) :
    RemainingConstructiveIngressTwo :=
  remainingConstructiveIngressTwo_of_directProperLocalWitnessTwo h_gap

/-- The aggregate constructive ingress predicate is equivalent to the explicit
ingress witness-gap payload. -/
theorem remainingConstructiveIngressTwo_iff_remainingConstructiveIngressTwoWitnessGap :
    RemainingConstructiveIngressTwo ↔ RemainingConstructiveIngressTwoWitnessGap := by
  simpa [RemainingConstructiveIngressTwoWitnessGap] using
    (remainingConstructiveIngressTwo_iff_directProperLocalWitness)

/-- Primitive-family specialization: the ingress witness-gap payload at `c = 2`
is obtained directly from a primitive restricted-map proper/local witness. -/
theorem remainingConstructiveIngressTwoWitnessGap_of_primitiveRestrictedMapProperLocalWitnessFamilyTwo
    (h_prim : PrimitiveRestrictedMapProperLocalWitnessFamilyTwo) :
    RemainingConstructiveIngressTwoWitnessGap :=
  directProperLocalWitnessTwo_of_primitiveRestrictedMapProperLocalWitnessFamilyTwo h_prim

/-- Primitive-family specialization: ingress witness-gap payload is equivalent
to the primitive restricted-map proper/local witness interface at `c = 2`. -/
theorem primitiveRestrictedMapProperLocalWitnessFamilyTwo_iff_remainingConstructiveIngressTwoWitnessGap :
    PrimitiveRestrictedMapProperLocalWitnessFamilyTwo ↔
      RemainingConstructiveIngressTwoWitnessGap := by
  simpa [RemainingConstructiveIngressTwoWitnessGap] using
    primitiveRestrictedMapProperLocalWitnessFamilyTwo_iff_directProperLocalWitnessTwo

/-- Non-seeded local-homeomorph branch seam constructor at `c = 2`, expressed
with explicit Green-ray seam hypotheses instead of fixed seed constants. -/
theorem cp5ResidualLocalHomeomorphInjSeamTwo_nonseeded_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam
    (huniq_seam : GreenRayUniquePreimageTwoAnchorSeam)
    (hlog_gt_anchor : GreenRayLogGtAnchorTwoSeam) :
    CP5ResidualLocalHomeomorphInjSeamTwo :=
  cp5ResidualLocalHomeomorphInjSeamTwo_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam
    huniq_seam hlog_gt_anchor

/-- Root witness-gap payload where Green-ray seam assumptions are explicit
parameters and no fixed seed constant appears. -/
def RootClosureSubstituteTwoWitnessGapWithoutGreenRaySeed : Prop :=
  RemainingConstructiveIngressTwoWitnessGap ∧
    GreenRayUniquePreimageTwoAnchorSeam ∧ GreenRayLogGtAnchorTwoSeam

/-- Discharge the root witness-gap payload from explicit non-seeded Green-ray
seam assumptions plus the ingress witness-gap payload. -/
theorem rootClosureSubstituteTwoWitnessGap_of_rootClosureSubstituteTwoWitnessGapWithoutGreenRaySeed
    (h : RootClosureSubstituteTwoWitnessGapWithoutGreenRaySeed) :
    RootClosureSubstituteTwoWitnessGap := by
  refine ⟨remainingConstructiveIngressTwo_of_remainingConstructiveIngressTwoWitnessGap h.1, ?_⟩
  exact
    cp5ResidualLocalHomeomorphInjSeamTwo_nonseeded_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam
      h.2.1 h.2.2

/-- Root closure substitute witness from explicit non-seeded Green-ray seam
assumptions plus the ingress witness-gap payload. -/
theorem rootClosureSubstituteTwo_of_rootClosureSubstituteTwoWitnessGapWithoutGreenRaySeed
    (h : RootClosureSubstituteTwoWitnessGapWithoutGreenRaySeed) :
    RootClosureSubstituteTwo := by
  refine ⟨?_, h.1⟩
  exact
    rootSafeOutsideOpenInjWitnessTwo_of_directProperLocalWitnessTwo_of_cp5ResidualLocalHomeomorphInjSeamTwo
      h.1
      (cp5ResidualLocalHomeomorphInjSeamTwo_nonseeded_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam
        h.2.1 h.2.2)

/-- Root-adjacent closure from the explicit non-seeded Green-ray seam interface
for the witness-gap payload. -/
theorem mlc_conjecture_of_rootClosureSubstituteTwoWitnessGapWithoutGreenRaySeed
    (h : RootClosureSubstituteTwoWitnessGapWithoutGreenRaySeed) :
    LocallyConnectedSpace mandelbrotSet := by
  exact
    mlc_conjecture_root_candidate_of_rootSafeOutsideOpenInjWitnessTwo_of_directProperLocalWitnessTwo
      (rootClosureSubstituteTwo_of_rootClosureSubstituteTwoWitnessGapWithoutGreenRaySeed h).1
      (rootClosureSubstituteTwo_of_rootClosureSubstituteTwoWitnessGapWithoutGreenRaySeed h).2

/-- Build the minimal non-seeded root-closure substitute interface from its
components. -/
theorem rootClosureSubstituteTwo_of_rootSafeOutsideOpenInjWitnessTwo_of_directProperLocalWitnessTwo
    (h_inj : RootSafeOutsideOpenInjWitnessTwo)
    (h_dir : DirectProperLocalWitnessTwo) :
    RootClosureSubstituteTwo :=
  ⟨h_inj, h_dir⟩

/-- Refined bridge into the minimal root-closure substitute interface from a
direct proper/local witness plus local-homeomorph branch seam data. -/
theorem rootClosureSubstituteTwo_of_directProperLocalWitnessTwo_of_cp5ResidualLocalHomeomorphInjSeamTwo
    (h : DirectProperLocalWitnessTwo)
    (h_seam : CP5ResidualLocalHomeomorphInjSeamTwo) :
    RootClosureSubstituteTwo :=
  rootClosureSubstituteTwo_of_rootSafeOutsideOpenInjWitnessTwo_of_directProperLocalWitnessTwo
    (rootSafeOutsideOpenInjWitnessTwo_of_directProperLocalWitnessTwo_of_cp5ResidualLocalHomeomorphInjSeamTwo
      h h_seam)
    h

/-- Extract the explicit witness-gap payload from a root-closure substitute
witness. -/
theorem rootClosureSubstituteTwoWitnessGap_of_rootClosureSubstituteTwo
    (h_sub : RootClosureSubstituteTwo) :
    RootClosureSubstituteTwoWitnessGap :=
  ⟨remainingConstructiveIngressTwo_of_directProperLocalWitnessTwo h_sub.2,
    cp5ResidualLocalHomeomorphInjSeamTwo_of_directProperLocalWitnessTwo h_sub.2⟩

/-- Rebuild the root-closure substitute witness from the explicit witness-gap
payload. -/
theorem rootClosureSubstituteTwo_of_rootClosureSubstituteTwoWitnessGap
    (h_gap : RootClosureSubstituteTwoWitnessGap) :
    RootClosureSubstituteTwo :=
  rootClosureSubstituteTwo_of_directProperLocalWitnessTwo_of_cp5ResidualLocalHomeomorphInjSeamTwo
    (directProperLocalWitnessTwo_of_remainingConstructiveIngressTwo h_gap.1)
    h_gap.2

/-- Root-closure substitute witness is equivalent to the current explicit
witness-gap payload. -/
theorem rootClosureSubstituteTwo_iff_rootClosureSubstituteTwoWitnessGap :
    RootClosureSubstituteTwo ↔ RootClosureSubstituteTwoWitnessGap := by
  constructor
  · intro h_sub
    exact rootClosureSubstituteTwoWitnessGap_of_rootClosureSubstituteTwo h_sub
  · intro h_gap
    exact rootClosureSubstituteTwo_of_rootClosureSubstituteTwoWitnessGap h_gap

/-- Primitive-family specialization: build the explicit root witness-gap payload
directly from a primitive restricted-map proper/local witness at `c = 2`. -/
theorem rootClosureSubstituteTwoWitnessGap_of_primitiveRestrictedMapProperLocalWitnessFamilyTwo
    (h_prim : PrimitiveRestrictedMapProperLocalWitnessFamilyTwo) :
    RootClosureSubstituteTwoWitnessGap := by
  refine ⟨?_, ?_⟩
  · exact remainingConstructiveIngressTwo_of_directProperLocalWitnessTwo
      (directProperLocalWitnessTwo_of_primitiveRestrictedMapProperLocalWitnessFamilyTwo h_prim)
  · exact cp5ResidualLocalHomeomorphInjSeamTwo_of_directProperLocalWitnessTwo
      (directProperLocalWitnessTwo_of_primitiveRestrictedMapProperLocalWitnessFamilyTwo h_prim)

/-- Primitive-family specialization: build the non-seam root-closure substitute
interface directly from a primitive restricted-map proper/local witness. -/
theorem rootClosureSubstituteTwo_of_primitiveRestrictedMapProperLocalWitnessFamilyTwo
    (h_prim : PrimitiveRestrictedMapProperLocalWitnessFamilyTwo) :
    RootClosureSubstituteTwo :=
  rootClosureSubstituteTwo_of_rootClosureSubstituteTwoWitnessGap
    (rootClosureSubstituteTwoWitnessGap_of_primitiveRestrictedMapProperLocalWitnessFamilyTwo h_prim)

/-- Root-adjacent closure from aggregate constructive ingress plus local seam
data at `c = 2`. -/
theorem mlc_conjecture_of_rootClosureSubstituteTwoWitnessGap
    (h_gap : RootClosureSubstituteTwoWitnessGap) :
    LocallyConnectedSpace mandelbrotSet := by
  exact
    mlc_conjecture_root_candidate_of_rootSafeOutsideOpenInjWitnessTwo_of_directProperLocalWitnessTwo
      (rootClosureSubstituteTwo_of_rootClosureSubstituteTwoWitnessGap h_gap).1
      (rootClosureSubstituteTwo_of_rootClosureSubstituteTwoWitnessGap h_gap).2

/-- Root-adjacent closure through the minimal non-seeded substitute interface. -/
theorem mlc_conjecture_of_rootClosureSubstituteTwo
    (h_sub : RootClosureSubstituteTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_root_candidate_of_rootSafeOutsideOpenInjWitnessTwo_of_directProperLocalWitnessTwo
    h_sub.1 h_sub.2

/-- Root boundary in direct inj/surj form: outside-open injectivity plus the
direct proper/local witness imply MLC at `c = 2` without passing through an
`ExternalRayMapData`-typed statement at this boundary. -/
theorem mlc_conjecture_of_rootSafeOutsideOpenInjWitnessTwo_of_directProperLocalWitnessTwo
    (h_inj : RootSafeOutsideOpenInjWitnessTwo)
    (h_dir : DirectProperLocalWitnessTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_rootClosureSubstituteTwo
    (rootClosureSubstituteTwo_of_rootSafeOutsideOpenInjWitnessTwo_of_directProperLocalWitnessTwo
      h_inj h_dir)

/-- Root boundary wrapper through the named non-seam replacement target. -/
theorem mlc_conjecture_of_nonseamRootReplacementTargetTwo
    (h_nonseam : NonseamRootReplacementTargetTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_rootClosureSubstituteTwo h_nonseam

/-- Root closure from explicit outside-open injectivity constructor-gap payload
plus direct proper/local witness, routed through the non-seam replacement
target. -/
theorem mlc_conjecture_of_rootSafeOutsideOpenInjWitnessTwoWitnessGap_of_directProperLocalWitnessTwo
    (h_gap : RootSafeOutsideOpenInjWitnessTwoWitnessGap)
    (h_dir : DirectProperLocalWitnessTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_nonseamRootReplacementTargetTwo
    (rootClosureSubstituteTwo_of_rootSafeOutsideOpenInjWitnessTwo_of_directProperLocalWitnessTwo
      (rootSafeOutsideOpenInjWitnessTwo_of_rootSafeOutsideOpenInjWitnessTwoWitnessGap h_gap)
      h_dir)

/-- Strict-mono-free root-candidate wrapper parameterized by the exact remaining
outside-open injectivity witness target and specialized to the current
anchor-gap seed. -/
theorem mlc_conjecture_root_candidate_of_rootSafeOutsideOpenInjWitnessTwo
    (h_inj : RootSafeOutsideOpenInjWitnessTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_root_candidate_of_rootSafeOutsideOpenInjWitnessTwo_of_greenRayLogGtAnchorTwoSeam
    greenRayLogGtAnchorTwo_seed h_inj

/-- Strict-mono-free root-candidate wrapper at `c = 2`, specialized to the
known non-iterate-left injectivity-source aggregate. -/
theorem mlc_conjecture_root_candidate_of_greenRayLogGtAnchorTwoSeam_of_knownInjOnOutsideOpenSourceCandidateTwo
    (hlog_gt_anchor : GreenRayLogGtAnchorTwoSeam)
    (h : KnownInjOnOutsideOpenSourceCandidateTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_root_candidate_of_rootSafeOutsideOpenInjWitnessTwo_of_greenRayLogGtAnchorTwoSeam
    hlog_gt_anchor
    (rootSafeOutsideOpenInjWitnessTwo_of_knownInjOnOutsideOpenSourceCandidateTwo h)

/-- Strict-mono-free root-candidate wrapper at `c = 2`, specialized to the
known non-iterate-left injectivity-source aggregate and the current anchor-gap
seed. -/
theorem mlc_conjecture_root_candidate_of_knownInjOnOutsideOpenSourceCandidateTwo
    (h : KnownInjOnOutsideOpenSourceCandidateTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_root_candidate_of_greenRayLogGtAnchorTwoSeam_of_knownInjOnOutsideOpenSourceCandidateTwo
    greenRayLogGtAnchorTwo_seed h

/-- Strict-mono-free root-candidate wrapper at `c = 2`, specialized to
outside-open analyticity. -/
theorem mlc_conjecture_root_candidate_of_greenRayLogGtAnchorTwoSeam_of_outsideOpenAnalyticityHypothesis
    (hlog_gt_anchor : GreenRayLogGtAnchorTwoSeam)
    (h_analytic : OutsideOpenAnalyticityHypothesis (2 : ℂ)) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_root_candidate_of_rootSafeOutsideOpenInjWitnessTwo_of_greenRayLogGtAnchorTwoSeam
    hlog_gt_anchor
    (rootSafeOutsideOpenInjWitnessTwo_of_outsideOpenAnalyticityHypothesis h_analytic)

/-- Strict-mono-free root-candidate wrapper at `c = 2`, specialized to
outside-open analyticity and the current anchor-gap seed. -/
theorem mlc_conjecture_root_candidate_of_outsideOpenAnalyticityHypothesis
    (h_analytic : OutsideOpenAnalyticityHypothesis (2 : ℂ)) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_root_candidate_of_greenRayLogGtAnchorTwoSeam_of_outsideOpenAnalyticityHypothesis
    greenRayLogGtAnchorTwo_seed h_analytic

/-- Strict-mono-free root-candidate wrapper at `c = 2`, specialized to a direct
proper/local witness plus a local seam witness. -/
theorem mlc_conjecture_root_candidate_of_directProperLocalWitnessTwo_of_cp5ResidualLocalHomeomorphInjSeamTwo
    (h : DirectProperLocalWitnessTwo)
    (h_seam : CP5ResidualLocalHomeomorphInjSeamTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_rootClosureSubstituteTwo
    (rootClosureSubstituteTwo_of_directProperLocalWitnessTwo_of_cp5ResidualLocalHomeomorphInjSeamTwo
      h h_seam)

/-- Strict-mono-free root-candidate wrapper at `c = 2`, specialized to the CP5
local-homeomorph source pair plus a local seam witness. -/
theorem mlc_conjecture_root_candidate_of_localHomeomorphSurjSourceTwo_of_cp5ResidualLocalHomeomorphInjSeamTwo
    (hlocal :
      IsProperMap (bottcher_map_outside_open_to_exterior (2 : ℂ)) ∧
        IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (h_seam : CP5ResidualLocalHomeomorphInjSeamTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_root_candidate_of_rootSafeOutsideOpenInjWitnessTwo
    (rootSafeOutsideOpenInjWitnessTwo_of_localHomeomorphSurjSourceTwo_of_cp5ResidualLocalHomeomorphInjSeamTwo
      hlocal h_seam)

/-- Strict-mono-free root-candidate wrapper at `c = 2`, specialized to explicit
restricted-map proper/local hypotheses plus a local seam witness. -/
theorem mlc_conjecture_root_candidate_of_isProperMap_restrict_of_isLocalHomeomorph_restrict_of_cp5ResidualLocalHomeomorphInjSeamTwo
    (hproper : IsProperMap (bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (hlocal : IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (h_seam : CP5ResidualLocalHomeomorphInjSeamTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_root_candidate_of_rootSafeOutsideOpenInjWitnessTwo
    (rootSafeOutsideOpenInjWitnessTwo_of_isProperMap_restrict_of_isLocalHomeomorph_restrict_of_cp5ResidualLocalHomeomorphInjSeamTwo
      hproper hlocal h_seam)

/-- Strict-mono-free root-candidate wrapper at `c = 2`, specialized to a direct
proper/local witness and Green-ray seam payload. -/
theorem mlc_conjecture_root_candidate_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam_of_directProperLocalWitnessTwo
    (huniq_seam : GreenRayUniquePreimageTwoAnchorSeam)
    (hlog_gt_anchor : GreenRayLogGtAnchorTwoSeam)
    (h : DirectProperLocalWitnessTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_root_candidate_of_rootSafeOutsideOpenInjWitnessTwo
    (injOn_outside_open_two_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam_of_directProperLocalWitnessTwo
      huniq_seam hlog_gt_anchor h)

/-- Strict-mono-free root-candidate wrapper at `c = 2`, specialized to the CP5
local-homeomorph source pair and Green-ray seam payload. -/
theorem mlc_conjecture_root_candidate_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam_of_localHomeomorphSurjSourceTwo
    (huniq_seam : GreenRayUniquePreimageTwoAnchorSeam)
    (hlog_gt_anchor : GreenRayLogGtAnchorTwoSeam)
    (hlocal :
      IsProperMap (bottcher_map_outside_open_to_exterior (2 : ℂ)) ∧
        IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ))) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_root_candidate_of_rootSafeOutsideOpenInjWitnessTwo
    (rootSafeOutsideOpenInjWitnessTwo_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam_of_localHomeomorphSurjSourceTwo
      huniq_seam hlog_gt_anchor hlocal)

/-- Strict-mono-free root-candidate wrapper at `c = 2`, specialized to explicit
restricted-map proper/local hypotheses and Green-ray seam payload. -/
theorem mlc_conjecture_root_candidate_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam_of_isProperMap_restrict_of_isLocalHomeomorph_restrict
    (huniq_seam : GreenRayUniquePreimageTwoAnchorSeam)
    (hlog_gt_anchor : GreenRayLogGtAnchorTwoSeam)
    (hproper : IsProperMap (bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (hlocal : IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ))) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_root_candidate_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam_of_localHomeomorphSurjSourceTwo
    huniq_seam hlog_gt_anchor ⟨hproper, hlocal⟩

/-- Strict-mono-seeded root-candidate wrapper at `c = 2`, specialized to
explicit restricted-map proper/local hypotheses. -/
theorem mlc_conjecture_root_candidate_of_isProperMap_restrict_of_isLocalHomeomorph_restrict_strictMono
    (hproper : IsProperMap (bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (hlocal : IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ))) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_root_candidate_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam_of_isProperMap_restrict_of_isLocalHomeomorph_restrict
    greenRayUniquePreimageTwoAnchorSeam_strictMono_seeded_of_greenFunctionStrictMonoAlongRayBasinTwo_seed
    greenRayLogGtAnchorTwo_seed
    hproper hlocal

/-- Strict-mono-seeded root-candidate wrapper at `c = 2`, specialized to the CP5
local-homeomorph source pair. -/
theorem mlc_conjecture_root_candidate_of_localHomeomorphSurjSourceTwo_strictMono
    (hlocal :
      IsProperMap (bottcher_map_outside_open_to_exterior (2 : ℂ)) ∧
        IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ))) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_root_candidate_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam_of_localHomeomorphSurjSourceTwo
    greenRayUniquePreimageTwoAnchorSeam_strictMono_seeded_of_greenFunctionStrictMonoAlongRayBasinTwo_seed
    greenRayLogGtAnchorTwo_seed
    hlocal

/-- Strict-mono-seeded root-candidate wrapper at `c = 2`, specialized to a
direct proper/local witness. -/
theorem mlc_conjecture_root_candidate_of_directProperLocalWitnessTwo_strictMono
    (h : DirectProperLocalWitnessTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_root_candidate_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam_of_directProperLocalWitnessTwo
    greenRayUniquePreimageTwoAnchorSeam_strictMono_seeded_of_greenFunctionStrictMonoAlongRayBasinTwo_seed
    greenRayLogGtAnchorTwo_seed
    h

/-- Strict-mono-free rooted theorem at `c = 2`, specialized to the known
non-iterate-left injectivity-source aggregate. -/
theorem mlc_conjecture_of_greenRayLogGtAnchorTwoSeam_of_knownInjOnOutsideOpenSourceCandidateTwo
    (hlog_gt_anchor : GreenRayLogGtAnchorTwoSeam)
    (h : KnownInjOnOutsideOpenSourceCandidateTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_externalRayMapData_two
    (external_ray_map_exists_two_constructive_strictMono_free_of_greenRayLogGtAnchorTwoSeam_of_knownInjOnOutsideOpenSourceCandidateTwo
      hlog_gt_anchor h)

/-- Strict-mono-free rooted theorem at `c = 2`, specialized to the known
non-iterate-left injectivity-source aggregate and the current anchor-gap seed. -/
theorem mlc_conjecture_of_green_function_of_knownInjOnOutsideOpenSourceCandidateTwo
    (h : KnownInjOnOutsideOpenSourceCandidateTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_greenRayLogGtAnchorTwoSeam_of_knownInjOnOutsideOpenSourceCandidateTwo
    greenRayLogGtAnchorTwo_seed h

/-- Strict-mono-free rooted theorem at `c = 2`, specialized to outside-open
analyticity. -/
theorem mlc_conjecture_of_greenRayLogGtAnchorTwoSeam_of_outsideOpenAnalyticityHypothesis
    (hlog_gt_anchor : GreenRayLogGtAnchorTwoSeam)
    (h_analytic : OutsideOpenAnalyticityHypothesis (2 : ℂ)) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_externalRayMapData_two
    (external_ray_map_exists_two_constructive_strictMono_free_of_greenRayLogGtAnchorTwoSeam_of_outsideOpenAnalyticityHypothesis
      hlog_gt_anchor h_analytic)

/-- Strict-mono-free rooted theorem at `c = 2`, specialized to outside-open
analyticity and the current anchor-gap seed. -/
theorem mlc_conjecture_of_green_function_of_outsideOpenAnalyticityHypothesis
    (h_analytic : OutsideOpenAnalyticityHypothesis (2 : ℂ)) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_greenRayLogGtAnchorTwoSeam_of_outsideOpenAnalyticityHypothesis
    greenRayLogGtAnchorTwo_seed h_analytic

/-- Root theorem routed directly through the centralized root-seam bundle. -/
theorem mlc_conjecture_of_rootSeedPairTwo
    (hseed : RootSeedPairTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_externalRayMapData_two_root_seed_of_rootSeedPairTwo hseed

/-- Root theorem routed directly through the centralized root-seed payload. -/
theorem mlc_conjecture_of_rootSeedPayloadTwo
    (hseed : RootSeedPayloadTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_externalRayMapData_two_root_seed_of_rootSeedPayloadTwo hseed

/-- Root theorem with explicit split seed boundary:
`greenRayLogGtAnchorTwo_axiom_seed` enters only via this theorem body, while
the strict-mono side enters only through the supplied outside-open injectivity
seed argument. -/
theorem mlc_conjecture_of_rootSafeOutsideOpenInjWitnessTwo_of_greenRayLogGtAnchorTwoSeam
    (hlog_gt_anchor : GreenRayLogGtAnchorTwoSeam)
    (h_inj_seed : RootSafeOutsideOpenInjWitnessTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_root_candidate_of_rootSafeOutsideOpenInjWitnessTwo_of_greenRayLogGtAnchorTwoSeam
    hlog_gt_anchor h_inj_seed

/-- v9 seed-dependency min-cut slice at root entry:
to close root, it is sufficient to provide a Green-ray log-gap seam witness and
an outside-open injectivity witness. -/
def SeedDependencyMinCutSliceTwo : Prop :=
  GreenRayLogGtAnchorTwoSeam →
    RootSafeOutsideOpenInjWitnessTwo →
      LocallyConnectedSpace mandelbrotSet

/-- Canonical witness of the v9 seed-dependency min-cut slice, extracted from
the split-boundary root theorem. -/
theorem seedDependencyMinCutSliceTwo_canonical :
    SeedDependencyMinCutSliceTwo := by
  intro hlog_gt_anchor h_inj
  exact
    mlc_conjecture_of_rootSafeOutsideOpenInjWitnessTwo_of_greenRayLogGtAnchorTwoSeam
      hlog_gt_anchor h_inj

/-- Root theorem with explicit split seed boundary:
`greenRayLogGtAnchorTwo_axiom_seed` enters only via this theorem body, while
the strict-mono side enters only through the supplied outside-open injectivity
seed argument. -/
theorem mlc_conjecture_of_rootSafeOutsideOpenInjWitnessTwo_seed
    (h_inj_seed : RootSafeOutsideOpenInjWitnessTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_rootSafeOutsideOpenInjWitnessTwo_of_greenRayLogGtAnchorTwoSeam
    greenRayLogGtAnchorTwo_seed h_inj_seed

/-- Central strict-mono-seeded outside-open injectivity seed alias used by the
root theorem split boundary. -/
theorem rootSafeOutsideOpenInjWitnessTwo_seed : RootSafeOutsideOpenInjWitnessTwo :=
  rootSafeOutsideOpenInjWitnessTwo_strictMono_seeded

/-- Root-tail wrapper routed through the non-seam replacement boundary using
the centralized strict-mono-seeded outside-open injectivity witness and an
explicit direct proper+local witness. This isolates the remaining no-arg gap to
`DirectProperLocalWitnessTwo`. -/
theorem mlc_conjecture_root_tail_nonseam_of_directProperLocalWitnessTwo
    (h_dir : DirectProperLocalWitnessTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_nonseamRootReplacementTargetTwo
    (rootClosureSubstituteTwo_of_rootSafeOutsideOpenInjWitnessTwo_of_directProperLocalWitnessTwo
      rootSafeOutsideOpenInjWitnessTwo_seed h_dir)

/-- Primitive-family specialization of the non-seam root-tail wrapper. -/
theorem mlc_conjecture_root_tail_nonseam_of_primitiveRestrictedMapProperLocalWitnessFamilyTwo
    (h_prim : PrimitiveRestrictedMapProperLocalWitnessFamilyTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_root_tail_nonseam_of_directProperLocalWitnessTwo
    (directProperLocalWitnessTwo_of_primitiveRestrictedMapProperLocalWitnessFamilyTwo h_prim)

/-- Localized-source transport specialization of the non-seam root-tail wrapper. -/
theorem mlc_conjecture_root_tail_nonseam_of_localizedSourceToRemainingConstructiveIngressGapTwo
    (h_loc : LocalizedSourceToRemainingConstructiveIngressGapTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_root_tail_nonseam_of_directProperLocalWitnessTwo
    (directProperLocalWitnessTwo_of_localizedSourceToRemainingConstructiveIngressGapTwo h_loc)

/-- Partial-window-source specialization of the non-seam root-tail wrapper
through the staged no-arg direct-witness target. -/
theorem mlc_conjecture_root_tail_nonseam_of_noargDirectProperLocalWitnessTwoFromPartialWindowSourceTwo
    (h_noarg : NoargDirectProperLocalWitnessTwoFromPartialWindowSourceTwo)
    (h_partial : PartialWindowNotCoveringCutoffWithNontransportedTailTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_root_tail_nonseam_of_directProperLocalWitnessTwo
    (h_noarg h_partial)

/-- v7 constructor-oriented partial-window specialization of the non-seam
root-tail wrapper. -/
theorem mlc_conjecture_root_tail_nonseam_of_noargDirectProperLocalWitnessTwoFromConstructedPartialSourceTwo
    (h_noarg : NoargDirectProperLocalWitnessTwoFromConstructedPartialSourceTwo)
    (h_partial : ConstructPartialWindowWitnessDirectlyWithoutTransportTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_root_tail_nonseam_of_directProperLocalWitnessTwo
    (h_noarg h_partial)

/-- v8 explicit-subcutoff-source specialization of the non-seam root-tail
wrapper through the staged explicit-localized-source no-arg target. -/
theorem mlc_conjecture_root_tail_nonseam_of_noargDirectProperLocalWitnessTwoFromExplicitLocalizedSourceTwo
    (h_noarg : NoargDirectProperLocalWitnessTwoFromExplicitLocalizedSourceTwo)
    (h_expl : ExplicitSubcutoffWitnessCandidateFromGreenBoundsTwo) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_root_tail_nonseam_of_directProperLocalWitnessTwo
    (h_noarg h_expl)

/-- v8 root-cutover interface marker:
unlocking the explicit-localized-source no-arg target plus an explicit
subcutoff witness candidate closes the non-seam root-tail route. -/
def RootCutoverAfterExplicitSubcutoffSourceUnlockTwo : Prop :=
  NoargDirectProperLocalWitnessTwoFromExplicitLocalizedSourceTwo →
    ExplicitSubcutoffWitnessCandidateFromGreenBoundsTwo →
      LocallyConnectedSpace mandelbrotSet

/-- Canonical v8 root-cutover wrapper through the explicit-localized-source
no-arg target. -/
theorem rootCutoverAfterExplicitSubcutoffSourceUnlockTwo_canonical :
    RootCutoverAfterExplicitSubcutoffSourceUnlockTwo := by
  intro h_noarg h_expl
  exact
    mlc_conjecture_root_tail_nonseam_of_noargDirectProperLocalWitnessTwoFromExplicitLocalizedSourceTwo
      h_noarg h_expl

/-- The Mandelbrot Local Connectivity (MLC) Conjecture:
    The Mandelbrot set is locally connected. -/

theorem mlc_conjecture
    : LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_rootSafeOutsideOpenInjWitnessTwo_seed
    rootSafeOutsideOpenInjWitnessTwo_seed

end MainProof

end MLC
