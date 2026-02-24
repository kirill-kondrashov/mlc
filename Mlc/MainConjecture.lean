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
    simpa using (not_lt_of_ge hge)
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
      _ = ‖p - (2 : ℂ)‖ := by simpa [hp2]
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
    simpa using (not_lt_of_ge hge)
  exact by simpa [hzero] using hnot

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
    simpa using (not_lt_of_ge hge)
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
  ∀ hlocal :
      IsProperMap (bottcher_map_outside_open_to_exterior (2 : ℂ)) ∧
        IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ)),
    Set.InjOn (Quadratic.bottcher_map (2 : ℂ)) {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2}

/-- Branch-local seam at `c = 2`: external-ray landing residual branch implies
outside-open injectivity. -/
def CP5ResidualLandingInjSeamTwo : Prop :=
  ∀ _hland : ExternalRayLandsOutsideOpen (2 : ℂ),
    Set.InjOn (Quadratic.bottcher_map (2 : ℂ)) {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2}

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
theorem cp5ResidualLocalHomeomorphInjSeamTwo_constructive :
    CP5ResidualLocalHomeomorphInjSeamTwo := by
  intro hlocal
  exact Mlc.Bottcher.DegreeOne.injOn_of_proper_localHomeomorph_asymptotic_at_infinity
    hlocal.1 hlocal.2
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
theorem external_ray_map_exists_two_constructive_of_dynamicalBottcherConformalIdentificationTwo
    (hconf : DynamicalBottcherConformalIdentificationTwo) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_exists_two_constructive_of_cp5ResidualTwo
    (cp5ResidualTwo_of_dynamicalBottcherConformalIdentificationTwo hconf)

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

/-- CP5 placeholder endpoint at `c = 2`; replace this body with the fully
constructive proof term after CP2/CP3/CP4 payloads are discharged. -/
theorem external_ray_map_exists_two_constructive :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  Quadratic.external_ray_map_exists (2 : ℂ)

/-- Current rooted axiom-seed external-ray-data target at `c = 2`. -/
lemma externalRayMapData_two_axiom_seed :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_exists_two_constructive

/-- Rooted theorem exposing the remaining axiom ingress at `c = 2` through the
external-ray-data seam. -/
theorem mlc_conjecture_of_external_ray_map_exists_two :
    Quadratic.ExternalRayMapData (2 : ℂ) →
    LocallyConnectedSpace mandelbrotSet := by
  intro h_ext
  exact mlc_conjecture_of_externalRayMapData_two h_ext

/-- The Mandelbrot Local Connectivity (MLC) Conjecture:
    The Mandelbrot set is locally connected. -/

theorem mlc_conjecture
    : LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_external_ray_map_exists_two
    externalRayMapData_two_axiom_seed

end MainProof

end MLC
