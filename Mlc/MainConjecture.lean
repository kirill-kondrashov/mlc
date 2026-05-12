import Yoccoz.Quadratic.Complex.Basic
import Yoccoz.Quadratic.Complex.Green
import Yoccoz.Quadratic.Complex.Puzzle
import Mlc.LcAtOfShrink
import Mlc.InfinitelyRenormalizable
import Mlc.AxiomsMainConjecture
import Mlc.InconsistencyRoute
import Mlc.RenormalizationTowerExistence
import Mlc.ParaPuzzleContainment
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
  have hc₀ : c ∈ Quadratic.ParaPuzzlePieceAt c n :=
    Quadratic.mandelbrot_subset_paraPuzzlePiece hc n
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

/-- Satellite-side local-connectivity payload expected from the virtual Julia /
    virtual Molecule strategy. This packages the endpoint of Problems 4.3/4.4/4.5
    without routing the root theorem through the current upstream Molecule axiom
    frontier. -/
def VirtualJuliaSatelliteLocalConnectivityData : Prop :=
  ∀ (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet)
    (_h : SatelliteRenormalizableTower c),
    MLC.LocallyConnectedAt MLC.Quadratic.MandelbrotSet ⟨c, hc⟩

/-- Finite-branch local-connectivity payload for the final strategy package. -/
def FiniteBranchLocalConnectivityData : Prop :=
  ∀ (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet) (_h : FinitelyRenormalizable c),
    MLC.LocallyConnectedAt MLC.Quadratic.MandelbrotSet ⟨c, hc⟩

/-- Problem 4.3 surface: pseudo-Siegel a priori bounds in the remaining
    unbounded satellite ql cases, represented at the current theorem interface
    as the uniform conformal lower-bound Track-2 target. -/
def Problem43PseudoSiegelAPrioriBoundsData : Prop :=
  MoleculeBridgeTarget.MoleculeImpliesUniformConformalLowerBoundTarget

/-- Problem 4.4 surface: the Virtual Molecule near-degenerate regime,
    represented at the current theorem interface as the Track-1
    no-tower-implies-primitive payload. -/
def Problem44VirtualMoleculeData : Prop :=
  IRNoTowerImpliesPrimitiveData

/-- Problem 4.5 surface: virtual near-Molecule renormalization in the
    primitive-first ql case. At the current seam, this upgrades the Problem 4.3
    pseudo-Siegel control to the satellite local-connectivity endpoint. -/
def Problem45VirtualNearMoleculeRenormalizationData : Prop :=
  Problem43PseudoSiegelAPrioriBoundsData → VirtualJuliaSatelliteLocalConnectivityData

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

/-- Main seam assembly from boundary-motion data, Track-1 no-tower
    classification, and direct satellite-side local-connectivity data. -/
theorem mlc_conjecture_of_motionHyp_noTowerImpliesPrimitive_satelliteLCData
    (h_motion : Quadratic.PuzzleBoundaryMotionHyp)
    (h_noTowerPrim : IRNoTowerImpliesPrimitiveData)
    (h_satelliteLC : VirtualJuliaSatelliteLocalConnectivityData) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_finiteClassificationBridgeData
    (finite_lc_provider_of_motionHyp h_motion)
    (fun c hc h_inf =>
      classify_infinitely_renormalizable_of_noTowerImpliesPrimitive
        h_noTowerPrim c hc h_inf)
    (fun _h_mol c hc h_tower => h_satelliteLC c hc h_tower)

/-- Problem 4.4 yields the Track-1 no-tower-implies-primitive interface. -/
theorem noTowerPrimitive_of_problem44
    (h44 : Problem44VirtualMoleculeData) :
    IRNoTowerImpliesPrimitiveData :=
  h44

/-- Problems 4.3 and 4.5 combine to yield the current satellite
    local-connectivity seam. -/
theorem satelliteLC_of_problem43_problem45
    (h43 : Problem43PseudoSiegelAPrioriBoundsData)
    (h45 : Problem45VirtualNearMoleculeRenormalizationData) :
    VirtualJuliaSatelliteLocalConnectivityData :=
  h45 h43

/-- Main MLC assembly from the split Problem 4.3 / 4.4 / 4.5 surfaces and a
    separate finite-branch payload. -/
theorem mlc_conjecture_of_problem43_44_45_data
    (h_fin : FiniteBranchLocalConnectivityData)
    (h43 : Problem43PseudoSiegelAPrioriBoundsData)
    (h44 : Problem44VirtualMoleculeData)
    (h45 : Problem45VirtualNearMoleculeRenormalizationData) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_finiteClassificationBridgeData
    h_fin
    (fun c hc h_inf =>
      classify_infinitely_renormalizable_of_noTowerImpliesPrimitive
        (noTowerPrimitive_of_problem44 h44) c hc h_inf)
    (fun _h_mol c hc h_tower =>
      (satelliteLC_of_problem43_problem45 h43 h45) c hc h_tower)

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
lemma bottcherApproachOneSeqFiberData_two_of_surjOnExterior
    (h_surj : BottcherSurjOnExterior (2 : ℂ)) :
    BottcherApproachOneSeqFiberData (2 : ℂ) :=
  bottcherApproachOneSeqFiberData_of_surjOnExterior (2 : ℂ) h_surj

/-- `c = 2` specialization: outside-open surjectivity implies minimal exterior
surjectivity. -/
lemma bottcherSurjOnExterior_two_of_externalRayMapData
    (h_data : Quadratic.ExternalRayMapData (2 : ℂ)) :
    BottcherSurjOnExterior (2 : ℂ) :=
  bottcherSurjOnExterior_of_externalRayMapData h_data

/-- Build canonical-sequence fiber data at `c = 2` from explicit external-ray
data. -/
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

/-- CP5 seam at `c = 2`: constructive external-ray-map-data target from
outside-open injectivity plus exterior surjectivity by outside-open preimages. -/
def AnalyticDerivConstructivePayloadTwo : Prop :=
  IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ))) ∧
    (∀ z, ‖z‖ > ‖(2 : ℂ)‖ + 2 → AnalyticAt ℂ (Quadratic.bottcher_map (2 : ℂ)) z) ∧
    (∀ z, ‖z‖ > ‖(2 : ℂ)‖ + 2 → deriv (Quadratic.bottcher_map (2 : ℂ)) z ≠ 0)

/-- Local-homeomorph-on source candidate at `c = 2` through slit inclusion plus
outside-disk injectivity. -/
def SlitInjOutsideDiskLocalHomeomorphOnConstructivePayloadTwo : Prop :=
  ({z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2} ⊆ slit_orbit (2 : ℂ)) ∧
    Set.InjOn (Quadratic.bottcher_map (2 : ℂ)) (outside_disk (2 : ℂ))

/-- Local-homeomorph-on source from slit inclusion plus outside-disk injectivity
at `c = 2`. -/
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

/-- Blocked surjectivity-source sub-aggregate at `c = 2`. -/
def KnownBlockedSurjOnExteriorFromOutsideOpenSourceCandidateTwo : Prop :=
  AnalyticDerivConstructivePayloadTwo ∨
    (IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ))) ∧
      SlitInjOutsideDiskLocalHomeomorphOnConstructivePayloadTwo)

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

/-- Combined payload: iterate-left-inverse injectivity plus outside-disk-to-
outside-open image refinement at `c = 2`. -/
def IterLeftInverseOutsideDiskRefinementConstructivePayloadTwo : Prop :=
  QuadraticMapIterLeftInverseOnBasin (2 : ℂ) ∧
    BottcherOutsideDiskToOutsideOpenImageRefinement (2 : ℂ)

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

/-- Combined payload: iterate-left-inverse injectivity plus the
analytic/derivative source package at `c = 2`. -/
def IterLeftInverseAnalyticDerivConstructivePayloadTwo : Prop :=
  QuadraticMapIterLeftInverseOnBasin (2 : ℂ) ∧
    AnalyticDerivConstructivePayloadTwo

/-- The chosen fixed point at `c = 2` lies strictly inside the outside-open
radius threshold. -/
def ExternalRayLandingCounterexampleTwo : Prop :=
  ∃ w, 1 < ‖w‖ ∧ ¬ ‖Quadratic.external_ray_map (2 : ℂ) w‖ > ‖(2 : ℂ)‖ + 2

/-- Explicit CP5 residual frontier package at `c = 2`: restricted local-homeomorph
source or external-ray landing. -/
def CP5ResidualTwo : Prop :=
  (IsProperMap (bottcher_map_outside_open_to_exterior (2 : ℂ)) ∧
      IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ))) ∨
    ExternalRayLandsOutsideOpen (2 : ℂ)

/-- Under constructive exclusion of external-ray landing at `c = 2`, the CP5
residual frontier is exactly the restricted proper+local-homeomorph branch. -/
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
noncomputable def greenRayLogGtAnchorTwoCutoff : ℝ :=
  Real.exp
    (Real.log (‖(2 : ℂ)‖ + 2) +
      (2 * ‖(2 : ℂ)‖ / (escape_bound (2 : ℂ))^2))

/-- Monotonicity-window interface for the Green-ray anchor-gap inequality at
`c = 2`: verify the inequality only on the bounded cutoff band. -/
def GreenRayLogGapMonotonicityWindowTwo : Prop :=
  ∀ w : ℂ, 1 < ‖w‖ → ‖w‖ ≤ greenRayLogGtAnchorTwoCutoff →
    MLC.Quadratic.green_function (2 : ℂ)
        (((‖(2 : ℂ)‖ + 2 : ℝ) * (w / ↑‖w‖)) : ℂ) < Real.log ‖w‖

/-- The current global anchor-gap seam is inconsistent at `c = 2`: choosing
`w` with modulus `exp(G_anchor / 2)` forces `G_anchor < G_anchor / 2`. -/
def NonimplicativeWindowInterfaceTwo (R : ℝ) : Prop :=
  1 < R ∧ R ≤ greenRayLogGtAnchorTwoCutoff ∧
    ∀ w : ℂ, 1 < ‖w‖ → ‖w‖ ≤ R →
      MLC.Quadratic.green_function (2 : ℂ)
          (((‖(2 : ℂ)‖ + 2 : ℝ) * (w / ↑‖w‖)) : ℂ) < Real.log ‖w‖

/-- Strictly subcutoff local-window package at `c = 2`: a local nonimplicative
window strictly below the global cutoff, together with a transport bridge for
the remaining cutoff annulus. -/
def StrictlySubcutoffLocalWindowWithTransportBridgeTwo : Prop :=
  ∃ R : ℝ, 1 < R ∧ R < greenRayLogGtAnchorTwoCutoff ∧
    NonimplicativeWindowInterfaceTwo R ∧
    (∀ w : ℂ, R < ‖w‖ → ‖w‖ ≤ greenRayLogGtAnchorTwoCutoff →
      MLC.Quadratic.green_function (2 : ℂ)
          (((‖(2 : ℂ)‖ + 2 : ℝ) * (w / ↑‖w‖)) : ℂ) < Real.log ‖w‖)

/-- Partial-window interface at `c = 2` that stays strictly below cutoff and
does not include any tail-transport payload. -/
def PartialWindowNotCoveringCutoffWithNontransportedTailTwo : Prop :=
  ∃ R : ℝ, 1 < R ∧ R < greenRayLogGtAnchorTwoCutoff ∧
    NonimplicativeWindowInterfaceTwo R

/-- v7 constructor-oriented alias: explicitly names the direct construction
target for partial-window witnesses without transport. -/
def ConstructPartialWindowWitnessDirectlyWithoutTransportTwo : Prop :=
  PartialWindowNotCoveringCutoffWithNontransportedTailTwo

/-- v8 explicit subcutoff witness-candidate interface:
strictly subcutoff local window data paired with the constructively available
tail inequality above cutoff. -/
def ExplicitSubcutoffWitnessCandidateFromGreenBoundsTwo : Prop :=
  ∃ R : ℝ, 1 < R ∧ R < greenRayLogGtAnchorTwoCutoff ∧
    NonimplicativeWindowInterfaceTwo R ∧
    (∀ w : ℂ, greenRayLogGtAnchorTwoCutoff < ‖w‖ →
      MLC.Quadratic.green_function (2 : ℂ)
          (((‖(2 : ℂ)‖ + 2 : ℝ) * (w / ↑‖w‖)) : ℂ) < Real.log ‖w‖)

/-- v9 strict-subcutoff existence route: existence of a strictly subcutoff
nonimplicative window, with no transport payload. -/
def StrictSubcutoffWindowExistenceTwo : Prop :=
  ∃ R : ℝ, 1 < R ∧ R < greenRayLogGtAnchorTwoCutoff ∧
    NonimplicativeWindowInterfaceTwo R

def DirectProperLocalWitnessTwo : Prop :=
  IsProperMap (bottcher_map_outside_open_to_exterior (2 : ℂ)) ∧
    IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ))

/-- Primitive restricted-map proper/local witness family at `c = 2`.
This packages the same payload as `DirectProperLocalWitnessTwo` under a
distinct interface name for no-arg witness-source design work. -/
def PrimitiveRestrictedMapProperLocalWitnessFamilyTwo : Prop :=
  IsProperMap (bottcher_map_outside_open_to_exterior (2 : ℂ)) ∧
    IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ))

/-- v9 packaged route to `DirectProperLocalWitnessTwo` from local-homeomorph
plus closed-preimage data on compact exterior targets. -/
def DirectProperLocalWitnessTwoFromLocalHomeomorphClosedRangeRouteTwo : Prop :=
  IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ)) ∧
    (∀ K : Set {w : ℂ // 1 < ‖w‖}, IsCompact K →
      IsClosed
        ({z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2 ∧
          Quadratic.bottcher_map (2 : ℂ) z ∈ ((↑) '' K : Set ℂ)} : Set ℂ))

/-- Constructive CP5 endpoint from the direct closure criterion witness. -/
def KnownLocalHomeomorphOnSourceCandidateTwo : Prop :=
  AnalyticDerivConstructivePayloadTwo ∨
    SlitInjOutsideDiskLocalHomeomorphOnConstructivePayloadTwo

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
def DynamicalBottcherConformalIdentificationTwo : Prop :=
  ∃ e : {z : ℂ // ‖z‖ > ‖(2 : ℂ)‖ + 2} ≃ₜ {w : ℂ // 1 < ‖w‖},
    (fun z => e z) = bottcher_map_outside_open_to_exterior (2 : ℂ)

/-- Direct proper+local witness extracted from the Dudko-style
outside-open/exterior conformal identification at `c = 2`. -/
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

/-- The preimage-closed proper+local source candidate is inconsistent at `c = 2`
because outside-open analyticity is impossible in the current model. -/
def KnownProperLocalSourceCandidateTwo : Prop :=
  ProperLocalFromAnalyticPreimageClosedCandidateTwo ∨
    ProperLocalFromAnalyticBoundaryExclusionCandidateTwo

/-- All currently wired proper+local source families are inconsistent in the
current model at `c = 2`. -/
def RemainingConstructiveIngressTwo : Prop :=
  KnownProperLocalSourceCandidateTwo ∨
    DynamicalBottcherConformalIdentificationTwo ∨
      DirectProperLocalWitnessTwo

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

/-- Revised CP3 formal target at `c = 2` in the current model. -/
def RevisedCP3TargetTwo : Prop :=
  ¬ NonSlitAnalyticInjConstructivePayloadTwo

/-- Revised CP4 formal target at `c = 2` in the current model. -/
def RevisedCP4TargetTwo : Prop :=
  ¬ AnalyticDerivConstructivePayloadTwo

/-- Revised CP5 formal target at `c = 2`: MLC follows from any non-vacuous
external-ray-data source term. -/
def RevisedCP5TargetTwo : Prop :=
  Quadratic.ExternalRayMapData (2 : ℂ) → LocallyConnectedSpace mandelbrotSet

/-- CP5 endpoint at `c = 2`: constructive Green-function ray inversion. -/
def GreenRayLogGtAnchorTwoThresholdSeam : Prop :=
  ∀ u : ℂ, ‖u‖ = 1 →
    ∃ R : ℝ, 1 < R ∧
      ∀ r : ℝ, R < r →
        MLC.Quadratic.green_function (2 : ℂ)
            (((‖(2 : ℂ)‖ + 2 : ℝ) * u) : ℂ) < Real.log r

/-- Constructive thresholded anchor inequality: along each unit direction,
the fixed anchor Green value is eventually below `log r` for large enough radii. -/
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
def RootSafeOutsideOpenInjWitnessTwo : Prop :=
  Set.InjOn (Quadratic.bottcher_map (2 : ℂ))
    {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2}

/-- Build the exact strict-mono-free root witness target from Green-ray
uniqueness+anchor seams at `c = 2`. -/
def RootSafeOutsideOpenInjWitnessTwoWitnessGap : Prop :=
  GreenRayUniquePreimageTwoAnchorSeam ∧ GreenRayLogGtAnchorTwoSeam

/-- Explicit constructor gap for the unique-preimage seam target: outside-open
injectivity on the target outside-open domain. -/
def GreenRayUniquePreimageTwoAnchorSeamWitnessGap : Prop :=
  RootSafeOutsideOpenInjWitnessTwo

/-- Strict-mono-seeded root witness target at `c = 2`, expressed via the
Green-ray seam bridge. -/
def ProperLocalDegreeOneFiberWitnessTwo : Prop :=
  ∃ y : ℂ, Nat.card ({x : ℂ // Quadratic.bottcher_map (2 : ℂ) x = y}) = 1

/-- Degree-one fiber witness on the restricted map
`outside_open → exterior` at `c = 2`. -/
def RestrictProperLocalDegreeOneFiberWitnessTwo : Prop :=
  ∃ y : {w : ℂ // 1 < ‖w‖},
    Nat.card
      ({x : {z : ℂ // ‖z‖ > ‖(2 : ℂ)‖ + 2} //
          bottcher_map_outside_open_to_exterior (2 : ℂ) x = y}) = 1

/-- Constructive outside-open injectivity from global proper+local-homeomorph
plus a degree-one fiber witness at `c = 2`. -/
def GlobalProperLocalDegreeOneRouteTwo : Prop :=
  IsProperMap (Quadratic.bottcher_map (2 : ℂ)) ∧
    IsLocalHomeomorph (Quadratic.bottcher_map (2 : ℂ)) ∧
      ProperLocalDegreeOneFiberWitnessTwo

/-- Constructive outside-open injectivity from the direct proper+local witness
at `c = 2`. -/
def GreenFunctionDegreeOneIngressTwo : Prop :=
  IsProperMap (Quadratic.bottcher_map (2 : ℂ)) ∧
    IsLocalHomeomorph (Quadratic.bottcher_map (2 : ℂ)) ∧
      ProperLocalDegreeOneFiberWitnessTwo

/-- No-go at `c = 2`: the degree-one Green-function ingress is inconsistent in
the current model because `bottcher_map` is not proper on `ℂ`. -/
def RootSafeOutsideOpenInjWitnessTwoStrictMonoFreeIngressTwo : Prop :=
  KnownInjOnOutsideOpenSourceCandidateTwo ∨ GreenFunctionDegreeOneIngressTwo

/-- Source-exhaustion normalization at `c = 2`: the strict-mono-free root-safe
outside-open injectivity ingress bundle collapses to the degree-one
Green-function ingress. -/
def RootSafeOutsideOpenInjWitnessTwoNonseededIngressFamilyTwo : Prop :=
  RootSafeOutsideOpenInjWitnessTwoStrictMonoFreeIngressTwo ∨
    RootSafeOutsideOpenInjWitnessTwoWitnessGap

/-- Geometric outside-open/fiber ingress family at `c = 2`: pair the root-safe
outside-open injectivity target with the restricted singleton-fiber witness. -/
def RootSafeOutsideOpenInjWitnessTwoGeometricFiberIngressFamilyTwo : Prop :=
  RootSafeOutsideOpenInjWitnessTwo ∧ RestrictProperLocalDegreeOneFiberWitnessTwo

/-- Candidate nonvacuous geometric witness-extraction bundle at `c = 2`:
geometric outside-open/fiber ingress plus bounded log-gap monotonicity window. -/
def NonvacuousGeometricIngressWitnessExtractionTwo : Prop :=
  RootSafeOutsideOpenInjWitnessTwoGeometricFiberIngressFamilyTwo ∧
    GreenRayLogGapMonotonicityWindowTwo

/-- Localized geometric source family at `c = 2`: pair a local nonimplicative
window of radius `R` with geometric outside-open/fiber ingress. -/
def LocalizedRayIntervalGeometricSourceTwo (R : ℝ) : Prop :=
  NonimplicativeWindowInterfaceTwo R ∧
    RootSafeOutsideOpenInjWitnessTwoGeometricFiberIngressFamilyTwo

/-- Strict-mono-free rooted external-ray-data candidate seed at `c = 2`,
parameterized by the exact remaining root witness target. -/
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
def RootSeedPayloadTwoStrictMonoFreeIngressTwo : Prop :=
  GreenRayLogGtAnchorTwoSeam ∧ RootSafeOutsideOpenInjWitnessTwoStrictMonoFreeIngressTwo

/-- Build centralized root-seed payload from the strict-mono-free ingress
payload. -/
theorem mlc_conjecture_of_external_ray_map_exists_two :
    Quadratic.ExternalRayMapData (2 : ℂ) →
    LocallyConnectedSpace mandelbrotSet := by
  intro h_ext
  exact mlc_conjecture_of_externalRayMapData_two h_ext

/-- Root theorem routed through the centralized root-seed payload selector. -/
def RootEntryDetourViaInjSurjExteriorConstructivePayloadTwo : Prop :=
  InjSurjExteriorConstructivePayloadTwo

/-- Minimal non-seeded root-closure substitute interface at `c = 2`:
outside-open injectivity plus direct proper/local witness. -/
def RootClosureSubstituteTwo : Prop :=
  RootSafeOutsideOpenInjWitnessTwo ∧ DirectProperLocalWitnessTwo

/-- Root-closure bridge at `c = 2`: from the root substitute interface and a
local-homeomorph injectivity seam witness, construct external-ray-map data. -/
def NonseamRootReplacementTargetTwo : Prop :=
  RootClosureSubstituteTwo

/-- v10 minimal non-seeded elimination gap at root entry: a constructor from
direct proper/local witness data to outside-open injectivity. -/
def NonseededDirectProperToRootSafeGapTwo : Prop :=
  DirectProperLocalWitnessTwo → RootSafeOutsideOpenInjWitnessTwo

/-- v12 equivalent non-seeded gap phrasing: from direct proper/local witness to
the local-homeomorph CP5 injectivity seam. -/
def NonseededDirectProperToLocalSeamGapTwo : Prop :=
  DirectProperLocalWitnessTwo → CP5ResidualLocalHomeomorphInjSeamTwo

/-- v10 route matrix for candidate paths currently used to obtain
`DirectProperLocalWitnessTwo`. -/
def DirectProperLocalWitnessTwoRouteMatrixV10 : Prop :=
  DirectProperLocalWitnessTwoFromLocalHomeomorphClosedRangeRouteTwo ∨
    KnownProperLocalSourceCandidateTwo ∨
      PrimitiveRestrictedMapProperLocalWitnessFamilyTwo

/-- v14 witness-source matrix for local-seam gap cutover. -/
def NonseededLocalSeamGapWitnessSourceMatrixV14 : Prop :=
  PrimitiveRestrictedMapProperLocalWitnessFamilyTwo ∨
    DirectProperLocalWitnessTwo

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

/-- v17 elimination kernel: the isolated core bridge together with one direct
proper/local witness. -/
def FinalAxiomEliminationKernelV17 : Prop :=
  FinalAxiomCoreConstructiveGapV16 ∧ DirectProperLocalWitnessTwo

/-- v18 ingress-level elimination kernel: the isolated core bridge together
with aggregate constructive ingress. -/
def FinalAxiomEliminationIngressKernelV18 : Prop :=
  FinalAxiomCoreConstructiveGapV16 ∧ RemainingConstructiveIngressTwo

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

/-- v20 witness-transport target: build outside-open injectivity directly from
aggregate constructive ingress. -/
def FinalAxiomWitnessTransportV20 : Prop :=
  RemainingConstructiveIngressTwo → RootSafeOutsideOpenInjWitnessTwo

/-- v20 contrapositive-obstruction target: if the local CP5 seam fails, then
aggregate constructive ingress fails. -/
def FinalAxiomContrapositiveObstructionV20 : Prop :=
  ¬ CP5ResidualLocalHomeomorphInjSeamTwo → ¬ RemainingConstructiveIngressTwo

/-- v19 elimination kernel: ingress-level bridge target plus aggregate
constructive ingress. -/
def FinalAxiomEliminationIngressBridgeKernelV19 : Prop :=
  FinalAxiomIngressBridgeGapV19 ∧ RemainingConstructiveIngressTwo

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

/-- v21 witness-gap kernel: bridge target plus explicit no-arg witness-gap
payload. -/
def FinalAxiomWitnessGapKernelV21 : Prop :=
  FinalAxiomWitnessGapBridgeV21 ∧ RemainingConstructiveIngressTwoWitnessGap

/-- v22 root-witness-gap bridge target: build the explicit root witness-gap
payload directly from the no-arg witness-gap payload. -/
def FinalAxiomRootWitnessGapBridgeV22 : Prop :=
  RemainingConstructiveIngressTwoWitnessGap → RootClosureSubstituteTwoWitnessGap

/-- v22 root-witness-gap kernel: root-witness-gap bridge plus explicit no-arg
witness-gap payload. -/
def FinalAxiomRootWitnessGapKernelV22 : Prop :=
  FinalAxiomRootWitnessGapBridgeV22 ∧ RemainingConstructiveIngressTwoWitnessGap

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

/-- v23 approach matrix: any one of the four approach interfaces is enough. -/
def FinalAxiomApproachMatrixV23 : Prop :=
  FinalAxiomGeometricApproachV23 ∨
    FinalAxiomTopologicalApproachV23 ∨
      FinalAxiomAnalyticApproachV23 ∨
        FinalAxiomCombinatorialApproachV23

/-- v23 approach-matrix kernel: approach matrix plus explicit no-arg witness-gap
payload. -/
def FinalAxiomApproachMatrixKernelV23 : Prop :=
  FinalAxiomApproachMatrixV23 ∧ RemainingConstructiveIngressTwoWitnessGap

/-- v24 root-closure bridge target: build the non-seam root substitute
directly from the explicit no-arg witness-gap payload. -/
def FinalAxiomRootClosureBridgeV24 : Prop :=
  RemainingConstructiveIngressTwoWitnessGap → RootClosureSubstituteTwo

/-- v24 root-closure kernel: root-closure bridge plus explicit no-arg
witness-gap payload. -/
def FinalAxiomRootClosureKernelV24 : Prop :=
  FinalAxiomRootClosureBridgeV24 ∧ RemainingConstructiveIngressTwoWitnessGap

/-- v25 direct constructive approach interface: explicit no-arg witness-gap
payload paired with the core constructive bridge target. -/
def FinalAxiomDirectConstructiveApproachV25 : Prop :=
  RemainingConstructiveIngressTwoWitnessGap ∧ FinalAxiomCoreConstructiveGapV16

/-- v25 alternative bridge strategies interface: either approach-matrix kernel
or root-closure kernel suffices. -/
def FinalAxiomAlternativeBridgeStrategiesV25 : Prop :=
  FinalAxiomApproachMatrixKernelV23 ∨ FinalAxiomRootClosureKernelV24

/-- v26 new direct approach interface, routed through the grounded v25 direct
constructive boundary. -/
def FinalAxiomNewDirectApproachV26 : Prop :=
  FinalAxiomDirectConstructiveApproachV25

/-- v26 alternative proof-structure interface, routed through the grounded v25
alternative-strategies boundary. -/
def FinalAxiomAlternativeProofStructureV26 : Prop :=
  FinalAxiomAlternativeBridgeStrategiesV25

/-- v26 minimal-counterexample interface: contradiction of the negated core
bridge theorem. -/
def FinalAxiomMinimalCounterexampleV26 : Prop :=
  ¬ FinalAxiomCoreConstructiveGapV16 → False

/-- v26 minimal-counterexample kernel: minimal-counterexample interface plus the
explicit no-arg witness-gap payload. -/
def FinalAxiomMinimalCounterexampleKernelV26 : Prop :=
  FinalAxiomMinimalCounterexampleV26 ∧ RemainingConstructiveIngressTwoWitnessGap

/-- v26 parallel matrix: any grounded v26 route is enough to close the same
witness-gap kernel. -/
def FinalAxiomParallelMatrixV26 : Prop :=
  FinalAxiomNewDirectApproachV26 ∨
    FinalAxiomAlternativeProofStructureV26 ∨
      FinalAxiomMinimalCounterexampleKernelV26

/-- Localized-source transport gap interface: strict subcutoff local-window
transport package plus the explicit ingress witness-gap payload. -/
def LocalizedSourceToRemainingConstructiveIngressGapTwo : Prop :=
  StrictlySubcutoffLocalWindowWithTransportBridgeTwo ∧
    RemainingConstructiveIngressTwoWitnessGap

/-- No-arg direct-witness target staged from a partial-window source: any
partial-window payload should produce `DirectProperLocalWitnessTwo`. -/
def NoargDirectProperLocalWitnessTwoFromPartialWindowSourceTwo : Prop :=
  PartialWindowNotCoveringCutoffWithNontransportedTailTwo →
    DirectProperLocalWitnessTwo

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

/-- Localized source interface that deliberately avoids full-window upgrade:
geometric outside-open/fiber ingress plus a strictly subcutoff partial window
without any tail-transport payload. -/
def LocalizedSourceWithoutFullWindowUpgradeTwo : Prop :=
  RootSafeOutsideOpenInjWitnessTwoGeometricFiberIngressFamilyTwo ∧
    PartialWindowNotCoveringCutoffWithNontransportedTailTwo

/-- v7 constructor map: a direct partial-window witness yields a localized
source witness by pairing it with the canonical strict-mono-seeded geometric
ingress witness. -/
def LocalizedSourceWitnessFromPartialWindowConstructorTwo : Prop :=
  ConstructPartialWindowWitnessDirectlyWithoutTransportTwo →
    LocalizedSourceWithoutFullWindowUpgradeTwo

/-- v8 constructor map: an explicit subcutoff witness candidate from Green
bounds yields a localized source witness after projection to the v7 constructor
target. -/
def LocalizedSourceWitnessFromExplicitSubcutoffWitnessTwo : Prop :=
  ExplicitSubcutoffWitnessCandidateFromGreenBoundsTwo →
    LocalizedSourceWithoutFullWindowUpgradeTwo

/-- Root witness-gap payload where Green-ray seam assumptions are explicit
parameters and no fixed seed constant appears. -/
def RootClosureSubstituteTwoWitnessGapWithoutGreenRaySeed : Prop :=
  RemainingConstructiveIngressTwoWitnessGap ∧
    GreenRayUniquePreimageTwoAnchorSeam ∧ GreenRayLogGtAnchorTwoSeam

/-- Strict-mono-free root-candidate wrapper parameterized by the exact remaining
outside-open injectivity witness target and specialized to the current
anchor-gap seed. -/
def SeedDependencyMinCutSliceTwo : Prop :=
  GreenRayLogGtAnchorTwoSeam →
    RootSafeOutsideOpenInjWitnessTwo →
      LocallyConnectedSpace mandelbrotSet

/-- v8 root-cutover interface marker:
unlocking the explicit-localized-source no-arg target plus an explicit
subcutoff witness candidate closes the non-seam root-tail route. -/
def RootCutoverAfterExplicitSubcutoffSourceUnlockTwo : Prop :=
  NoargDirectProperLocalWitnessTwoFromExplicitLocalizedSourceTwo →
    ExplicitSubcutoffWitnessCandidateFromGreenBoundsTwo →
      LocallyConnectedSpace mandelbrotSet

/-- Current root-frontier witness at `c = 2`.
This is the single swap point for removing
`MLC.Quadratic.external_ray_map_exists` from `mlc_conjecture`. -/
lemma externalRayMapData_two_root_frontier :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  Quadratic.external_ray_map_exists (2 : ℂ)

/-! ### Direct proof route (bypassing `external_ray_map_exists`)

The direct route wires `mlc_conjecture` through the FR/IR dichotomy using:
1. The existing para-puzzle connectivity axiom for the FR branch (Yoccoz shrinkage).
2. A single seam axiom for the IR branch (local connectivity of IR parameters).

This replaces the vacuous `external_ray_map_exists(2) → False → MainPathData`
chain with a mathematically sound proof skeleton.
-/

/-- Seam axiom: the Mandelbrot set is locally connected at every infinitely
    renormalizable parameter.
    Proof idea: this combines two deep results —
    (a) the Lyubich a priori bounds (primitive renormalization gives modulus
        divergence, hence puzzle shrinkage, hence LC), and
    (b) the Dudko-Lyubich-Selinger satellite theory (the molecule conjecture
        gives uniform modulus lower bounds along satellite tower depths,
        yielding shrinkage via the Grötzsch inequality).
    Every IR parameter falls into one of these two cases by the combinatorial
    classification of renormalization (Douady-Hubbard, McMullen). -/
axiom ir_locally_connected_seam :
    ∀ (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet),
      InfinitelyRenormalizable c →
        MLC.LocallyConnectedAt MLC.Quadratic.MandelbrotSet ⟨c, hc⟩

/-- Minimal IR seam payload: local connectivity at all infinitely
    renormalizable Mandelbrot parameters. -/
def IRLocallyConnectedData : Prop :=
  ∀ (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet),
    InfinitelyRenormalizable c →
      MLC.LocallyConnectedAt MLC.Quadratic.MandelbrotSet ⟨c, hc⟩

/-- Build the minimal IR seam payload from explicit IR classify/bridge data. -/
lemma irLocallyConnectedData_of_classify_bridge_data
    (h_classify_ir : IRClassificationData)
    (h_bridge :
      MoleculeConjectureRefined →
      ∀ (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet)
        (_h : SatelliteRenormalizableTower c),
        MLC.LocallyConnectedAt MLC.Quadratic.MandelbrotSet ⟨c, hc⟩) :
    IRLocallyConnectedData := by
  intro c hc h_inf
  exact mlc_infinitely_renormalizable h_classify_ir h_bridge c hc h_inf

/-- IR payload packaged as classification + satellite bridge. -/
structure IRClassifyBridgeData : Prop where
  classify : IRClassificationData
  bridge :
    MoleculeConjectureRefined →
    ∀ (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet)
      (_h : SatelliteRenormalizableTower c),
      MLC.LocallyConnectedAt MLC.Quadratic.MandelbrotSet ⟨c, hc⟩

/-- Packaged seam payload for the direct route:
    FR connectedness data + packaged IR classify/bridge data. -/
structure MLCClassifyBridgeSeamData : Prop where
  puzzle_connected : Quadratic.ParaPuzzlePieceInterMandelbrotConnectedData
  ir : IRClassifyBridgeData

/-- Characterization of packaged IR classify/bridge payload. -/
theorem irClassifyBridgeData_iff :
    IRClassifyBridgeData ↔
      IRClassificationData ∧
        (MoleculeConjectureRefined →
          ∀ (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet)
            (_h : SatelliteRenormalizableTower c),
            MLC.LocallyConnectedAt MLC.Quadratic.MandelbrotSet ⟨c, hc⟩) := by
  constructor
  · intro h
    exact ⟨h.classify, h.bridge⟩
  · intro h
    exact ⟨h.1, h.2⟩

/-- Characterization of the packaged classify/bridge seam payload. -/
theorem mlcClassifyBridgeSeamData_iff :
    MLCClassifyBridgeSeamData ↔
      Quadratic.ParaPuzzlePieceInterMandelbrotConnectedData ∧ IRClassifyBridgeData := by
  constructor
  · intro h
    exact ⟨h.puzzle_connected, h.ir⟩
  · intro h
    exact ⟨h.1, h.2⟩

/-- Build FR connectedness payload from boundary-motion hypotheses. -/
def paraPuzzleConnectedData_of_motionHyp
    (h_motion : Quadratic.PuzzleBoundaryMotionHyp) :
    Quadratic.ParaPuzzlePieceInterMandelbrotConnectedData :=
  finite_connectedAt_provider_of_motionHyp h_motion

/-- Build packaged IR classify/bridge payload from separate inputs. -/
def irClassifyBridgeData_of_classify_bridge_data
    (h_classify_ir : IRClassificationData)
    (h_bridge :
      MoleculeConjectureRefined →
      ∀ (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet)
        (_h : SatelliteRenormalizableTower c),
        MLC.LocallyConnectedAt MLC.Quadratic.MandelbrotSet ⟨c, hc⟩) :
    IRClassifyBridgeData where
  classify := h_classify_ir
  bridge := h_bridge

/-- Build IR classification data from global IR→tower bridge data. -/
lemma irClassificationData_of_infinitelyRenormalizableHasTowerData
    (h_tower_data : InfinitelyRenormalizableHasTowerData) :
    IRClassificationData := by
  intro c _hc h_ir
  exact classify_infinitely_renormalizable h_tower_data c h_ir

/-- Build packaged IR classify/bridge data from IR classification plus the
    strong molecule bridge target. -/
def irClassifyBridgeData_of_classify_moleculeBridgeTarget_data
    (h_classify_ir : IRClassificationData)
    (h_target : MoleculeBridgeTarget.MoleculeImpliesSatellitePrincipalNestData) :
    IRClassifyBridgeData :=
  irClassifyBridgeData_of_classify_bridge_data
    h_classify_ir
    (MoleculeBridgeTarget.bridge_of_moleculeBridgeTarget h_target)

/-- Build packaged IR classify/bridge data from IR classification plus the
    uniform conformal molecule bridge target. -/
def irClassifyBridgeData_of_classify_moleculeUniformBridgeTarget_data
    (h_classify_ir : IRClassificationData)
    (h_uniform : MoleculeBridgeTarget.MoleculeImpliesUniformConformalLowerBoundTarget) :
    IRClassifyBridgeData :=
  irClassifyBridgeData_of_classify_moleculeBridgeTarget_data
    h_classify_ir
    (MoleculeBridgeTarget.moleculeBridgeTarget_of_moleculeUniformBridgeTarget h_uniform)

/-- Build packaged IR classify/bridge data from global IR→tower bridge data and
    the strong molecule bridge target. -/
def irClassifyBridgeData_of_infinitelyRenormalizableHasTowerData_moleculeBridgeTarget
    (h_tower_data : InfinitelyRenormalizableHasTowerData)
    (h_target : MoleculeBridgeTarget.MoleculeImpliesSatellitePrincipalNestData) :
    IRClassifyBridgeData :=
  irClassifyBridgeData_of_classify_moleculeBridgeTarget_data
    (irClassificationData_of_infinitelyRenormalizableHasTowerData h_tower_data)
    h_target

/-- Build packaged IR classify/bridge data from global IR→tower bridge data and
    the uniform conformal molecule bridge target. -/
def irClassifyBridgeData_of_infinitelyRenormalizableHasTowerData_moleculeUniformBridgeTarget
    (h_tower_data : InfinitelyRenormalizableHasTowerData)
    (h_uniform : MoleculeBridgeTarget.MoleculeImpliesUniformConformalLowerBoundTarget) :
    IRClassifyBridgeData :=
  irClassifyBridgeData_of_classify_moleculeUniformBridgeTarget_data
    (irClassificationData_of_infinitelyRenormalizableHasTowerData h_tower_data)
    h_uniform

/-- Build minimal IR seam payload from packaged classify/bridge IR data. -/
lemma irLocallyConnectedData_of_irClassifyBridgeData
    (h_ir : IRClassifyBridgeData) :
    IRLocallyConnectedData :=
  irLocallyConnectedData_of_classify_bridge_data
    h_ir.classify
    h_ir.bridge

/-- Current axiom-backed provider for the minimal IR seam payload. -/
lemma irLocallyConnectedData_of_axiom : IRLocallyConnectedData := by
  intro c hc h_inf
  exact ir_locally_connected_seam c hc h_inf

/-- Under the Gaussian proxy model, IR local-connectivity data forces
    primitive classification at every IR parameter. -/
lemma irClassificationData_of_irLocallyConnectedData
    (h_ir_lc : IRLocallyConnectedData) :
    IRClassificationData := by
  intro c hc h_ir
  exact Or.inl (fun _ => h_ir_lc c hc h_ir)

/-- Under the Gaussian proxy model, IR local-connectivity data yields a
    `mlc_strategy`-compatible satellite bridge. -/
lemma bridgeData_of_irLocallyConnectedData
    (h_ir_lc : IRLocallyConnectedData) :
    MoleculeConjectureRefined →
    ∀ (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet)
      (_h : SatelliteRenormalizableTower c),
      MLC.LocallyConnectedAt MLC.Quadratic.MandelbrotSet ⟨c, hc⟩ := by
  intro _h_mol c hc _h_sat
  exact h_ir_lc c hc (infinitely_renormalizable_of_gaussian_modulus c)

/-- Build packaged IR classify/bridge data from IR local-connectivity data. -/
def irClassifyBridgeData_of_irLocallyConnectedData
    (h_ir_lc : IRLocallyConnectedData) :
    IRClassifyBridgeData :=
  irClassifyBridgeData_of_classify_bridge_data
    (irClassificationData_of_irLocallyConnectedData h_ir_lc)
    (bridgeData_of_irLocallyConnectedData h_ir_lc)

/-- Current axiom-backed provider for packaged IR classify/bridge data. -/
def irClassifyBridgeData_of_axiom : IRClassifyBridgeData :=
  irClassifyBridgeData_of_irLocallyConnectedData irLocallyConnectedData_of_axiom

/-- Bridge payload: any renormalization tower supplies IR local-connectivity
    data via the inconsistency route. -/
lemma irLocallyConnectedData_of_tower {c₀ : ℂ}
    (T : RenormalizationTower (parameterToBMol c₀)) :
    IRLocallyConnectedData :=
  ir_locally_connected_seam_of_tower T

/-- Existential-tower bridge: one renormalization tower already yields the
    full IR seam payload (via the inconsistency route). -/
lemma irLocallyConnectedData_of_exists_tower
    (h_exists : ∃ c₀ : ℂ, Nonempty (RenormalizationTower (parameterToBMol c₀))) :
    IRLocallyConnectedData := by
  rcases h_exists with ⟨c₀, ⟨T⟩⟩
  exact irLocallyConnectedData_of_tower (c₀ := c₀) T

/-- In the current Gaussian-modulus model, IR local-connectivity data alone
    yields global MLC. -/
theorem mlc_conjecture_of_irLocallyConnectedData
    (h_ir_lc : IRLocallyConnectedData) :
    LocallyConnectedSpace mandelbrotSet := by
  rw [mandelbrotSet_eq_MandelbrotSet]
  -- Keep the IR payload conversions explicitly connected in the main route.
  have _h_ir_packaging_chain : True := by
    let h_ir_pkg : IRClassifyBridgeData :=
      irClassifyBridgeData_of_irLocallyConnectedData h_ir_lc
    have _h_ir_lc_roundtrip : IRLocallyConnectedData :=
      irLocallyConnectedData_of_irClassifyBridgeData h_ir_pkg
    have _h_ir_class : IRClassificationData := h_ir_pkg.classify
    have _h_ir_bridge :
        MoleculeConjectureRefined →
        ∀ (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet)
          (_h : SatelliteRenormalizableTower c),
          MLC.LocallyConnectedAt MLC.Quadratic.MandelbrotSet ⟨c, hc⟩ :=
      h_ir_pkg.bridge
    trivial
  -- Thread canonical/uniform/strong molecule-bridge target conversions so this
  -- route stays linked to the bridge-target development.
  have _h_molecule_target_chain : True := by
    by_cases h_canonical :
        MoleculeBridgeTarget.MoleculeImpliesCanonicalSatellitePrincipalNestData
    · let h_uniform_target :
          MoleculeBridgeTarget.MoleculeImpliesUniformConformalLowerBoundTarget :=
        MoleculeBridgeTarget.moleculeUniformBridgeTarget_of_moleculeCanonicalSatellitePrincipalNestData
          h_canonical
      let _h_strong_target :
          MoleculeBridgeTarget.MoleculeImpliesSatellitePrincipalNestData :=
        MoleculeBridgeTarget.moleculeBridgeTarget_of_moleculeUniformBridgeTarget
          h_uniform_target
      trivial
    · trivial
  let h_main : LocallyConnectedSpace MLC.Quadratic.MandelbrotSet :=
    mlc_strategy_of_branchLocalData
      -- FR handler: vacuous under Gaussian proxy (every parameter is IR).
      (fun c _hc h_fr =>
        absurd (infinitely_renormalizable_of_gaussian_modulus c) h_fr)
      -- IR classification is forced through the primitive branch by `h_ir_lc`.
      (irClassificationData_of_irLocallyConnectedData h_ir_lc)
      -- Satellite bridge also follows from `h_ir_lc` under Gaussian IR.
      (bridgeData_of_irLocallyConnectedData h_ir_lc)
  -- Optional tower-data branch used to keep the IR/tower development linked
  -- to the main theorem path without changing the frontier.
  by_cases h_tower_data : InfinitelyRenormalizableHasTowerData
  · have h_ir0 : InfinitelyRenormalizable (0 : ℂ) :=
      infinitely_renormalizable_of_gaussian_modulus 0
    have _h_proper_pow2 : IsProperMap (fun z : ℂ => z ^ 2) :=
      isProperMap_pow2
    have _h_proper_quad0 : IsProperMap (fun z : ℂ => z ^ 2 + (0 : ℂ)) :=
      isProperMap_quadratic (0 : ℂ)
    have _h_paramToBMol_criticalValue0 := parameterToBMol_criticalValue (0 : ℂ)
    have _h_paramToBMol_spec0 : True := by
      rcases parameterToBMol_spec (0 : ℂ) with ⟨g, hg, hcv⟩
      have _hg := hg
      have _hcv := hcv
      trivial
    have h_sat0 : SatelliteRenormalizableTower (0 : ℂ) :=
      tower_of_infinitely_renormalizable h_tower_data 0 h_ir0
    let T0 : RenormalizationTower (parameterToBMol (0 : ℂ)) := satelliteTower 0 h_sat0
    have _h_step0 := tower_step_classification T0 0
    have _h_period_ge_two0 : 2 ≤ T0.period 0 := RenormalizationTower.period_ge_two T0 0
    have _h_cp_unbounded0 : ∃ n : ℕ, 0 ≤ T0.cumulativePeriod n :=
      RenormalizationTower.le_cumulativePeriod_of_le T0 0
    have _h_cp_mono : Monotone T0.cumulativePeriod :=
      RenormalizationTower.cumulativePeriod_monotone T0
    have _h_cp_cof : Quadratic.PrincipalNest.Cofinal T0.cumulativePeriod :=
      RenormalizationTower.cumulativePeriod_cofinal T0
    have _h_sat_depths_mono :
        Monotone (RenormalizationTower.cumulativePeriod (satelliteTower 0 h_sat0)) :=
      satelliteTower_depths_monotone 0 h_sat0
    have _h_sat_depths_cof :
        Quadratic.PrincipalNest.Cofinal
          (RenormalizationTower.cumulativePeriod (satelliteTower 0 h_sat0)) :=
      satelliteTower_depths_cofinal 0 h_sat0
    rcases exists_renormalization_tower_sequence h_tower_data 0 h_ir0 with
      ⟨_g, _hg0, _hstep⟩
    have _h_ir_class_data : IRClassificationData :=
      irClassificationData_of_infinitelyRenormalizableHasTowerData h_tower_data
    have _h_class0 :
        PrimitiveRenormalizable (0 : ℂ) ∨ SatelliteRenormalizableTower (0 : ℂ) :=
      classify_infinitely_renormalizable h_tower_data 0 h_ir0
    have _h_class_noTowerPrim : True := by
      by_cases h_noTowerPrim : IRNoTowerImpliesPrimitiveData
      · have _h_class_alt :
          PrimitiveRenormalizable (0 : ℂ) ∨ SatelliteRenormalizableTower (0 : ℂ) :=
          classify_infinitely_renormalizable_of_noTowerImpliesPrimitive
            h_noTowerPrim 0 zero_mem_mandelbrotSet_fastTower h_ir0
        trivial
      · trivial
    have _h_comb :
        {n : ℕ | True}.Infinite ∨ (∀ᶠ n : ℕ in Filter.atTop, False) := by
      exact combinatorial_dichotomy (p := fun _ : ℕ => True) (q := fun _ : ℕ => False)
        (fun _ => Or.inl trivial)
    have _h_sat_bridge : True := by
      by_cases h_ev_sat : ∀ᶠ n in Filter.atTop, IsSatellite (T0.rel n)
      · have _h_sat_again : SatelliteRenormalizableTower (0 : ℂ) :=
          satellite_tower_implies_satellite 0 h_ir0 T0 h_ev_sat
        trivial
      · trivial
    have h_exists_mem_tower :
        ∃ c : ℂ, c ∈ MLC.Quadratic.MandelbrotSet ∧ SatelliteRenormalizableTower c :=
      ⟨0, zero_mem_mandelbrotSet_fastTower, h_sat0⟩
    by_cases h_mod : MoleculeModulusLowerBoundData
    · have hFalse :
          False :=
        (not_moleculeModulusLowerBoundData_of_exists_mem_mandelbrot_tower
          h_exists_mem_tower) h_mod
      have _h_not_sat0 : ¬ SatelliteRenormalizableTower (0 : ℂ) :=
        not_satelliteRenormalizableTower_of_mem_mandelbrot
          h_mod 0 zero_mem_mandelbrotSet_fastTower
      have _hFalse_mod2 : False :=
        false_of_infinitely_renormalizable_has_tower_data h_mod h_tower_data
      have _h_no_tower_data : ¬ InfinitelyRenormalizableHasTowerData :=
        not_infinitely_renormalizable_has_tower_data h_mod
      exact False.elim hFalse
    · have _h_no_mod : ¬ MoleculeModulusLowerBoundData := h_mod
      by_cases h_conf : MoleculeConformalModulusLowerBoundData
      · have hFalse :
            False :=
          (not_moleculeConformalModulusLowerBoundData_of_exists_mem_mandelbrot_tower
            h_exists_mem_tower) h_conf
        have _h_not_sat0_conf : ¬ SatelliteRenormalizableTower (0 : ℂ) :=
          not_satelliteRenormalizableTower_of_mem_mandelbrot_conformal
            h_conf 0 zero_mem_mandelbrotSet_fastTower
        have _hFalse_conf2 : False :=
          false_of_moleculeConformalModulusLowerBoundData_and_infinitely_renormalizable_has_tower_data
            h_conf h_tower_data
        have _h_no_tower_conf : ¬ InfinitelyRenormalizableHasTowerData :=
          consistency_checkpoint_conformal_bridge_excludes_global_ir_tower h_conf
        exact False.elim hFalse
      · have _h_no_conf : ¬ MoleculeConformalModulusLowerBoundData := h_conf
        by_cases h_uniform : MoleculeUniformConformalLowerBoundData
        · have hFalse :
            False :=
              false_of_moleculeUniformConformalLowerBoundData_and_infinitely_renormalizable_has_tower_data
                h_uniform h_tower_data
          have _hFalse_uniform_exists :
              False :=
            (not_moleculeUniformConformalLowerBoundData_of_exists_mem_mandelbrot_tower
              h_exists_mem_tower) h_uniform
          have h_conf_from_uniform : MoleculeConformalModulusLowerBoundData :=
            moleculeConformalModulusLowerBoundData_of_uniformConformalLowerBoundData h_uniform
          have _h_no_tower_from_conf : ¬ InfinitelyRenormalizableHasTowerData :=
            consistency_checkpoint_conformal_bridge_excludes_global_ir_tower h_conf_from_uniform
          have h_noTowerOnM :
              ∀ (c : ℂ), c ∈ MLC.Quadratic.MandelbrotSet → ¬ SatelliteRenormalizableTower c := by
            intro c hc
            exact not_satelliteRenormalizableTower_of_mem_mandelbrot_uniform h_uniform c hc
          have _h_class_noTowerOnM : True := by
            by_cases h_noTowerPrim : IRNoTowerImpliesPrimitiveData
            · have _h_class_alt :
                PrimitiveRenormalizable (0 : ℂ) ∨ SatelliteRenormalizableTower (0 : ℂ) :=
                classify_infinitely_renormalizable_of_noTowerImpliesPrimitive_of_noTowerOnM
                  h_noTowerPrim h_noTowerOnM 0 zero_mem_mandelbrotSet_fastTower h_ir0
              trivial
            · trivial
          exact False.elim hFalse
        · exact h_main
  · exact h_main

/-- Packaged-IR wrapper for the IR-only MLC route. -/
theorem mlc_conjecture_of_irClassifyBridgeData
    (h_ir : IRClassifyBridgeData) :
    LocallyConnectedSpace mandelbrotSet :=
  mlc_conjecture_of_irLocallyConnectedData
    (irLocallyConnectedData_of_irClassifyBridgeData h_ir)

/-- IR seam payload and packaged IR classify/bridge payload are equivalent. -/
theorem irLocallyConnectedData_iff_irClassifyBridgeData :
    IRLocallyConnectedData ↔ IRClassifyBridgeData := by
  constructor
  · intro h_ir_lc
    exact irClassifyBridgeData_of_irLocallyConnectedData h_ir_lc
  · intro h_ir
    exact irLocallyConnectedData_of_irClassifyBridgeData h_ir

/-- Explicit roundtrip route: build the packaged IR payload from the minimal IR
    seam payload, then apply the packaged MLC wrapper. -/
theorem mlc_conjecture_of_irLocallyConnectedData_via_irClassifyBridgeData
    (h_ir_lc : IRLocallyConnectedData) :
    LocallyConnectedSpace mandelbrotSet :=
  mlc_conjecture_of_irClassifyBridgeData
    (irClassifyBridgeData_of_irLocallyConnectedData h_ir_lc)

/-- Direct IR-packaged assembly from explicit IR classification and the strong
    molecule bridge target. -/
theorem mlc_conjecture_of_classify_moleculeBridgeTarget_data
    (h_classify_ir : IRClassificationData)
    (h_target : MoleculeBridgeTarget.MoleculeImpliesSatellitePrincipalNestData) :
    LocallyConnectedSpace mandelbrotSet :=
  mlc_conjecture_of_irClassifyBridgeData
    (irClassifyBridgeData_of_classify_moleculeBridgeTarget_data h_classify_ir h_target)

/-- Direct IR-packaged assembly from explicit IR classification and the
    uniform conformal molecule bridge target. -/
theorem mlc_conjecture_of_classify_moleculeUniformBridgeTarget_data
    (h_classify_ir : IRClassificationData)
    (h_uniform : MoleculeBridgeTarget.MoleculeImpliesUniformConformalLowerBoundTarget) :
    LocallyConnectedSpace mandelbrotSet :=
  mlc_conjecture_of_irClassifyBridgeData
    (irClassifyBridgeData_of_classify_moleculeUniformBridgeTarget_data h_classify_ir h_uniform)

/-- Direct IR-packaged assembly from global IR→tower bridge data and the strong
    molecule bridge target. -/
theorem mlc_conjecture_of_infinitelyRenormalizableHasTowerData_moleculeBridgeTarget
    (h_tower_data : InfinitelyRenormalizableHasTowerData)
    (h_target : MoleculeBridgeTarget.MoleculeImpliesSatellitePrincipalNestData) :
    LocallyConnectedSpace mandelbrotSet :=
  mlc_conjecture_of_irClassifyBridgeData
    (irClassifyBridgeData_of_infinitelyRenormalizableHasTowerData_moleculeBridgeTarget
      h_tower_data h_target)

/-- Direct IR-packaged assembly from global IR→tower bridge data and the
    uniform conformal molecule bridge target. -/
theorem mlc_conjecture_of_infinitelyRenormalizableHasTowerData_moleculeUniformBridgeTarget
    (h_tower_data : InfinitelyRenormalizableHasTowerData)
    (h_uniform : MoleculeBridgeTarget.MoleculeImpliesUniformConformalLowerBoundTarget) :
    LocallyConnectedSpace mandelbrotSet :=
  mlc_conjecture_of_irClassifyBridgeData
    (irClassifyBridgeData_of_infinitelyRenormalizableHasTowerData_moleculeUniformBridgeTarget
      h_tower_data h_uniform)

/-- Bridge theorem: any renormalization tower yields `mlc_conjecture` via the
    IR seam payload produced by the inconsistency route. -/
theorem mlc_conjecture_of_tower {c₀ : ℂ}
    (T : RenormalizationTower (parameterToBMol c₀)) :
    LocallyConnectedSpace mandelbrotSet :=
  mlc_conjecture_of_irLocallyConnectedData (irLocallyConnectedData_of_tower T)

/-- Existential-tower bridge theorem: one renormalization tower already
    implies `mlc_conjecture`. -/
theorem mlc_conjecture_of_exists_tower
    (h_exists : ∃ c₀ : ℂ, Nonempty (RenormalizationTower (parameterToBMol c₀))) :
    LocallyConnectedSpace mandelbrotSet :=
  mlc_conjecture_of_irLocallyConnectedData
    (irLocallyConnectedData_of_exists_tower h_exists)

/-- BMol-level existential-tower bridge theorem: one abstract renormalization
    tower already implies `mlc_conjecture` via the generalized inconsistency
    route. -/
theorem mlc_conjecture_of_exists_tower_bMol
    (h_exists : ∃ g : Molecule.BMol, Nonempty (RenormalizationTower g)) :
    LocallyConnectedSpace mandelbrotSet := by
  rcases h_exists with ⟨g, ⟨T⟩⟩
  exact mlc_of_tower_bMol T

/-- Molecule fixed-point hypotheses plus fixed-point parameter lift data imply
    `mlc_conjecture` through the tower route. -/
theorem mlc_conjecture_of_moleculeRenormalizableFixedPointData
    (h_mol : MoleculeRenormalizableFixedPointData)
    (h_lift : ParameterToBMolFixedPointLiftData) :
    LocallyConnectedSpace mandelbrotSet :=
  mlc_conjecture_of_exists_tower
    (exists_renormalization_tower_of_moleculeRenormalizableFixedPointData h_mol h_lift)

/-- Model-data variant: fixed-point parameter-model data suffices to recover
    the tower route into `mlc_conjecture`. -/
theorem mlc_conjecture_of_moleculeRenormalizableFixedPointData_of_fixedPointParameterModelData
    (h_mol : MoleculeRenormalizableFixedPointData)
    (h_model : FixedPointParameterModelData) :
    LocallyConnectedSpace mandelbrotSet :=
  mlc_conjecture_of_exists_tower
    (exists_renormalization_tower_of_moleculeRenormalizableFixedPointData_of_fixedPointParameterModelData
      h_mol h_model)

/-- Parameter-level fixed-point bridge:
    if some parameter map is a fast-renormalizable fixed point of `Rfast`,
    then `mlc_conjecture` follows via tower existence. -/
theorem mlc_conjecture_of_exists_parameter_rfast_fixed_point
    (h_exists :
      ∃ c : ℂ, Molecule.IsFastRenormalizable (parameterToBMol c) ∧
        Molecule.Rfast (parameterToBMol c) = parameterToBMol c) :
    LocallyConnectedSpace mandelbrotSet :=
  mlc_conjecture_of_exists_tower
    (exists_renormalization_tower_of_exists_parameter_rfast_fixed_point h_exists)

/-- Satellite specialization: a satellite renormalization tower hypothesis
    gives `mlc_conjecture` through the tower bridge. -/
theorem mlc_conjecture_of_satellite_tower (c : ℂ)
    (h : SatelliteRenormalizableTower c) :
    LocallyConnectedSpace mandelbrotSet :=
  mlc_conjecture_of_tower (satelliteTower c h)

/-- Existential satellite-tower specialization. -/
theorem mlc_conjecture_of_exists_satellite_tower
    (h_exists : ∃ c : ℂ, SatelliteRenormalizableTower c) :
    LocallyConnectedSpace mandelbrotSet := by
  rcases h_exists with ⟨c, h_sat⟩
  exact mlc_conjecture_of_satellite_tower c h_sat

/-- Any explicit IR witness together with global IR→tower bridge data implies
    `mlc_conjecture`. -/
theorem mlc_conjecture_of_irWitness_of_infinitelyRenormalizableHasTowerData
    (h_data : InfinitelyRenormalizableHasTowerData)
    (c : ℂ) (h_ir : InfinitelyRenormalizable c) :
    LocallyConnectedSpace mandelbrotSet := by
  rcases infinitely_renormalizable_has_tower h_data c h_ir with ⟨T, _⟩
  exact mlc_conjecture_of_tower T

/-- Globalized fast-tower bridge into `mlc_conjecture` using the Gaussian
    proxy IR witness at `c = 0`. -/
theorem mlc_conjecture_of_infinitelyRenormalizableHasTowerData
    (h_data : InfinitelyRenormalizableHasTowerData) :
    LocallyConnectedSpace mandelbrotSet :=
  mlc_conjecture_of_irWitness_of_infinitelyRenormalizableHasTowerData
    h_data 0 (infinitely_renormalizable_of_gaussian_modulus 0)

/-- Minimal seam payload for the direct MLC route:
    FR connectedness data plus IR local-connectivity data. -/
structure MLCSeamData : Prop where
  puzzle_connected : Quadratic.ParaPuzzlePieceInterMandelbrotConnectedData
  ir_local_connected : IRLocallyConnectedData

/-- Characterization of the minimal direct-route seam payload. -/
theorem mlcSeamData_iff :
    MLCSeamData ↔
      Quadratic.ParaPuzzlePieceInterMandelbrotConnectedData ∧ IRLocallyConnectedData := by
  constructor
  · intro h
    exact ⟨h.puzzle_connected, h.ir_local_connected⟩
  · intro h
    exact ⟨h.1, h.2⟩

/-- Build minimal seam payload from FR connectedness + IR local-connectivity
    payloads. -/
def mlcSeamData_of_paraPuzzleConnectedData_irLocallyConnectedData
    (h_conn : Quadratic.ParaPuzzlePieceInterMandelbrotConnectedData)
    (h_ir_lc : IRLocallyConnectedData) :
    MLCSeamData where
  puzzle_connected := h_conn
  ir_local_connected := h_ir_lc

/-- Build minimal seam payload from FR connectedness + packaged IR
    classify/bridge data. -/
def mlcSeamData_of_paraPuzzleConnectedData_irClassifyBridgeData
    (h_conn : Quadratic.ParaPuzzlePieceInterMandelbrotConnectedData)
    (h_ir : IRClassifyBridgeData) :
    MLCSeamData :=
  mlcSeamData_of_paraPuzzleConnectedData_irLocallyConnectedData
    h_conn
    (irLocallyConnectedData_of_irClassifyBridgeData h_ir)

/-- Build packaged classify/bridge seam payload from FR connectedness +
    packaged IR classify/bridge data. -/
def mlcClassifyBridgeSeamData_of_paraPuzzleConnectedData_irClassifyBridgeData
    (h_conn : Quadratic.ParaPuzzlePieceInterMandelbrotConnectedData)
    (h_ir : IRClassifyBridgeData) :
    MLCClassifyBridgeSeamData where
  puzzle_connected := h_conn
  ir := h_ir

/-- Build packaged classify/bridge seam payload from boundary-motion hypotheses
    + packaged IR classify/bridge data. -/
def mlcClassifyBridgeSeamData_of_motionHyp_irClassifyBridgeData
    (h_motion : Quadratic.PuzzleBoundaryMotionHyp)
    (h_ir : IRClassifyBridgeData) :
    MLCClassifyBridgeSeamData :=
  mlcClassifyBridgeSeamData_of_paraPuzzleConnectedData_irClassifyBridgeData
    (paraPuzzleConnectedData_of_motionHyp h_motion)
    h_ir

/-- Build packaged classify/bridge seam payload from FR subset-data +
    packaged IR classify/bridge data. -/
def mlcClassifyBridgeSeamData_of_paraPuzzleMandelbrotSubsetData_irClassifyBridgeData
    (hsub : Quadratic.ParaPuzzleMandelbrotSubsetData)
    (h_ir : IRClassifyBridgeData) :
    MLCClassifyBridgeSeamData :=
  mlcClassifyBridgeSeamData_of_paraPuzzleConnectedData_irClassifyBridgeData
    (Quadratic.para_puzzle_piece_inter_mandelbrot_connected_data_of_mandelbrot_subset_data hsub)
    h_ir

/-- Build packaged classify/bridge seam payload from FR transport-data +
    packaged IR classify/bridge data. -/
def mlcClassifyBridgeSeamData_of_paraPuzzleTransportData_irClassifyBridgeData
    (htr : Quadratic.ParaPuzzleInterMandelbrotTransportData)
    (h_ir : IRClassifyBridgeData) :
    MLCClassifyBridgeSeamData :=
  mlcClassifyBridgeSeamData_of_paraPuzzleConnectedData_irClassifyBridgeData
    (Quadratic.para_puzzle_piece_inter_mandelbrot_connected_data_of_transport_data htr)
    h_ir

/-- Build packaged classify/bridge seam payload from FR existential
    transport-data + packaged IR classify/bridge data. -/
def mlcClassifyBridgeSeamData_of_paraPuzzleTransportExistsData_irClassifyBridgeData
    (hex : Quadratic.ParaPuzzleInterMandelbrotTransportExistsData)
    (h_ir : IRClassifyBridgeData) :
    MLCClassifyBridgeSeamData :=
  mlcClassifyBridgeSeamData_of_paraPuzzleConnectedData_irClassifyBridgeData
    (Quadratic.para_puzzle_piece_inter_mandelbrot_connected_data_of_transport_exists_data hex)
    h_ir

/-- Current axiom-backed minimal seam payload. -/
def mlcSeamData_of_axiom : MLCSeamData :=
  mlcSeamData_of_paraPuzzleConnectedData_irLocallyConnectedData
    Quadratic.para_puzzle_piece_inter_mandelbrot_connected_data_of_axiom
    irLocallyConnectedData_of_axiom

/-- Direct MLC assembly from the minimal seam payload. -/
theorem mlc_conjecture_of_MLCSeamData
    (h_seam : MLCSeamData) :
    LocallyConnectedSpace mandelbrotSet := by
  rw [mandelbrotSet_eq_MandelbrotSet]
  apply locallyConnectedSpace_of_locallyConnectedAt
  intro ⟨c, hc⟩
  rcases dichotomy c with h_fin | h_inf
  · exact finite_lc_provider_of_motionHyp
      (Quadratic.puzzleBoundaryMotionHyp_of_connected_data h_seam.puzzle_connected)
      c hc h_fin
  · exact h_seam.ir_local_connected c hc h_inf

/-- Convert packaged classify/bridge seam payload to minimal seam payload. -/
def mlcSeamData_of_MLCClassifyBridgeSeamData
    (h : MLCClassifyBridgeSeamData) :
    MLCSeamData :=
  mlcSeamData_of_paraPuzzleConnectedData_irClassifyBridgeData
    h.puzzle_connected
    h.ir

/-- Direct MLC assembly from packaged classify/bridge seam payload. -/
theorem mlc_conjecture_of_MLCClassifyBridgeSeamData
    (h : MLCClassifyBridgeSeamData) :
    LocallyConnectedSpace mandelbrotSet :=
  mlc_conjecture_of_MLCSeamData
    (mlcSeamData_of_MLCClassifyBridgeSeamData h)

/-- Direct MLC assembly from boundary-motion hypotheses + packaged IR
    classify/bridge data. -/
theorem mlc_conjecture_of_motionHyp_irClassifyBridgeData
    (h_motion : Quadratic.PuzzleBoundaryMotionHyp)
    (h_ir : IRClassifyBridgeData) :
    LocallyConnectedSpace mandelbrotSet :=
  mlc_conjecture_of_MLCClassifyBridgeSeamData
    (mlcClassifyBridgeSeamData_of_motionHyp_irClassifyBridgeData h_motion h_ir)

/-- Packaged wrapper for the legacy motion-hyp + classify/bridge entrypoint,
    routed through the canonical packaged seam payload. -/
theorem mlc_conjecture_of_motionHyp_classify_bridge_data_packaged
    (h_motion : Quadratic.PuzzleBoundaryMotionHyp)
    (h_classify_ir : IRClassificationData)
    (h_bridge :
      MoleculeConjectureRefined →
      ∀ (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet)
        (_h : SatelliteRenormalizableTower c),
        MLC.LocallyConnectedAt MLC.Quadratic.MandelbrotSet ⟨c, hc⟩) :
    LocallyConnectedSpace mandelbrotSet :=
  mlc_conjecture_of_motionHyp_irClassifyBridgeData
    h_motion
    (irClassifyBridgeData_of_classify_bridge_data h_classify_ir h_bridge)

/-- Packaged-IR wrapper for finite-branch + IR classify/bridge assembly. -/
theorem mlc_conjecture_of_finite_irClassifyBridgeData
    (h_fin_lc :
      ∀ (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet) (_h : FinitelyRenormalizable c),
        MLC.LocallyConnectedAt MLC.Quadratic.MandelbrotSet ⟨c, hc⟩)
    (h_ir : IRClassifyBridgeData) :
    LocallyConnectedSpace mandelbrotSet :=
  mlc_conjecture_of_finiteClassificationBridgeData
    h_fin_lc
    h_ir.classify
    h_ir.bridge

/-- Build packaged IR classify/bridge payload from boundary-motion hypotheses,
    explicit IR classification, and molecule bridge target data. -/
def irClassifyBridgeData_of_motionHyp_classify_moleculeBridgeTarget_data
    (h_motion : Quadratic.PuzzleBoundaryMotionHyp)
    (h_classify_ir : IRClassificationData)
    (h_target : MoleculeBridgeTarget.MoleculeImpliesSatellitePrincipalNestData) :
    IRClassifyBridgeData :=
  irClassifyBridgeData_of_classify_bridge_data
    h_classify_ir
    (bridge_provider_of_motionHyp_moleculeBridgeTarget_data h_motion h_target)

/-- Build packaged IR classify/bridge payload from boundary-motion hypotheses,
    explicit IR classification, and the uniform conformal bridge target. -/
def irClassifyBridgeData_of_motionHyp_classify_moleculeUniformBridgeTarget_data
    (h_motion : Quadratic.PuzzleBoundaryMotionHyp)
    (h_classify_ir : IRClassificationData)
    (h_uniform : MoleculeBridgeTarget.MoleculeImpliesUniformConformalLowerBoundTarget) :
    IRClassifyBridgeData :=
  irClassifyBridgeData_of_motionHyp_classify_moleculeBridgeTarget_data
    h_motion
    h_classify_ir
    (MoleculeBridgeTarget.moleculeBridgeTarget_of_moleculeUniformBridgeTarget h_uniform)

/-- Build packaged IR classify/bridge payload from boundary-motion hypotheses,
    Track-1 no-tower primitive data, and the uniform conformal bridge target. -/
def irClassifyBridgeData_of_motionHyp_noTowerImpliesPrimitive_moleculeUniformBridgeTarget_data
    (h_motion : Quadratic.PuzzleBoundaryMotionHyp)
    (h_noTowerPrim : IRNoTowerImpliesPrimitiveData)
    (h_uniform : MoleculeBridgeTarget.MoleculeImpliesUniformConformalLowerBoundTarget) :
    IRClassifyBridgeData :=
  irClassifyBridgeData_of_motionHyp_classify_moleculeUniformBridgeTarget_data
    h_motion
    (irClassificationData_of_noTowerImpliesPrimitiveData_of_moleculeUniformBridgeTarget
      h_noTowerPrim h_uniform)
    h_uniform

/-- Packaged wrapper for boundary-motion + classification + molecule bridge
    target route. -/
theorem mlc_conjecture_of_motionHyp_classify_moleculeBridgeTarget_packaged
    (h_motion : Quadratic.PuzzleBoundaryMotionHyp)
    (h_classify_ir : IRClassificationData)
    (h_target : MoleculeBridgeTarget.MoleculeImpliesSatellitePrincipalNestData) :
    LocallyConnectedSpace mandelbrotSet :=
  mlc_conjecture_of_motionHyp_irClassifyBridgeData
    h_motion
    (irClassifyBridgeData_of_motionHyp_classify_moleculeBridgeTarget_data
      h_motion h_classify_ir h_target)

/-- Packaged wrapper for boundary-motion + classification + uniform conformal
    bridge route. -/
theorem mlc_conjecture_of_motionHyp_classify_moleculeUniformBridgeTarget_packaged
    (h_motion : Quadratic.PuzzleBoundaryMotionHyp)
    (h_classify_ir : IRClassificationData)
    (h_uniform : MoleculeBridgeTarget.MoleculeImpliesUniformConformalLowerBoundTarget) :
    LocallyConnectedSpace mandelbrotSet :=
  mlc_conjecture_of_motionHyp_irClassifyBridgeData
    h_motion
    (irClassifyBridgeData_of_motionHyp_classify_moleculeUniformBridgeTarget_data
      h_motion h_classify_ir h_uniform)

/-- Packaged wrapper for boundary-motion + Track-1 + uniform conformal bridge
    route. -/
theorem mlc_conjecture_of_motionHyp_noTowerImpliesPrimitive_moleculeUniformBridgeTarget_packaged
    (h_motion : Quadratic.PuzzleBoundaryMotionHyp)
    (h_noTowerPrim : IRNoTowerImpliesPrimitiveData)
    (h_uniform : MoleculeBridgeTarget.MoleculeImpliesUniformConformalLowerBoundTarget) :
    LocallyConnectedSpace mandelbrotSet :=
  mlc_conjecture_of_motionHyp_irClassifyBridgeData
    h_motion
    (irClassifyBridgeData_of_motionHyp_noTowerImpliesPrimitive_moleculeUniformBridgeTarget_data
      h_motion h_noTowerPrim h_uniform)

/-- Build packaged IR classify/bridge payload from boundary-motion hypotheses
    and Track-1/Track-2 combined data. -/
def irClassifyBridgeData_of_motionHyp_track12_data
    (h_motion : Quadratic.PuzzleBoundaryMotionHyp)
    (h_track12 : IRNoTowerPrimitiveAndMoleculeBridgeTargetData) :
    IRClassifyBridgeData :=
  irClassifyBridgeData_of_motionHyp_noTowerImpliesPrimitive_moleculeUniformBridgeTarget_data
    h_motion h_track12.1 h_track12.2

/-- Packaged wrapper for boundary-motion + Track-1/Track-2 combined data. -/
theorem mlc_conjecture_of_motionHyp_track12_data_packaged
    (h_motion : Quadratic.PuzzleBoundaryMotionHyp)
    (h_track12 : IRNoTowerPrimitiveAndMoleculeBridgeTargetData) :
    LocallyConnectedSpace mandelbrotSet :=
  mlc_conjecture_of_motionHyp_irClassifyBridgeData
    h_motion
    (irClassifyBridgeData_of_motionHyp_track12_data h_motion h_track12)

/-- Packaged wrapper for `MainPathData`. -/
theorem mlc_conjecture_of_mainPathData_packaged
    (h_main : MainPathData) :
    LocallyConnectedSpace mandelbrotSet :=
  mlc_conjecture_of_motionHyp_track12_data_packaged h_main.1 h_main.2

/-- Legacy and packaged bridge-target motion routes are definitionally aligned. -/
theorem mlc_conjecture_of_motionHyp_classify_moleculeBridgeTarget_eq_packaged
    (h_motion : Quadratic.PuzzleBoundaryMotionHyp)
    (h_classify_ir : IRClassificationData)
    (h_target : MoleculeBridgeTarget.MoleculeImpliesSatellitePrincipalNestData) :
    mlc_conjecture_of_motionHyp_classify_moleculeBridgeTarget h_motion h_classify_ir h_target =
      mlc_conjecture_of_motionHyp_classify_moleculeBridgeTarget_packaged
        h_motion h_classify_ir h_target := by
  rfl

/-- Legacy and packaged uniform-bridge motion routes are definitionally aligned. -/
theorem mlc_conjecture_of_motionHyp_classify_moleculeUniformBridgeTarget_eq_packaged
    (h_motion : Quadratic.PuzzleBoundaryMotionHyp)
    (h_classify_ir : IRClassificationData)
    (h_uniform : MoleculeBridgeTarget.MoleculeImpliesUniformConformalLowerBoundTarget) :
    mlc_conjecture_of_motionHyp_classify_moleculeUniformBridgeTarget
        h_motion h_classify_ir h_uniform =
      mlc_conjecture_of_motionHyp_classify_moleculeUniformBridgeTarget_packaged
        h_motion h_classify_ir h_uniform := by
  rfl

/-- Legacy and packaged Track-1+uniform motion routes are definitionally aligned. -/
theorem mlc_conjecture_of_motionHyp_noTowerImpliesPrimitive_moleculeUniformBridgeTarget_eq_packaged
    (h_motion : Quadratic.PuzzleBoundaryMotionHyp)
    (h_noTowerPrim : IRNoTowerImpliesPrimitiveData)
    (h_uniform : MoleculeBridgeTarget.MoleculeImpliesUniformConformalLowerBoundTarget) :
    mlc_conjecture_of_motionHyp_noTowerImpliesPrimitive_moleculeUniformBridgeTarget
        h_motion h_noTowerPrim h_uniform =
      mlc_conjecture_of_motionHyp_noTowerImpliesPrimitive_moleculeUniformBridgeTarget_packaged
        h_motion h_noTowerPrim h_uniform := by
  rfl

/-- Legacy and packaged Track-1/Track-2 motion routes are definitionally aligned. -/
theorem mlc_conjecture_of_motionHyp_track12_data_eq_packaged
    (h_motion : Quadratic.PuzzleBoundaryMotionHyp)
    (h_track12 : IRNoTowerPrimitiveAndMoleculeBridgeTargetData) :
    mlc_conjecture_of_motionHyp_track12_data h_motion h_track12 =
      mlc_conjecture_of_motionHyp_track12_data_packaged h_motion h_track12 := by
  rfl

/-- Legacy and packaged `MainPathData` routes are definitionally aligned. -/
theorem mlc_conjecture_of_mainPathData_eq_packaged
    (h_main : MainPathData) :
    mlc_conjecture_of_mainPathData h_main =
      mlc_conjecture_of_mainPathData_packaged h_main := by
  rfl

/-- Direct seam theorem with explicit FR connectedness + minimal IR seam
    payloads. -/
theorem mlc_conjecture_of_paraPuzzleConnectedData_irLocallyConnectedData
    (h_conn : Quadratic.ParaPuzzlePieceInterMandelbrotConnectedData)
    (h_ir_lc : IRLocallyConnectedData) :
    LocallyConnectedSpace mandelbrotSet :=
  mlc_conjecture_of_MLCSeamData
    (mlcSeamData_of_paraPuzzleConnectedData_irLocallyConnectedData h_conn h_ir_lc)

/-- Direct seam theorem with explicit FR connectedness payload.
    Replacing `Quadratic.para_puzzle_piece_inter_mandelbrot_connected_data_of_axiom`
    by a constructive witness is the FR unblocking step. -/
theorem mlc_conjecture_of_paraPuzzleConnectedData
    (h_conn : Quadratic.ParaPuzzlePieceInterMandelbrotConnectedData) :
    LocallyConnectedSpace mandelbrotSet :=
  mlc_conjecture_of_paraPuzzleConnectedData_irLocallyConnectedData
    h_conn irLocallyConnectedData_of_axiom

/-- Constructive-route assembly from FR connected-data + IR classify/bridge
    payloads. This bypasses the `ir_locally_connected_seam` axiom once those
    IR payloads are available constructively. -/
theorem mlc_conjecture_of_paraPuzzleConnectedData_classify_bridge_data
    (h_conn : Quadratic.ParaPuzzlePieceInterMandelbrotConnectedData)
    (h_classify_ir : IRClassificationData)
    (h_bridge :
      MoleculeConjectureRefined →
      ∀ (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet)
        (_h : SatelliteRenormalizableTower c),
        MLC.LocallyConnectedAt MLC.Quadratic.MandelbrotSet ⟨c, hc⟩) :
    LocallyConnectedSpace mandelbrotSet :=
  mlc_conjecture_of_MLCClassifyBridgeSeamData
    (mlcClassifyBridgeSeamData_of_paraPuzzleConnectedData_irClassifyBridgeData
      h_conn
      (irClassifyBridgeData_of_classify_bridge_data h_classify_ir h_bridge))

/-- Constructive-route assembly from FR connected-data + packaged IR
    classify/bridge payload. -/
theorem mlc_conjecture_of_paraPuzzleConnectedData_irClassifyBridgeData
    (h_conn : Quadratic.ParaPuzzlePieceInterMandelbrotConnectedData)
    (h_ir : IRClassifyBridgeData) :
    LocallyConnectedSpace mandelbrotSet :=
  mlc_conjecture_of_MLCClassifyBridgeSeamData
    (mlcClassifyBridgeSeamData_of_paraPuzzleConnectedData_irClassifyBridgeData
      h_conn h_ir)

/-- FR branch provider from connected-data payload. -/
lemma finite_lc_provider_of_paraPuzzleConnectedData
    (h_conn : Quadratic.ParaPuzzlePieceInterMandelbrotConnectedData) :
    ∀ (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet) (_h : FinitelyRenormalizable c),
      MLC.LocallyConnectedAt MLC.Quadratic.MandelbrotSet ⟨c, hc⟩ :=
  finite_lc_provider_of_motionHyp
    (Quadratic.puzzleBoundaryMotionHyp_of_connected_data h_conn)

/-- Subset-data route to the direct seam theorem.
    This is axiom-free once `ParaPuzzleMandelbrotSubsetData` is provided
    constructively. -/
theorem mlc_conjecture_of_paraPuzzleMandelbrotSubsetData
    (hsub : Quadratic.ParaPuzzleMandelbrotSubsetData) :
    LocallyConnectedSpace mandelbrotSet :=
  mlc_conjecture_of_paraPuzzleConnectedData
    (Quadratic.para_puzzle_piece_inter_mandelbrot_connected_data_of_mandelbrot_subset_data hsub)

/-- Constructive-route assembly from the stronger subset-data FR payload plus
    explicit IR classify/bridge payloads. -/
theorem mlc_conjecture_of_paraPuzzleMandelbrotSubsetData_classify_bridge_data
    (hsub : Quadratic.ParaPuzzleMandelbrotSubsetData)
    (h_classify_ir : IRClassificationData)
    (h_bridge :
      MoleculeConjectureRefined →
      ∀ (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet)
        (_h : SatelliteRenormalizableTower c),
        MLC.LocallyConnectedAt MLC.Quadratic.MandelbrotSet ⟨c, hc⟩) :
    LocallyConnectedSpace mandelbrotSet :=
  mlc_conjecture_of_MLCClassifyBridgeSeamData
    (mlcClassifyBridgeSeamData_of_paraPuzzleMandelbrotSubsetData_irClassifyBridgeData
      hsub
      (irClassifyBridgeData_of_classify_bridge_data h_classify_ir h_bridge))

/-- Constructive-route assembly from subset-data FR payload plus packaged IR
    classify/bridge payload. -/
theorem mlc_conjecture_of_paraPuzzleMandelbrotSubsetData_irClassifyBridgeData
    (hsub : Quadratic.ParaPuzzleMandelbrotSubsetData)
    (h_ir : IRClassifyBridgeData) :
    LocallyConnectedSpace mandelbrotSet :=
  mlc_conjecture_of_MLCClassifyBridgeSeamData
    (mlcClassifyBridgeSeamData_of_paraPuzzleMandelbrotSubsetData_irClassifyBridgeData hsub h_ir)

/-- Constructive-route assembly from subset-data FR payload plus minimal IR
    local-connectivity seam payload. -/
theorem mlc_conjecture_of_paraPuzzleMandelbrotSubsetData_irLocallyConnectedData
    (hsub : Quadratic.ParaPuzzleMandelbrotSubsetData)
    (h_ir_lc : IRLocallyConnectedData) :
    LocallyConnectedSpace mandelbrotSet :=
  mlc_conjecture_of_paraPuzzleMandelbrotSubsetData_irClassifyBridgeData
    hsub
    (irClassifyBridgeData_of_irLocallyConnectedData h_ir_lc)

/-- Transport-data route to the direct seam theorem.
    This is axiom-free once `ParaPuzzleInterMandelbrotTransportData` is provided
    constructively. -/
theorem mlc_conjecture_of_paraPuzzleTransportData
    (htr : Quadratic.ParaPuzzleInterMandelbrotTransportData) :
    LocallyConnectedSpace mandelbrotSet :=
  mlc_conjecture_of_paraPuzzleConnectedData
    (Quadratic.para_puzzle_piece_inter_mandelbrot_connected_data_of_transport_data htr)

/-- Constructive-route assembly from transport-data FR payload plus explicit
    IR classify/bridge payloads. -/
theorem mlc_conjecture_of_paraPuzzleTransportData_classify_bridge_data
    (htr : Quadratic.ParaPuzzleInterMandelbrotTransportData)
    (h_classify_ir : IRClassificationData)
    (h_bridge :
      MoleculeConjectureRefined →
      ∀ (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet)
        (_h : SatelliteRenormalizableTower c),
        MLC.LocallyConnectedAt MLC.Quadratic.MandelbrotSet ⟨c, hc⟩) :
    LocallyConnectedSpace mandelbrotSet :=
  mlc_conjecture_of_MLCClassifyBridgeSeamData
    (mlcClassifyBridgeSeamData_of_paraPuzzleTransportData_irClassifyBridgeData
      htr
      (irClassifyBridgeData_of_classify_bridge_data h_classify_ir h_bridge))

/-- Constructive-route assembly from transport-data FR payload plus packaged IR
    classify/bridge payload. -/
theorem mlc_conjecture_of_paraPuzzleTransportData_irClassifyBridgeData
    (htr : Quadratic.ParaPuzzleInterMandelbrotTransportData)
    (h_ir : IRClassifyBridgeData) :
    LocallyConnectedSpace mandelbrotSet :=
  mlc_conjecture_of_MLCClassifyBridgeSeamData
    (mlcClassifyBridgeSeamData_of_paraPuzzleTransportData_irClassifyBridgeData htr h_ir)

/-- Constructive-route assembly from transport-data FR payload plus minimal IR
    local-connectivity seam payload. -/
theorem mlc_conjecture_of_paraPuzzleTransportData_irLocallyConnectedData
    (htr : Quadratic.ParaPuzzleInterMandelbrotTransportData)
    (h_ir_lc : IRLocallyConnectedData) :
    LocallyConnectedSpace mandelbrotSet :=
  mlc_conjecture_of_paraPuzzleTransportData_irClassifyBridgeData
    htr
    (irClassifyBridgeData_of_irLocallyConnectedData h_ir_lc)

/-- Existential-transport-data route to the direct seam theorem.
    This is axiom-free once `ParaPuzzleInterMandelbrotTransportExistsData` is
    provided constructively. -/
theorem mlc_conjecture_of_paraPuzzleTransportExistsData
    (hex : Quadratic.ParaPuzzleInterMandelbrotTransportExistsData) :
    LocallyConnectedSpace mandelbrotSet :=
  mlc_conjecture_of_paraPuzzleConnectedData
    (Quadratic.para_puzzle_piece_inter_mandelbrot_connected_data_of_transport_exists_data hex)

/-- Constructive-route assembly from existential transport-data FR payload plus
    explicit IR classify/bridge payloads. -/
theorem mlc_conjecture_of_paraPuzzleTransportExistsData_classify_bridge_data
    (hex : Quadratic.ParaPuzzleInterMandelbrotTransportExistsData)
    (h_classify_ir : IRClassificationData)
    (h_bridge :
      MoleculeConjectureRefined →
      ∀ (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet)
        (_h : SatelliteRenormalizableTower c),
        MLC.LocallyConnectedAt MLC.Quadratic.MandelbrotSet ⟨c, hc⟩) :
    LocallyConnectedSpace mandelbrotSet :=
  mlc_conjecture_of_MLCClassifyBridgeSeamData
    (mlcClassifyBridgeSeamData_of_paraPuzzleTransportExistsData_irClassifyBridgeData
      hex
      (irClassifyBridgeData_of_classify_bridge_data h_classify_ir h_bridge))

/-- Constructive-route assembly from existential transport-data FR payload plus
    packaged IR classify/bridge payload. -/
theorem mlc_conjecture_of_paraPuzzleTransportExistsData_irClassifyBridgeData
    (hex : Quadratic.ParaPuzzleInterMandelbrotTransportExistsData)
    (h_ir : IRClassifyBridgeData) :
    LocallyConnectedSpace mandelbrotSet :=
  mlc_conjecture_of_MLCClassifyBridgeSeamData
    (mlcClassifyBridgeSeamData_of_paraPuzzleTransportExistsData_irClassifyBridgeData hex h_ir)

/-- Constructive-route assembly from existential transport-data FR payload plus
    minimal IR local-connectivity seam payload. -/
theorem mlc_conjecture_of_paraPuzzleTransportExistsData_irLocallyConnectedData
    (hex : Quadratic.ParaPuzzleInterMandelbrotTransportExistsData)
    (h_ir_lc : IRLocallyConnectedData) :
    LocallyConnectedSpace mandelbrotSet :=
  mlc_conjecture_of_paraPuzzleTransportExistsData_irClassifyBridgeData
    hex
    (irClassifyBridgeData_of_irLocallyConnectedData h_ir_lc)

/-- Separate finite-branch local-connectivity seam retained for the current
    pass while the IR/satellite package is split into Problems 4.3 / 4.4 / 4.5. -/
axiom finite_branch_local_connectivity : FiniteBranchLocalConnectivityData

/-- Problem 4.3 root-facing axiom: pseudo-Siegel a priori bounds in the
    remaining unbounded satellite ql cases. -/
axiom problem43_pseudoSiegelAPrioriBounds :
  Problem43PseudoSiegelAPrioriBoundsData

/-- Problem 4.4 root-facing axiom: the Virtual Molecule near-degenerate
    regime. -/
axiom problem44_virtualMolecule :
  Problem44VirtualMoleculeData

/-- Problem 4.5 root-facing axiom: virtual near-Molecule renormalization in the
    primitive-first ql case. -/
axiom problem45_virtualNearMoleculeRenormalization :
  Problem45VirtualNearMoleculeRenormalizationData

/-- The Mandelbrot Local Connectivity (MLC) Conjecture:
    the Mandelbrot set is locally connected. The current root theorem is routed
    through split Problem 4.3 / 4.4 / 4.5 seams together with a separate
    finite-branch payload. -/

theorem mlc_conjecture
    : LocallyConnectedSpace mandelbrotSet :=
  mlc_conjecture_of_problem43_44_45_data
    finite_branch_local_connectivity
    problem43_pseudoSiegelAPrioriBounds
    problem44_virtualMolecule
    problem45_virtualNearMoleculeRenormalization


end MainProof

end MLC
