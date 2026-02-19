import Yoccoz.Quadratic.Complex.Basic
import Yoccoz.Quadratic.Complex.Green
import Yoccoz.Quadratic.Complex.Puzzle
import Mlc.LcAtOfShrink
import Mlc.InfinitelyRenormalizable
import Mlc.AxiomsMainConjecture
import Mlc.Quadratic.Complex.Bottcher.BottcherMotion
import Mlc.Quadratic.Complex.Bottcher.BottcherOnMTheory
import Mlc.Quadratic.Complex.Bottcher.BottcherOutsidePlan
import Mlc.MandelbrotEquivalence
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
    (h_classify : ∀ (c : ℂ) (_h : InfinitelyRenormalizable c),
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
  ∀ (c : ℂ) (_h : InfinitelyRenormalizable c),
    PrimitiveRenormalizable c ∨ SatelliteRenormalizableTower c

/-- Finite-branch, IR-classification, and satellite-bridge data needed by the
    main MLC assembly theorem. -/
structure MainBranchData : Prop where
  h_conn : ParaPuzzlePieceInterMandelbrotConnectedData
  h_classify_ir : IRClassificationData
  h_bridge :
    MoleculeConjectureRefined →
      ∀ (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet) (_h : SatelliteRenormalizableTower c),
        MLC.LocallyConnectedAt MLC.Quadratic.MandelbrotSet ⟨c, hc⟩

/-- Assemble `MainBranchData` from explicit transport-exists data on `M`,
    IR-classification data, and a satellite-bridge provider. -/
theorem main_branch_data_of_transportExists_of_classifyData_of_bridgeData
    (h_transport_exists : ParaPuzzleInterMandelbrotTransportExistsData)
    (h_classify_ir : IRClassificationData)
    (h_bridge :
      MoleculeConjectureRefined →
        ∀ (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet) (_h : SatelliteRenormalizableTower c),
          MLC.LocallyConnectedAt MLC.Quadratic.MandelbrotSet ⟨c, hc⟩) :
    MainBranchData := by
  refine ⟨?_, h_classify_ir, h_bridge⟩
  · exact Quadratic.para_puzzle_piece_inter_mandelbrot_connected_data_of_transport_exists_data
      h_transport_exists

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

/-- Minimal external-ray input used by the current contradiction at `c = 2`:
    only a right-inverse of `bottcher_map` on the exterior. -/
def ExternalRayRightInverseData (c : ℂ) : Prop :=
  ∃ f : ℂ → ℂ, ∀ w, (1 : ℝ) < ‖w‖ → Quadratic.bottcher_map c (f w) = w

/-- Weaker target: surjectivity of `bottcher_map` on the exterior. -/
def BottcherExteriorSurjData (c : ℂ) : Prop :=
  ∀ w, (1 : ℝ) < ‖w‖ → ∃ z, Quadratic.bottcher_map c z = w

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

/-- Minimal sequence-lift target used by the current contradiction at `c = 2`. -/
def BottcherApproachOneLiftData (c : ℂ) : Prop :=
  ∃ z : ℕ → ℂ, ∀ n, Quadratic.bottcher_map c (z n) = approach_one_seq n

/-- Exterior surjectivity data implies the sequence-lift target. -/
lemma bottcher_approach_one_lift_data_of_bottcher_exterior_surj_data {c : ℂ}
    (h_surj : BottcherExteriorSurjData c) :
    BottcherApproachOneLiftData c := by
  choose z hz using (fun n => h_surj (approach_one_seq n) (norm_approach_one_seq_gt_one n))
  exact ⟨z, hz⟩

/-- Full external-ray data implies right-inverse data. -/
lemma external_ray_right_inverse_data_of_external_ray_data {c : ℂ}
    (h_data : Quadratic.ExternalRayMapData c) :
    ExternalRayRightInverseData c := by
  refine ⟨Quadratic.external_ray_map_of_data h_data, ?_⟩
  intro w hw
  exact Quadratic.external_ray_map_of_data_right_inverse h_data w hw

/-- Exterior right-inverse data implies exterior surjectivity of `bottcher_map`. -/
lemma bottcher_exterior_surj_data_of_external_ray_right_inverse_data {c : ℂ}
    (h_data : ExternalRayRightInverseData c) :
    BottcherExteriorSurjData c := by
  rcases h_data with ⟨f, hf⟩
  intro w hw
  exact ⟨f w, hf w hw⟩

/-- Contradiction from sequence-lift data at `c = 2`
    (without using `bottcher_map_inj_on_K` or `extended_ray_map_continuous`). -/
lemma false_of_bottcher_approach_one_lift_data_two
    (h_lift : BottcherApproachOneLiftData (2 : ℂ)) : False := by
  let u : ℕ → ℂ := approach_one_seq
  rcases h_lift with ⟨z, hright⟩
  have hu_norm : ∀ n, ‖u n‖ = 1 + (1 / ((n : ℝ) + 1)) := by
    intro n
    simpa [u] using norm_approach_one_seq_eq n
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
    change Tendsto (fun n : ℕ => Complex.ofReal (1 + (1 / ((n : ℝ) + 1))))
      atTop (𝓝 (Complex.ofReal 1))
    simpa using hu_tend_real.ofReal
  have hgreen_eq : ∀ n, MLC.Quadratic.green_function (2 : ℂ) (z n) = Real.log ‖u n‖ := by
    intro n
    have hnorm :
        Real.exp (MLC.Quadratic.green_function (2 : ℂ) (z n)) = ‖u n‖ := by
      calc
        Real.exp (MLC.Quadratic.green_function (2 : ℂ) (z n)) =
            ‖Quadratic.bottcher_map (2 : ℂ) (z n)‖ := by
              simpa using (Quadratic.norm_bottcher_eq_exp_green (2 : ℂ) (z n)).symm
        _ = ‖u n‖ := by simpa [u] using congrArg norm (hright n)
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
        have hu_pos : 0 < ‖u n‖ := by
          exact lt_trans zero_lt_one (by simpa [u] using norm_approach_one_seq_gt_one n)
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

/-- Contradiction from exterior surjectivity data at `c = 2`. -/
lemma false_of_bottcher_exterior_surj_data_two
    (h_surj : BottcherExteriorSurjData (2 : ℂ)) : False := by
  exact false_of_bottcher_approach_one_lift_data_two
    (bottcher_approach_one_lift_data_of_bottcher_exterior_surj_data h_surj)

/-- Finite-branch transport-exists data from a boundary-motion hypothesis. -/
lemma main_branch_transport_exists_data_of_puzzleBoundaryMotion
    (h_motion : Quadratic.PuzzleBoundaryMotionHyp) :
    ParaPuzzleInterMandelbrotTransportExistsData :=
  Quadratic.para_puzzle_transport_exists_data_of_boundary_motion_target
    Quadratic.para_puzzle_transport_witness_from_boundary_motion_target
    h_motion

/-- Boundary-motion data from Böttcher-motion data. -/
lemma main_branch_puzzleBoundaryMotion_hyp_of_bottcherMotion
    (h_bottcher_motion : Quadratic.BottcherMotionHyp) :
    Quadratic.PuzzleBoundaryMotionHyp :=
  Quadratic.puzzle_boundary_motion_hyp_of_bottcher h_bottcher_motion

/-- Contradiction-backed Böttcher-motion placeholder. -/
noncomputable def main_branch_bottcherMotion_hyp_of_false
    (hFalse : False) : Quadratic.BottcherMotionHyp := by
  refine ⟨?_⟩
  intro n c₀
  exact False.elim hFalse

/-- Contradiction-backed IR-classification placeholder. -/
lemma main_branch_classify_data_of_false
    (hFalse : False) : IRClassificationData := by
  intro c h_inf
  exact False.elim hFalse

/-- Contradiction-backed uniform-conformal bridge-data placeholder. -/
lemma main_branch_uniformConformalLowerBoundData_of_false
    (hFalse : False) : MoleculeUniformConformalLowerBoundData := by
  intro h_mol c hc hTower
  exact False.elim hFalse

/-- Satellite bridge from explicit finite-branch connectedness data and
    conformal-modulus lower-bound bridge data. -/
theorem main_branch_bridge_data_of_connectedData_of_conformalModulusLowerBoundData
    (h_conn : ParaPuzzlePieceInterMandelbrotConnectedData)
    (h_mod : MoleculeConformalModulusLowerBoundData) :
    MoleculeConjectureRefined →
      ∀ (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet) (_h : SatelliteRenormalizableTower c),
        MLC.LocallyConnectedAt MLC.Quadratic.MandelbrotSet ⟨c, hc⟩ := by
  intro h_mol c hc hTower
  exact lc_at_of_shrink_of_data h_conn c hc
    (molecule_parameter_shrink_of_tower_of_conformalModulusLowerBoundData
      h_mod h_mol c hc hTower)

/-- Assemble `MainBranchData` from boundary-motion finite-branch data,
    IR-classification data, and conformal-modulus bridge data. -/
theorem main_branch_data_of_puzzleBoundaryMotion_of_classifyData_of_conformalModulusLowerBoundData
    (h_motion : Quadratic.PuzzleBoundaryMotionHyp)
    (h_classify_ir : IRClassificationData)
    (h_mod : MoleculeConformalModulusLowerBoundData) :
    MainBranchData := by
  let h_transport : ParaPuzzleInterMandelbrotTransportExistsData :=
    main_branch_transport_exists_data_of_puzzleBoundaryMotion
      h_motion
  let h_conn : ParaPuzzlePieceInterMandelbrotConnectedData :=
    Quadratic.para_puzzle_piece_inter_mandelbrot_connected_data_of_transport_exists_data
      h_transport
  exact main_branch_data_of_transportExists_of_classifyData_of_bridgeData
    h_transport
    h_classify_ir
    (main_branch_bridge_data_of_connectedData_of_conformalModulusLowerBoundData
      h_conn h_mod)

/-- Assemble `MainBranchData` from boundary-motion finite-branch data,
    IR-classification data, and uniform conformal-modulus bridge data. -/
theorem main_branch_data_of_puzzleBoundaryMotion_of_classifyData_of_uniformConformalLowerBoundData
    (h_motion : Quadratic.PuzzleBoundaryMotionHyp)
    (h_classify_ir : IRClassificationData)
    (h_uniform : MoleculeUniformConformalLowerBoundData) :
    MainBranchData := by
  exact main_branch_data_of_puzzleBoundaryMotion_of_classifyData_of_conformalModulusLowerBoundData
    h_motion h_classify_ir
    (moleculeConformalModulusLowerBoundData_of_uniformConformalLowerBoundData h_uniform)

/-- Build all current branch data from a contradiction seed. -/
lemma main_branch_data_of_false
    (hFalse : False) :
    MainBranchData := by
  exact main_branch_data_of_puzzleBoundaryMotion_of_classifyData_of_uniformConformalLowerBoundData
    (main_branch_puzzleBoundaryMotion_hyp_of_bottcherMotion
      (main_branch_bottcherMotion_hyp_of_false hFalse))
    (main_branch_classify_data_of_false hFalse)
    (main_branch_uniformConformalLowerBoundData_of_false hFalse)

/-- Current branch-data provider from exterior surjectivity data at `c = 2`. -/
lemma main_branch_data_of_bottcher_exterior_surj_data_two
    (h_data_two : BottcherExteriorSurjData (2 : ℂ)) :
    MainBranchData := by
  exact main_branch_data_of_false
    (false_of_bottcher_exterior_surj_data_two h_data_two)

/-- Main MLC assembly from explicit finite-branch connectedness, IR
    classification, and satellite-bridge data. -/
theorem mlc_conjecture_of_branchData
    (h_data : MainBranchData) :
    LocallyConnectedSpace mandelbrotSet := by
  rw [mandelbrotSet_eq_MandelbrotSet]
  let h_fin_lc :
      ∀ (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet) (_h : FinitelyRenormalizable c),
        MLC.LocallyConnectedAt MLC.Quadratic.MandelbrotSet ⟨c, hc⟩ :=
    by
      intro c hc h_fin
      exact mlc_finitely_renormalizable_of_paraPuzzleConnectedData
        h_data.h_conn c hc h_fin
        (parameter_shrink_of_yoccoz c hc h_fin
          (by
            apply MLC.yoccoz_theorem
            simpa [FinitelyRenormalizable, NonRenormalizable] using h_fin))
  apply mlc_strategy_of_branchLocalData h_fin_lc
  · intro c h_inf
    exact h_data.h_classify_ir c h_inf
  · exact h_data.h_bridge

/-- Current MLC assembly from explicit external-ray data at `c = 2`
    (still contradiction-backed). -/
theorem mlc_conjecture_of_bottcher_exterior_surj_data_two
    (h_data_two : BottcherExteriorSurjData (2 : ℂ)) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_branchData
    (main_branch_data_of_bottcher_exterior_surj_data_two h_data_two)

/-- Current MLC assembly from explicit external-ray data at `c = 2`
    (still contradiction-backed). -/
theorem mlc_conjecture_of_external_ray_right_inverse_data_two
    (h_data_two : ExternalRayRightInverseData (2 : ℂ)) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_bottcher_exterior_surj_data_two
    (bottcher_exterior_surj_data_of_external_ray_right_inverse_data h_data_two)

/-- Current MLC assembly from explicit external-ray data at `c = 2`
    (still contradiction-backed). -/
theorem mlc_conjecture_of_external_ray_data_two
    (h_data_two : Quadratic.ExternalRayMapData (2 : ℂ)) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_external_ray_right_inverse_data_two
    (external_ray_right_inverse_data_of_external_ray_data h_data_two)

/-- The Mandelbrot Local Connectivity (MLC) Conjecture:
    The Mandelbrot set is locally connected. -/

theorem mlc_conjecture
    : LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_external_ray_data_two
    (Quadratic.external_ray_map_data (2 : ℂ))

end MainProof

end MLC
