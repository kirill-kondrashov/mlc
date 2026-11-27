import Yoccoz.Quadratic.Complex.Basic
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Compactness of the Mandelbrot set

The parameter escape test and its compactness consequence are elementary
quadratic-dynamics facts. They provide the global bound used by the residual
area metric.
-/

namespace MLC.Quadratic

open Complex Filter Topology Metric

lemma continuous_parameter_orbit (n : ℕ) :
    Continuous (fun c : ℂ => orbit c 0 n) := by
  induction n with
  | zero =>
      simpa [orbit] using (continuous_const :
        Continuous fun _ : ℂ => (0 : ℂ))
  | succ n ih =>
      rw [show (fun c : ℂ => orbit c 0 (n + 1)) =
          fun c => (orbit c 0 n) ^ 2 + c by
        funext c
        simp [orbit_succ, fc]]
      exact (ih.pow 2).add continuous_id

lemma escapes_of_large_norm_and_ge_parameter
    {c z : ℂ} (hz : 2 < ‖z‖) (hcz : ‖c‖ ≤ ‖z‖) :
    ¬ boundedOrbit c z := by
  intro hbounded
  rcases hbounded with ⟨M, hM⟩
  have hgrowth : ∀ n, ‖orbit c z n‖ ≥ 2 + 3 ^ n * (‖z‖ - 2) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        let zn := orbit c z n
        have hzn2 : 2 < ‖zn‖ := by
          have : 0 < (3 : ℝ) ^ n * (‖z‖ - 2) :=
            mul_pos (pow_pos (by norm_num) _) (sub_pos.mpr hz)
          linarith [ih]
        have hznc : ‖c‖ ≤ ‖zn‖ := by
          have hpow : (1 : ℝ) ≤ (3 : ℝ) ^ n := one_le_pow₀ (by norm_num)
          have hmargin :
              ‖z‖ - 2 ≤ (3 : ℝ) ^ n * (‖z‖ - 2) := by
            calc
              ‖z‖ - 2 = 1 * (‖z‖ - 2) := by ring
              _ ≤ (3 : ℝ) ^ n * (‖z‖ - 2) :=
                mul_le_mul_of_nonneg_right hpow
                  (sub_nonneg.mpr (le_of_lt hz))
          calc
            ‖c‖ ≤ ‖z‖ := hcz
            _ = 2 + (‖z‖ - 2) := by ring
            _ ≤ 2 + (3 : ℝ) ^ n * (‖z‖ - 2) :=
              by simpa [add_comm] using add_le_add_left hmargin 2
            _ ≤ ‖zn‖ := by exact ih
        have htri : ‖zn ^ 2 + c‖ ≥ ‖zn‖ ^ 2 - ‖c‖ := by
          have h := norm_add_le (zn ^ 2 + c) (-c)
          rw [add_neg_cancel_right, norm_neg, Complex.norm_pow] at h
          linarith
        have hstep : ‖zn‖ ^ 2 - ‖c‖ ≥ 2 + 3 * (‖zn‖ - 2) := by
          calc
            ‖zn‖ ^ 2 - ‖c‖ ≥ ‖zn‖ ^ 2 - ‖zn‖ := by linarith
            _ = (‖zn‖ - 2) * (‖zn‖ + 1) + 2 := by ring
            _ ≥ (‖zn‖ - 2) * 3 + 2 := by
              have : 3 ≤ ‖zn‖ + 1 := by linarith
              simpa [mul_comm] using
                add_le_add_right
                  (mul_le_mul_of_nonneg_left
                    this (sub_nonneg.mpr (le_of_lt hzn2))) 2
            _ = 2 + 3 * (‖zn‖ - 2) := by ring
        calc
          ‖orbit c z (n + 1)‖ = ‖zn ^ 2 + c‖ := by
            rw [orbit_succ]
            rfl
          _ ≥ ‖zn‖ ^ 2 - ‖c‖ := htri
          _ ≥ 2 + 3 * (‖zn‖ - 2) := hstep
          _ ≥ 2 + 3 * ((3 : ℝ) ^ n * (‖z‖ - 2)) := by
            have hmargin : (3 : ℝ) ^ n * (‖z‖ - 2) ≤ ‖zn‖ - 2 := by
              linarith [ih]
            nlinarith
          _ = 2 + (3 : ℝ) ^ (n + 1) * (‖z‖ - 2) := by
            rw [pow_succ]
            ring
  let C := ‖z‖ - 2
  have hC : 0 < C := sub_pos.mpr hz
  obtain ⟨N, hN⟩ := exists_nat_ge ((M - 2) / C + 1)
  have hpow : (3 : ℝ) ^ N ≥ (N : ℝ) := by
    have h : ∀ n : ℕ, (3 : ℝ) ^ n ≥ n := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        cases n with
        | zero => norm_num
        | succ n =>
            have ih' : (n : ℝ) + 1 ≤ (3 : ℝ) ^ (n + 1) := by
              exact_mod_cast ih
            have hmul :
                (3 : ℝ) ^ (n + 1) * 3 ≥ ((n : ℝ) + 1) * 3 :=
              mul_le_mul_of_nonneg_right ih' (by norm_num)
            calc
              (3 : ℝ) ^ (n + 1 + 1)
                  = (3 : ℝ) ^ (n + 1) * 3 := by rw [pow_succ]
              _ ≥ ((n : ℝ) + 1) * 3 := hmul
              _ ≥ (n + 1 + 1 : ℕ) := by
                norm_num
                linarith
    exact h N
  have hbig : (3 : ℝ) ^ N * C > M - 2 := by
    calc
      (3 : ℝ) ^ N * C ≥ (N : ℝ) * C :=
        mul_le_mul_of_nonneg_right hpow (le_of_lt hC)
      _ ≥ ((M - 2) / C + 1) * C :=
        mul_le_mul_of_nonneg_right hN (le_of_lt hC)
      _ = (M - 2) + C := by field_simp [ne_of_gt hC]
      _ > M - 2 := by linarith
  have hbound := hM N
  linarith [hgrowth N, hbig]

lemma parameter_gt_two_escapes {c : ℂ} (hc : 2 < ‖c‖) :
    ¬ boundedOrbit c 0 := by
  intro hbounded
  have hshift : boundedOrbit c c := by
    rcases hbounded with ⟨M, hM⟩
    refine ⟨M, ?_⟩
    intro n
    have horbit : orbit c c n = orbit c 0 (n + 1) := by
      rw [show orbit c c n = (MLC.Quadratic.fc c)^[n] c by rfl,
        show orbit c 0 (n + 1) =
          (MLC.Quadratic.fc c)^[n] ((MLC.Quadratic.fc c) 0) by rfl,
        MLC.Quadratic.fc]
      simp
    rw [horbit]
    exact hM (n + 1)
  exact escapes_of_large_norm_and_ge_parameter hc (le_refl _) hshift

theorem mandelbrot_subset_closedBall :
    MandelbrotSet ⊆ Metric.closedBall (0 : ℂ) 2 := by
  intro c hc
  by_contra hnot
  rw [Metric.mem_closedBall, dist_zero_right] at hnot
  push_neg at hnot
  exact parameter_gt_two_escapes hnot hc

theorem ball_quarter_subset_mandelbrot :
    Metric.ball (0 : ℂ) (1 / 4 : ℝ) ⊆ MandelbrotSet := by
  intro c hc
  have hc_norm : ‖c‖ < (1 / 4 : ℝ) := by
    simpa [Metric.mem_ball, dist_zero_right] using hc
  refine ⟨(1 / 2 : ℝ), ?_⟩
  intro n
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [orbit_succ]
      change ‖orbit c 0 n ^ 2 + c‖ ≤ (1 / 2 : ℝ)
      calc
        ‖orbit c 0 n ^ 2 + c‖ ≤ ‖orbit c 0 n ^ 2‖ + ‖c‖ :=
          norm_add_le _ _
        _ = ‖orbit c 0 n‖ ^ 2 + ‖c‖ := by rw [Complex.norm_pow]
        _ ≤ (1 / 2 : ℝ) ^ 2 + (1 / 4 : ℝ) := by
          have hnonneg : 0 ≤ ‖orbit c 0 n‖ := norm_nonneg _
          nlinarith [ih, le_of_lt hc_norm]
        _ = (1 / 2 : ℝ) := by norm_num

theorem ball_quarter_subset_interior_mandelbrot :
    Metric.ball (0 : ℂ) (1 / 4 : ℝ) ⊆ interior MandelbrotSet :=
  interior_maximal ball_quarter_subset_mandelbrot Metric.isOpen_ball

theorem mandelbrot_eq_inter :
    MandelbrotSet =
      ⋂ n, {c : ℂ | ‖orbit c 0 n‖ ≤ (2 : ℝ)} := by
  ext c
  constructor
  · intro hc
    refine Set.mem_iInter.mpr fun n => ?_
    by_contra hgt
    have hc2 : ‖c‖ ≤ 2 := by
      simpa [Metric.mem_closedBall, dist_zero_right] using
        mandelbrot_subset_closedBall hc
    have hlarge : ¬ boundedOrbit c (orbit c 0 n) := by
      apply escapes_of_large_norm_and_ge_parameter
      · exact lt_of_not_ge hgt
      · exact hc2.trans (le_of_lt (lt_of_not_ge hgt))
    have hshift : boundedOrbit c (orbit c 0 n) := by
      rcases hc with ⟨M, hM⟩
      refine ⟨M, ?_⟩
      intro k
      rw [show orbit c (orbit c 0 n) k = orbit c 0 (n + k) by
        dsimp [orbit]
        rw [← Function.iterate_add_apply, add_comm]]
      exact hM (n + k)
    exact hlarge hshift
  · intro h
    refine ⟨2, ?_⟩
    intro n
    exact Set.mem_iInter.mp h n

theorem isClosed_mandelbrot : IsClosed MandelbrotSet := by
  rw [mandelbrot_eq_inter]
  apply isClosed_iInter
  intro n
  exact isClosed_le
    ((continuous_parameter_orbit n).norm) continuous_const

theorem isCompact_mandelbrot : IsCompact MandelbrotSet :=
  (isCompact_closedBall (0 : ℂ) 2).of_isClosed_subset
    isClosed_mandelbrot mandelbrot_subset_closedBall

end MLC.Quadratic
