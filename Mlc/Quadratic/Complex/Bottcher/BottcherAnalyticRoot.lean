import Mlc.Quadratic.Complex.Bottcher.BottcherOnMTheory
import Mathlib.Analysis.Analytic.Binomial

namespace MLC

open Quadratic Complex Topology Set Filter

lemma analyticAt_one_add_cpow (a : ℂ) :
    AnalyticAt ℂ (fun x => (1 + x) ^ a) (0 : ℂ) := by
  exact (Complex.one_add_cpow_hasFPowerSeriesAt_zero (a := a)).analyticAt

lemma analyticAt_one_add_cpow_comp {h : ℂ → ℂ} {z : ℂ} (a : ℂ)
    (hh : AnalyticAt ℂ h z) (hh0 : h z = 0) :
    AnalyticAt ℂ (fun w => (1 + h w) ^ a) z := by
  have hpow : AnalyticAt ℂ (fun x => (1 + x) ^ a) (h z) := by
    simpa [hh0] using (analyticAt_one_add_cpow a)
  exact AnalyticAt.comp hpow hh

noncomputable def analytic_root_aux (h : ℂ → ℂ) (z : ℂ) (a : ℂ) : ℂ → ℂ :=
  let c := h z
  fun w => c ^ a * (1 + (h w / c - 1)) ^ a

lemma analytic_root_aux_analyticAt {h : ℂ → ℂ} {z : ℂ} {a : ℂ}
    (hh : AnalyticAt ℂ h z) (hc : h z ≠ 0) :
    AnalyticAt ℂ (analytic_root_aux h z a) z := by
  classical
  have h1 : AnalyticAt ℂ (fun w => h w / h z - 1) z := by
    have : AnalyticAt ℂ (fun w => h w / h z) z := by
      simpa [div_eq_mul_inv] using (hh.mul analyticAt_const)
    simpa using this.sub analyticAt_const
  have h10 : (fun w => h w / h z - 1) z = 0 := by
    simp [hc]
  have hpow : AnalyticAt ℂ (fun w => (1 + (h w / h z - 1)) ^ a) z :=
    analyticAt_one_add_cpow_comp a h1 h10
  simpa [analytic_root_aux] using (analyticAt_const.mul hpow)

lemma analytic_root_aux_pow_nat {h : ℂ → ℂ} {z : ℂ} {n : ℕ} (hn : n ≠ 0) :
    (analytic_root_aux h z ((1 : ℂ) / n)) ^ n =
      fun w => h z * (1 + (h w / h z - 1)) := by
  funext w
  have h1 : ((h z) ^ ((↑n : ℂ)⁻¹)) ^ n = h z := by
    have hmul : ((↑n : ℂ)⁻¹) * (n : ℂ) = (1 : ℂ) := by
      field_simp [hn]
    calc
      ((h z) ^ ((↑n : ℂ)⁻¹)) ^ n
          = (h z) ^ (((↑n : ℂ)⁻¹) * n) := by
              exact (Complex.cpow_mul_nat (h z) ((↑n : ℂ)⁻¹) n).symm
      _ = (h z) ^ (1 : ℂ) := by
              simp [hmul]
      _ = h z := by
              simp [Complex.cpow_one]
  have h2 : ((1 + (h w / h z - 1)) ^ ((↑n : ℂ)⁻¹)) ^ n =
      (1 + (h w / h z - 1)) := by
    have hmul : ((↑n : ℂ)⁻¹) * (n : ℂ) = (1 : ℂ) := by
      field_simp [hn]
    calc
      ((1 + (h w / h z - 1)) ^ ((↑n : ℂ)⁻¹)) ^ n
          = (1 + (h w / h z - 1)) ^ (((↑n : ℂ)⁻¹) * n) := by
              exact (Complex.cpow_mul_nat (1 + (h w / h z - 1)) ((↑n : ℂ)⁻¹) n).symm
      _ = (1 + (h w / h z - 1)) ^ (1 : ℂ) := by
              simp [hmul]
      _ = (1 + (h w / h z - 1)) := by
              simp [Complex.cpow_one]
  calc
    (analytic_root_aux h z ((1 : ℂ) / n) w) ^ n
        =
          ((h z) ^ ((↑n : ℂ)⁻¹)) ^ n *
            ((1 + (h w / h z - 1)) ^ ((↑n : ℂ)⁻¹)) ^ n := by
            simp [analytic_root_aux, div_eq_mul_inv, mul_pow]
    _ = h z * (1 + (h w / h z - 1)) := by
            rw [h1, h2]

lemma analytic_root_aux_eq_mul {h : ℂ → ℂ} {z : ℂ} (w : ℂ) (hc : h z ≠ 0) :
    h z * (1 + (h w / h z - 1)) = h w := by
  field_simp [hc]
  ring

end MLC
