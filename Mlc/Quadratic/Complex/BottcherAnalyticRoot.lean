import Mlc.Quadratic.Complex.BottcherOnMTheory
import Mathlib.Analysis.Analytic.Binomial

namespace MLC

open Quadratic Complex Topology Set Filter

lemma analyticAt_one_add_cpow (a : ℂ) :
    AnalyticAt ℂ (fun x => (1 + x) ^ a) (0 : ℂ) := by
  exact (one_add_cpow_hasFPowerSeriesAt_zero (a := a)).analyticAt

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
  have h1 : ((h z) ^ ((1 : ℂ) / n)) ^ n = h z := by
    have : (h z) ^ ((1 : ℂ) / n * n) = (h z) ^ (1 : ℂ) := by
      field_simp [hn]
    simpa [Complex.cpow_mul_nat, this] using
      (Complex.cpow_mul_nat (h z) ((1 : ℂ) / n) n)
  have h2 : ((1 + (h w / h z - 1)) ^ ((1 : ℂ) / n)) ^ n =
      (1 + (h w / h z - 1)) := by
    have : (1 + (h w / h z - 1)) ^ ((1 : ℂ) / n * n) =
        (1 + (h w / h z - 1)) ^ (1 : ℂ) := by
      field_simp [hn]
    simpa [Complex.cpow_mul_nat, this] using
      (Complex.cpow_mul_nat (1 + (h w / h z - 1)) ((1 : ℂ) / n) n)
  simp [analytic_root_aux, mul_pow, h1, h2]

lemma analytic_root_aux_eq_mul {h : ℂ → ℂ} {z : ℂ} (w : ℂ) (hc : h z ≠ 0) :
    h z * (1 + (h w / h z - 1)) = h w := by
  field_simp [hc]
  ring

end MLC
