import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

namespace MLC

open Complex Filter Topology


lemma tendsto_log_of_tendsto_slitPlane {α : Type*} {l : Filter α}
    {f : α → ℂ} {x : ℂ}
    (hf : Tendsto f l (𝓝 x)) (hx : x ∈ Complex.slitPlane) :
    Tendsto (fun t => Complex.log (f t)) l (𝓝 (Complex.log x)) :=
  hf.clog hx

lemma tendsto_cpow_const_of_tendsto_slitPlane {α : Type*} {l : Filter α}
    {f : α → ℂ} {x a : ℂ}
    (hf : Tendsto f l (𝓝 x)) (hx : x ∈ Complex.slitPlane) :
    Tendsto (fun t => (f t) ^ a) l (𝓝 (x ^ a)) := by
  have hfa : AnalyticAt ℂ (fun z : ℂ => z) x := by
    simpa using (analyticAt_id : AnalyticAt ℂ (fun z : ℂ => z) x)
  have hga : AnalyticAt ℂ (fun _ : ℂ => a) x := by
    simpa using (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => a) x)
  have hcpow : AnalyticAt ℂ (fun z : ℂ => z ^ a) x :=
    hfa.cpow hga hx
  exact hcpow.continuousAt.tendsto.comp hf

lemma tendsto_cpow_const_of_tendsto_one {α : Type*} {l : Filter α}
    {f : α → ℂ} {a : ℂ}
    (hf : Tendsto f l (𝓝 (1 : ℂ))) :
    Tendsto (fun t => (f t) ^ a) l (𝓝 (1 : ℂ)) := by
  have h1 : (1 : ℂ) ∈ Complex.slitPlane := by
    exact one_mem_slitPlane
  have h :=
    tendsto_cpow_const_of_tendsto_slitPlane (f := f) (x := (1 : ℂ)) (a := a) hf h1
  convert h using 1
  simp

lemma tendsto_cpow_const_sub_one_of_tendsto_one {α : Type*} {l : Filter α}
    {f : α → ℂ} {a : ℂ}
    (hf : Tendsto f l (𝓝 (1 : ℂ))) :
    Tendsto (fun t => (f t) ^ a - (1 : ℂ)) l (𝓝 (0 : ℂ)) := by
  have hcpow : Tendsto (fun t => (f t) ^ a) l (𝓝 (1 : ℂ)) :=
    tendsto_cpow_const_of_tendsto_one (f := f) (a := a) hf
  have hconst : Tendsto (fun _ : α => (1 : ℂ)) l (𝓝 (1 : ℂ)) := tendsto_const_nhds
  simpa using hcpow.sub hconst

lemma cpow_mul_of_log_mul (x y a : ℂ) (hx : x ≠ 0) (hy : y ≠ 0)
    (hlog : Complex.log (x * y) = Complex.log x + Complex.log y) :
    (x * y) ^ a = x ^ a * y ^ a := by
  have hxy : x * y ≠ 0 := mul_ne_zero hx hy
  simp [cpow_def_of_ne_zero, hxy, hx, hy, hlog, mul_add, Complex.exp_add, mul_comm]

lemma cpow_mul_of_arg (x y a : ℂ) (hx : x ≠ 0) (hy : y ≠ 0)
    (harg : Complex.arg x + Complex.arg y ∈ Set.Ioc (-Real.pi) Real.pi) :
    (x * y) ^ a = x ^ a * y ^ a := by
  have hlog : Complex.log (x * y) = Complex.log x + Complex.log y :=
    (Complex.log_mul_eq_add_log_iff hx hy).2 harg
  exact cpow_mul_of_log_mul x y a hx hy hlog

lemma log_mul_of_real_pos (r : ℝ) (hr : 0 < r) (x : ℂ) (hx : x ≠ 0) :
    Complex.log ((r : ℂ) * x) = Real.log r + Complex.log x := by
  simpa using (Complex.log_ofReal_mul (r := r) (x := x) hr hx)

lemma log_ofReal_pos (r : ℝ) (hr : 0 < r) : Complex.log (r : ℂ) = Real.log r := by
  calc
    Complex.log (r : ℂ) = Complex.log ((r : ℂ) * (1 : ℂ)) := by simp
    _ = Real.log r + Complex.log (1 : ℂ) := by
          have h :=
            (Complex.log_ofReal_mul (r := r) (x := (1 : ℂ)) hr (by exact one_ne_zero))
          exact h
    _ = Real.log r := by simp

lemma cpow_mul_of_real_pos (r : ℝ) (hr : 0 < r) (x a : ℂ) (hx : x ≠ 0) :
    ((r : ℂ) * x) ^ a = (r : ℂ) ^ a * x ^ a := by
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hr)
  have hmul : (r : ℂ) * x ≠ 0 := mul_ne_zero hr' hx
  have hlog : Complex.log ((r : ℂ) * x) = Real.log r + Complex.log x :=
    log_mul_of_real_pos r hr x hx
  have hlogr : Complex.log (r : ℂ) = Real.log r := log_ofReal_pos r hr
  calc
    ((r : ℂ) * x) ^ a = Complex.exp (Complex.log ((r : ℂ) * x) * a) := by
      simp [cpow_def_of_ne_zero, hmul]
    _ = Complex.exp ((Real.log r + Complex.log x) * a) := by
      simp [hlog]
    _ = Complex.exp (Real.log r * a + Complex.log x * a) := by
      ring_nf
    _ = Complex.exp (Real.log r * a) * Complex.exp (Complex.log x * a) := by
      simp [Complex.exp_add]
    _ = (r : ℂ) ^ a * x ^ a := by
      simp [cpow_def_of_ne_zero, hr', hx, hlogr, mul_comm]

lemma slitPlane_mul_of_real_pos (x : ℂ) (hx : x ∈ Complex.slitPlane) (r : ℝ) (hr : 0 < r) :
    x * (r : ℂ) ∈ Complex.slitPlane := by
  have hx0 : x ≠ 0 := Complex.slitPlane_ne_zero hx
  have hxr0 : x * (r : ℂ) ≠ 0 := by
    have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hr)
    exact mul_ne_zero hx0 hr'
  have harg : Complex.arg (x * (r : ℂ)) ≠ Real.pi := by
    have hargx : Complex.arg x ≠ Real.pi := (Complex.mem_slitPlane_iff_arg.mp hx).1
    have harg' : Complex.arg (x * (r : ℂ)) = Complex.arg x := by
      simpa [mul_comm] using (Complex.arg_mul_real hr x)
    simpa [harg'] using hargx
  exact (Complex.mem_slitPlane_iff_arg.2 ⟨harg, hxr0⟩)

lemma mem_slitPlane_of_norm_sub_one_lt_one {y : ℂ} (hy : ‖y - (1 : ℂ)‖ < 1) :
    y ∈ Complex.slitPlane := by
  have h := Complex.mem_slitPlane_of_norm_lt_one (z := y - (1 : ℂ)) hy
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h

lemma re_pos_of_norm_sub_one_lt_one {y : ℂ} (hy : ‖y - (1 : ℂ)‖ < 1) :
    0 < y.re := by
  have hle : |(y - 1).re| ≤ ‖y - 1‖ := by
    simpa using (Complex.abs_re_le_norm (y - 1))
  have hle' : -‖y - 1‖ ≤ (y - 1).re := by
    exact (abs_le.mp hle).1
  have : (1 : ℝ) - ‖y - 1‖ ≤ y.re := by
    have h1 : (y - 1).re = y.re - 1 := by simp
    linarith [hle', h1]
  have hpos : 0 < (1 : ℝ) - ‖y - 1‖ := by linarith
  exact lt_of_lt_of_le hpos this

lemma abs_arg_lt_pi_div_two_of_re_pos {y : ℂ} (hy : 0 < y.re) :
    |Complex.arg y| < Real.pi / 2 := by
  have h := (Complex.abs_arg_lt_pi_div_two_iff (z := y)).2 (Or.inl hy)
  simpa using h

lemma arg_add_mem_Ioc_of_abs_lt_pi_div_two {a b : ℝ}
    (ha : |a| < Real.pi / 2) (hb : |b| < Real.pi / 2) :
    a + b ∈ Set.Ioc (-Real.pi) Real.pi := by
  have h1 : -Real.pi < a + b := by
    have ha' : -Real.pi / 2 < a := by
      have := (abs_lt.1 ha).1
      linarith
    have hb' : -Real.pi / 2 < b := by
      have := (abs_lt.1 hb).1
      linarith
    linarith
  have h2 : a + b ≤ Real.pi := by
    have ha' : a < Real.pi / 2 := (abs_lt.1 ha).2
    have hb' : b < Real.pi / 2 := (abs_lt.1 hb).2
    linarith
  exact ⟨h1, h2⟩


end MLC
