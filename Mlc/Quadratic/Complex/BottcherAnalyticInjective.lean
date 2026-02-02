import Mlc.Quadratic.Complex.BottcherOnMTheory
import Mlc.Quadratic.Complex.BottcherAnalyticRoot
import Mlc.Quadratic.Complex.BottcherAnalyticOrder
import Mathlib.Analysis.Analytic.Order
import Mathlib.RingTheory.RootsOfUnity.Complex

namespace MLC

open Quadratic Complex Topology Set Filter

theorem analyticOrderAt_sub_ne_one_of_deriv_eq_zero
    {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) (hderiv : deriv f z = 0) :
    analyticOrderAt (fun w => f w - f z) z ≠ 1 := by
  intro h
  have hge : (2 : ℕ∞) ≤ analyticOrderAt (fun w => f w - f z) z :=
    analyticOrderAt_sub_ge_two_of_deriv_eq_zero hf hderiv
  have : (2 : ℕ∞) ≤ (1 : ℕ∞) := by
    rw [h] at hge
    exact hge
  have hlt : (1 : ℕ∞) < (2 : ℕ∞) := by decide
  exact (not_lt_of_ge this) hlt

theorem pow_not_injOn_ball {n : ℕ} (hn : 1 < n) {r : ℝ} (hr : 0 < r) :
    ¬ Set.InjOn (fun w : ℂ => w ^ n) (Metric.ball 0 r) := by
  classical
  have hn0 : n ≠ 0 := by
    exact ne_of_gt (lt_trans zero_lt_one hn)
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)
  have hζ : IsPrimitiveRoot ζ n := Complex.isPrimitiveRoot_exp n hn0
  have hζne : ζ ≠ 1 := hζ.ne_one hn
  have hζnorm : ‖ζ‖ = 1 := hζ.norm'_eq_one hn0
  let w : ℂ := (r / 2 : ℝ)
  have hwne : w ≠ 0 := by
    have : (r / 2 : ℝ) ≠ 0 := by nlinarith
    have : ((r / 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast this
    simpa [w] using this
  have hwball : w ∈ Metric.ball (0 : ℂ) r := by
    have hr' : (r / 2 : ℝ) < r := by nlinarith
    have hnorm : ‖w‖ = r / 2 := by
      have hnonneg : 0 ≤ (r / 2 : ℝ) := by nlinarith
      simpa [w] using (Complex.norm_of_nonneg hnonneg)
    simpa [hnorm] using hr'
  have hwzball : ζ * w ∈ Metric.ball (0 : ℂ) r := by
    have : ‖ζ * w‖ < r := by
      have : ‖w‖ < r := by
        simpa using hwball
      simpa [norm_mul, hζnorm] using this
    simpa [Metric.ball, dist_eq_norm] using this
  have hneq : ζ * w ≠ w := by
    intro h
    have : ζ = 1 := by
      apply mul_right_cancel₀ hwne
      simpa [one_mul] using h
    exact hζne this
  have hpow : (ζ * w) ^ n = w ^ n := by
    simp [mul_pow, hζ.pow_eq_one]
  intro hinj
  have := hinj hwzball hwball hpow
  exact hneq (by simpa using this)

theorem not_injOn_of_local_pow
    {u : ℂ → ℂ} {u' z : ℂ} {n : ℕ}
    (h : HasStrictDerivAt u u' z) (h' : u' ≠ 0)
    (hu0 : u z = 0) (hn : 1 < n) :
    ¬ Set.InjOn (fun w => (u w) ^ n)
      ((h.hasStrictFDerivAt_equiv h').toOpenPartialHomeomorph u).source := by
  classical
  let e := (h.hasStrictFDerivAt_equiv h').toOpenPartialHomeomorph u
  have hmem : (0 : ℂ) ∈ e.target := by
    simpa [hu0] using (h.hasStrictFDerivAt_equiv h').image_mem_toOpenPartialHomeomorph_target
  have hnhds : e.target ∈ 𝓝 (0 : ℂ) := e.open_target.mem_nhds hmem
  rcases Metric.mem_nhds_iff.mp hnhds with ⟨r, hr, hrsub⟩
  have hnotinj :
      ¬ Set.InjOn (fun w : ℂ => w ^ n) (Metric.ball 0 r) :=
    pow_not_injOn_ball hn hr
  -- use the local inverse from `e` to transport non-injectivity
  intro hinj
  have htarget : Metric.ball (0 : ℂ) r ⊆ e.target := by
    intro w hw
    exact hrsub hw
  have hzinj : Set.InjOn (fun w : ℂ => w ^ n) (Metric.ball 0 r) := by
    -- restrict `hinj` through the local inverse
    intro w hw v hv hwv
    have hw' : e.symm w ∈ e.source := (e.symm_mapsTo (htarget hw))
    have hv' : e.symm v ∈ e.source := (e.symm_mapsTo (htarget hv))
    have hUw : u (e.symm w) = w := e.right_inv (htarget hw)
    have hUv : u (e.symm v) = v := e.right_inv (htarget hv)
    have hpow' : (u (e.symm w)) ^ n = (u (e.symm v)) ^ n := by
      simpa [hUw, hUv] using hwv
    have hEq := hinj hw' hv' hpow'
    have hEq' : w = v := by
      have := congrArg u hEq
      simpa [hUw, hUv] using this
    exact hEq'
  exact hnotinj hzinj

theorem not_injOn_of_local_pow_nhds
    {u : ℂ → ℂ} {u' z : ℂ} {n : ℕ} {s : Set ℂ}
    (h : HasStrictDerivAt u u' z) (h' : u' ≠ 0)
    (hu0 : u z = 0) (hn : 1 < n) (hs : s ∈ 𝓝 z) :
    ¬ Set.InjOn (fun w => (u w) ^ n) s := by
  classical
  let e := (h.hasStrictFDerivAt_equiv h').toOpenPartialHomeomorph u
  have hz : z ∈ e.source := (h.hasStrictFDerivAt_equiv h').mem_toOpenPartialHomeomorph_source
  have hmem : (0 : ℂ) ∈ e.target := by
    simpa [hu0] using (h.hasStrictFDerivAt_equiv h').image_mem_toOpenPartialHomeomorph_target
  have hsymm0 : e.symm 0 = z := by
    have hleft : e.symm (e z) = z := e.left_inv hz
    have hz0 : e z = 0 := by
      simp [e, hu0]
    simpa [hz0] using hleft
  have hcont : ContinuousAt e.symm (0 : ℂ) :=
    e.continuousAt_symm hmem
  have hpre : e.symm ⁻¹' s ∈ 𝓝 (0 : ℂ) := by
    have : s ∈ 𝓝 (e.symm 0) := by simpa [hsymm0] using hs
    exact hcont.preimage_mem_nhds this
  have htarget : e.target ∈ 𝓝 (0 : ℂ) := e.open_target.mem_nhds hmem
  have hinter : e.symm ⁻¹' s ∩ e.target ∈ 𝓝 (0 : ℂ) :=
    Filter.inter_mem hpre htarget
  rcases Metric.mem_nhds_iff.mp hinter with ⟨r, hr, hrsub⟩
  have hball : Metric.ball (0 : ℂ) r ⊆ e.symm ⁻¹' s := by
    intro w hw
    exact (hrsub hw).1
  have hballt : Metric.ball (0 : ℂ) r ⊆ e.target := by
    intro w hw
    exact (hrsub hw).2
  -- pick two distinct points in the ball with equal n-th powers
  have hnotinj : ¬ Set.InjOn (fun w : ℂ => w ^ n) (Metric.ball 0 r) :=
    pow_not_injOn_ball hn hr
  intro hinj
  -- build contradiction to `hnotinj` by transferring along `e.symm`
  have hzinj : Set.InjOn (fun w : ℂ => w ^ n) (Metric.ball 0 r) := by
    intro w hw v hv hwv
    have hw' : e.symm w ∈ s := hball hw
    have hv' : e.symm v ∈ s := hball hv
    have hUw : u (e.symm w) = w := e.right_inv (hballt hw)
    have hUv : u (e.symm v) = v := e.right_inv (hballt hv)
    have hpow' : (u (e.symm w)) ^ n = (u (e.symm v)) ^ n := by
      simpa [hUw, hUv] using hwv
    have hEq := hinj hw' hv' hpow'
    have hEq' : w = v := by
      have := congrArg u hEq
      simpa [hUw, hUv] using this
    exact hEq'
  exact hnotinj hzinj

theorem not_injOn_of_eq_pow_nhds
    {f u : ℂ → ℂ} {u' z : ℂ} {n : ℕ}
    (h : HasStrictDerivAt u u' z) (h' : u' ≠ 0) (hu0 : u z = 0) (hn : 1 < n)
    (h_eq : ∀ᶠ w in 𝓝 z, f w - f z = (u w) ^ n) :
    ∀ s ∈ 𝓝 z, ¬ Set.InjOn f s := by
  intro s hs hinj
  have hpre : {w | f w - f z = (u w) ^ n} ∈ 𝓝 z :=
    (Filter.eventually_iff).1 h_eq
  have hnhds : s ∩ {w | f w - f z = (u w) ^ n} ∈ 𝓝 z :=
    Filter.inter_mem hs hpre
  have hnot : ¬ Set.InjOn (fun w => (u w) ^ n) (s ∩ {w | f w - f z = (u w) ^ n}) :=
    not_injOn_of_local_pow_nhds h h' hu0 hn hnhds
  have hsubset : s ∩ {w | f w - f z = (u w) ^ n} ⊆ s := by
    intro w hw; exact hw.1
  have hinj' : Set.InjOn f (s ∩ {w | f w - f z = (u w) ^ n}) :=
    hinj.mono hsubset
  have hpowinj :
      Set.InjOn (fun w => (u w) ^ n) (s ∩ {w | f w - f z = (u w) ^ n}) := by
    intro w hw v hv hwv
    have hw' : f w - f z = (u w) ^ n := hw.2
    have hv' : f v - f z = (u v) ^ n := hv.2
    have : f w = f v := by
      have hsub : f w - f z = f v - f z := by simpa [hw', hv'] using hwv
      have hadd : f w + f z = f v + f z := (sub_eq_sub_iff_add_eq_add).1 hsub
      exact add_right_cancel hadd
    exact hinj' hw hv this
  exact hnot hpowinj

theorem not_injOn_nhds_of_analyticOrderAt_ge_two
    {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z)
    (hge : (2 : ℕ∞) ≤ analyticOrderAt (fun w => f w - f z) z) :
    ∀ s ∈ 𝓝 z, ¬ Set.InjOn f s := by
  classical
  set g : ℂ → ℂ := fun w => f w - f z
  by_cases htop : analyticOrderAt g z = ⊤
  · -- locally constant, hence not injective on any neighborhood
    have hconst : ∀ᶠ w in 𝓝 z, g w = 0 := (analyticOrderAt_eq_top (f := g) (z₀ := z)).1 htop
    intro s hs hinj
    have hpre : {w | g w = 0} ∈ 𝓝 z := (Filter.eventually_iff).1 hconst
    have hnhds : s ∩ {w | g w = 0} ∈ 𝓝 z := Filter.inter_mem hs hpre
    rcases Metric.mem_nhds_iff.mp hnhds with ⟨r, hr, hrsub⟩
    let w1 : ℂ := z + (r / 2 : ℝ)
    let w2 : ℂ := z - (r / 2 : ℝ)
    have hw1ball : w1 ∈ Metric.ball z r := by
      have hdist : dist w1 z = ‖((r / 2 : ℝ) : ℂ)‖ := by
        simp [w1, dist_eq_norm, sub_eq_add_neg, add_comm, add_left_comm]
      have hnorm : ‖((r / 2 : ℝ) : ℂ)‖ = r / 2 := by
        have hnonneg : 0 ≤ (r / 2 : ℝ) := by nlinarith [hr]
        simpa using (Complex.norm_of_nonneg hnonneg)
      have hlt : ‖((r / 2 : ℝ) : ℂ)‖ < r := by nlinarith [hnorm, hr]
      have : dist w1 z < r := by simpa [hdist] using hlt
      simpa [Metric.ball, dist_eq_norm] using this
    have hw2ball : w2 ∈ Metric.ball z r := by
      have hdist : dist w2 z = ‖((r / 2 : ℝ) : ℂ)‖ := by
        simp [w2, dist_eq_norm, sub_eq_add_neg, add_comm, add_left_comm]
      have hnorm : ‖((r / 2 : ℝ) : ℂ)‖ = r / 2 := by
        have hnonneg : 0 ≤ (r / 2 : ℝ) := by nlinarith [hr]
        simpa using (Complex.norm_of_nonneg hnonneg)
      have hlt : ‖((r / 2 : ℝ) : ℂ)‖ < r := by nlinarith [hnorm, hr]
      have : dist w2 z < r := by simpa [hdist] using hlt
      simpa [Metric.ball, dist_eq_norm] using this
    have hw1 : w1 ∈ s := (hrsub hw1ball).1
    have hw2 : w2 ∈ s := (hrsub hw2ball).1
    have hgw1 : g w1 = 0 := (hrsub hw1ball).2
    have hgw2 : g w2 = 0 := (hrsub hw2ball).2
    have hfeq : f w1 = f w2 := by
      have hsub : f w1 - f z = f w2 - f z := by
        simpa [g] using hgw1.trans hgw2.symm
      have hadd : f w1 + f z = f w2 + f z := (sub_eq_sub_iff_add_eq_add).1 hsub
      exact add_right_cancel hadd
    have hne : w1 ≠ w2 := by
      intro h
      have h' : ((r / 2 : ℝ) : ℂ) = -((r / 2 : ℝ) : ℂ) := by
        have h' : z + ((r / 2 : ℝ) : ℂ) = z + -((r / 2 : ℝ) : ℂ) := by
          simpa [w1, w2, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
        exact add_left_cancel h'
      have h'' : (r / 2 : ℝ) = -(r / 2 : ℝ) := by
        simpa using congrArg Complex.re h'
      have : (r / 2 : ℝ) = 0 := by nlinarith
      nlinarith
    exact hne (hinj hw1 hw2 hfeq)
  · -- finite order: use factorization and local nth-root
    have hgan : AnalyticAt ℂ g z := by
      simpa [g] using (hf.sub analyticAt_const)
    have hfin : analyticOrderAt g z ≠ ⊤ := by
      intro htop'; exact htop htop'
    rcases (AnalyticAt.analyticOrderAt_ne_top (hf := hgan)).1 hfin with ⟨h, hha, hhne, hfg⟩
    intro s hs hinj
    -- choose n from the analytic order
    set n : ℕ := analyticOrderNatAt g z
    have hn2 : 1 < n := by
      have hn : (n : ℕ∞) = analyticOrderAt g z := by
        simpa [n] using (Nat.cast_analyticOrderNatAt (f := g) (z₀ := z) hfin)
      have : (2 : ℕ∞) ≤ (n : ℕ∞) := by simpa [hn] using hge
      exact_mod_cast this
    have hc : h z ≠ 0 := hhne
    let r := analytic_root_aux h z ((1 : ℂ) / n)
    let u : ℂ → ℂ := fun w => (w - z) * r w
    have hroot : ∀ w, (r w) ^ n = h w := by
      intro w
      have hrfun :
          (analytic_root_aux h z ((1 : ℂ) / n)) ^ n =
            fun w => h z * (1 + (h w / h z - 1)) :=
        analytic_root_aux_pow_nat (h := h) (z := z) (n := n)
          (by exact ne_of_gt (lt_trans zero_lt_one hn2))
      have hr : (r w) ^ n = h z * (1 + (h w / h z - 1)) := by
        have := congrArg (fun f => f w) hrfun
        simpa [r] using this
      calc
        (r w) ^ n = h z * (1 + (h w / h z - 1)) := hr
        _ = h w := analytic_root_aux_eq_mul (h := h) (z := z) w hc
    have hEq : ∀ᶠ w in 𝓝 z, f w - f z = (u w) ^ n := by
      have hpre : ∀ᶠ w in 𝓝 z, g w = (w - z) ^ n • h w := hfg
      filter_upwards [hpre] with w hw
      have : (u w) ^ n = (w - z) ^ n * h w := by
        simp [u, mul_pow, hroot, mul_comm]
      simpa [g, smul_eq_mul, this] using hw
    have hur : AnalyticAt ℂ r z :=
      analytic_root_aux_analyticAt (h := h) (z := z) (a := (1 : ℂ) / n) hha hc
    have hu : AnalyticAt ℂ u z := by
      have hlin : AnalyticAt ℂ (fun w => w - z) z := analyticAt_id.sub analyticAt_const
      simpa [u] using hlin.mul hur
    have hderiv : deriv u z ≠ 0 := by
      have hderiv' : deriv u z = r z := by
        have hdiff1 : DifferentiableAt ℂ (fun w => w - z) z :=
          (differentiableAt_id.sub (differentiableAt_const (c := z)))
        have hdiff2 : DifferentiableAt ℂ r z := hur.differentiableAt
        have hmul := deriv_mul hdiff1 hdiff2
        have hderiv1 : deriv (fun w => w - z) z = 1 := by
          simp
        have hval : (fun w => w - z) z = 0 := by simp
        simpa [u, hderiv1, hval] using hmul
      have hz0 : r z ≠ 0 := by
        have : r z = (h z) ^ ((1 : ℂ) / n) := by
          simp [r, analytic_root_aux, hc]
        have : r z ≠ 0 := by
          intro hzero
          have hzero' : h z = 0 := by
            have h' := (Complex.cpow_eq_zero_iff (h z) ((1 : ℂ) / n)).1
            have h'' := h' (by simpa [this] using hzero)
            exact h''.1
          exact hc hzero'
        exact this
      simpa [hderiv'] using hz0
    have hstrict : HasStrictDerivAt u (deriv u z) z := hu.hasStrictDerivAt
    exact not_injOn_of_eq_pow_nhds hstrict hderiv (by simp [u]) hn2 hEq s hs hinj

end MLC
