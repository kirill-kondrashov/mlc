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
  have h' : deriv f z ≠ 0 := by
    exact (hf.analyticOrderAt_sub_eq_one_of_deriv_ne_zero).mp h
  exact h' hderiv

theorem pow_not_injOn_ball {n : ℕ} (hn : 1 < n) {r : ℝ} (hr : 0 < r) :
    ¬ Set.InjOn (fun w : ℂ => w ^ n) (Metric.ball 0 r) := by
  classical
  have hn0 : n ≠ 0 := by
    exact ne_of_gt (lt_trans zero_lt_one hn)
  let ζ : ℂ := Complex.exp (2 * π * I / n)
  have hζ : IsPrimitiveRoot ζ n := Complex.isPrimitiveRoot_exp n hn0
  have hζne : ζ ≠ 1 := hζ.ne_one hn
  have hζnorm : ‖ζ‖ = 1 := hζ.norm'_eq_one hn0
  let w : ℂ := (r / 2 : ℝ)
  have hwne : w ≠ 0 := by
    have : (r / 2 : ℝ) ≠ 0 := by nlinarith
    exact_mod_cast this
  have hwball : w ∈ Metric.ball (0 : ℂ) r := by
    have hr' : (r / 2 : ℝ) < r := by nlinarith
    have hnorm : ‖w‖ = r / 2 := by
      have hnonneg : 0 ≤ (r / 2 : ℝ) := by nlinarith
      simpa [w] using (Complex.norm_of_nonneg hnonneg)
    simpa [hnorm] using hr'
  have hwzball : ζ * w ∈ Metric.ball (0 : ℂ) r := by
    have hnorm : ‖ζ * w‖ = ‖w‖ := by
      simp [norm_mul, hζnorm]
    have : ‖w‖ < r := by
      simpa using hwball
    simpa [hnorm] using this
  have hneq : ζ * w ≠ w := by
    intro h
    have : ζ = 1 := by
      apply mul_right_cancel₀ (a := w)
      simpa [mul_comm] using h
    exact hζne this
  have hpow : (ζ * w) ^ n = w ^ n := by
    simp [mul_pow, hζ.pow_eq_one, hn0]
  intro hinj
  have := hinj hwzball hwball hpow
  exact hneq (by simpa [mul_comm] using this.symm)

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
    simpa [hu0] using (e.left_inv hz)
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
  have hnot : ¬ Set.InjOn (fun w => (u w) ^ n) s :=
    not_injOn_of_local_pow_nhds h h' hu0 hn hs
  have hpre : {w | f w - f z = (u w) ^ n} ∈ 𝓝 z :=
    (Filter.eventually_iff).1 h_eq
  have hnhds : s ∩ {w | f w - f z = (u w) ^ n} ∈ 𝓝 z :=
    Filter.inter_mem hs hpre
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
      have : f w - f z = f v - f z := by simpa [hw', hv'] using hwv
      linarith
    exact hinj' hw hv this
  exact hnot (hpowinj.mono hsubset)

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
    let w1 : ℂ := (r / 2 : ℝ)
    let w2 : ℂ := -(r / 2 : ℝ)
    have hw1 : w1 ∈ s := (hrsub (by
      have : (r / 2 : ℝ) < r := by nlinarith
      have : ‖w1‖ < r := by
        have hnonneg : 0 ≤ (r / 2 : ℝ) := by nlinarith
        simpa [w1] using (this)
      simpa [Metric.ball, dist_eq_norm] using this)).1
    have hw2 : w2 ∈ s := (hrsub (by
      have : (r / 2 : ℝ) < r := by nlinarith
      have : ‖w2‖ < r := by
        have hnonneg : 0 ≤ (r / 2 : ℝ) := by nlinarith
        simpa [w2, norm_neg] using (this)
      simpa [Metric.ball, dist_eq_norm] using this)).1
    have hgw1 : g w1 = 0 := (hrsub (by
      have : ‖w1‖ < r := by
        have : (r / 2 : ℝ) < r := by nlinarith
        have hnonneg : 0 ≤ (r / 2 : ℝ) := by nlinarith
        simpa [w1] using (this)
      simpa [Metric.ball, dist_eq_norm] using this)).2
    have hgw2 : g w2 = 0 := (hrsub (by
      have : ‖w2‖ < r := by
        have : (r / 2 : ℝ) < r := by nlinarith
        have hnonneg : 0 ≤ (r / 2 : ℝ) := by nlinarith
        simpa [w2, norm_neg] using (this)
      simpa [Metric.ball, dist_eq_norm] using this)).2
    have hfeq : f w1 = f w2 := by
      have : f w1 - f z = f w2 - f z := by simpa [g] using congrArg id (by simpa [g] using hgw1.trans hgw2.symm)
      linarith
    have hne : w1 ≠ w2 := by
      intro h
      have : (r / 2 : ℝ) = 0 := by
        simpa [w1, w2] using congrArg Complex.re h
      nlinarith
    exact hne (hinj hw1 hw2 hfeq)
  · -- finite order: use factorization and local nth-root
    rcases (analyticOrderAt_eq_natCast (f := g) (z₀ := z) (n := (analyticOrderAt g z).toNat)
      (by
        have : AnalyticAt ℂ g z := by
          simpa [g] using (hf.sub analyticAt_const)
        exact this)).1 ?_ with ⟨h, hha, hhne, hfg⟩
    · intro s hs hinj
      -- choose n from the analytic order
      set n : ℕ := analyticOrderNatAt g z
      have hn2 : 1 < n := by
        have hge' : (2 : ℕ∞) ≤ analyticOrderAt g z := hge
        -- conclude 2 ≤ n
        have hfin : analyticOrderAt g z ≠ ⊤ := by
          intro htop'; exact htop htop'
        have hn : (n : ℕ∞) = analyticOrderAt g z := by
          simpa [analyticOrderNatAt, Nat.cast_analyticOrderNatAt hfin] using rfl
        have : (2 : ℕ∞) ≤ (n : ℕ∞) := by simpa [hn] using hge'
        -- in ℕ, 2 ≤ n
        exact_mod_cast this
      have hc : h z ≠ 0 := hhne
      let r := analytic_root_aux h z ((1 : ℂ) / n)
      let u : ℂ → ℂ := fun w => (w - z) * r w
      have hroot : ∀ w, (r w) ^ n = h w := by
        intro w
        have hr : (r w) ^ n = h z * (1 + (h w / h z - 1)) := by
          simpa [r, analytic_root_aux] using (analytic_root_aux_pow_nat (h := h) (z := z) (n := n)
            (by exact ne_of_gt (lt_trans zero_lt_one hn2)) w)
        simpa [analytic_root_aux_eq_mul (h := h) (z := z) w hc] using hr
      have hEq : ∀ᶠ w in 𝓝 z, f w - f z = (u w) ^ n := by
        have hpre : ∀ᶠ w in 𝓝 z, g w = (w - z) ^ n * h w := hfg
        filter_upwards [hpre] with w hw
        have : (u w) ^ n = (w - z) ^ n * h w := by
          simp [u, mul_pow, hroot, mul_comm, mul_left_comm, mul_assoc]
        simpa [g, this] using hw
      have hur : AnalyticAt ℂ r z := analytic_root_aux_analyticAt (h := h) (z := z) (a := (1 : ℂ) / n) hha hc
      have hu : AnalyticAt ℂ u z := by
        have hlin : AnalyticAt ℂ (fun w => w - z) z := analyticAt_id.sub analyticAt_const
        simpa [u] using hlin.mul hur
      have hderiv : deriv u z ≠ 0 := by
        have hderiv' : deriv u z = r z := by
          have hdiff1 : DifferentiableAt ℂ (fun w => w - z) z := by
            simpa [sub_eq_add_neg] using (differentiableAt_id.add_const (-z))
          have hdiff2 : DifferentiableAt ℂ r z := hur.differentiableAt
          have hmul := deriv_mul hdiff1 hdiff2
          have hderiv1 : deriv (fun w => w - z) z = 1 := by
            simpa [sub_eq_add_neg] using (deriv_add_const (f := fun w : ℂ => w) (c := -z) (x := z))
          have hval : (fun w => w - z) z = 0 := by simp
          simpa [u, hderiv1, hval] using hmul
        have hz0 : r z ≠ 0 := by
          -- `r z = (h z)^(1/n)`; this is nonzero since `h z ≠ 0`.
          have : r z = (h z) ^ ((1 : ℂ) / n) := by
            simp [r, analytic_root_aux, hc]
          have : r z ≠ 0 := by
            intro hzero
            have hzero' : h z = 0 := by
              have := (Complex.cpow_eq_zero_iff (h z) ((1 : ℂ) / n)).1
              have h' := this (by simpa [this] using hzero)
              exact h'.1
            exact hc hzero'
          exact this
        simpa [hderiv'] using hz0
      have hstrict : HasStrictDerivAt u (deriv u z) z := hu.hasStrictDerivAt
      exact not_injOn_of_eq_pow_nhds hstrict hderiv (by simp [u]) hn2 hEq s hs hinj
    · -- analytic order equals its nat cast
      have hfin : analyticOrderAt g z ≠ ⊤ := by
        intro htop'; exact htop htop'
      simpa [analyticOrderNatAt, Nat.cast_analyticOrderNatAt hfin]

end MLC
