import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Toward the subharmonic maximum principle (Ahlfors prerequisite)

This file begins the **subharmonic maximum principle** infrastructure that Ahlfors'
generalized Schwarz lemma (step 2 of the `ℂ \ {0,1}` / Schottky pipeline in
`HyperbolicMetric.lean`) requires, and which Mathlib currently lacks.

The classical `C²` proof of the maximum principle perturbs a subharmonic function
`u` (with `Δu ≥ 0`) to `u_ε = u + ε‖z‖²` (`Δu_ε > 0`) and uses the fact that a
function with strictly positive Laplacian has no interior maximum — because at an
interior maximum the Hessian is negative semidefinite, so its trace (the Laplacian)
is `≤ 0`.

The foundational analytic input is the **one-dimensional second-derivative test**:
at a local maximum of a `C²` real function, the second derivative is `≤ 0`. Mathlib
has the first-derivative test (`IsLocalMax.deriv_eq_zero`) but not this one; we prove
it here from Taylor's theorem with the Peano remainder (`taylor_tendsto`).

## Contents (sorry-free)

* `iteratedDeriv_two_nonpos_of_isLocalMax` — the 1D second-derivative test.
* `deriv_deriv_nonpos_of_isLocalMax` — the same, phrased as `deriv (deriv g) a ≤ 0`.
-/

namespace MLC.Quadratic

open Filter Topology Set Metric
open scoped Laplacian

/-- **One-dimensional second-derivative test.** If `g : ℝ → ℝ` is `C²` and has a
local maximum at `a`, then its second derivative there is nonpositive. -/
theorem iteratedDeriv_two_nonpos_of_isLocalMax {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g)
    {a : ℝ} (hmax : IsLocalMax g a) :
    iteratedDeriv 2 g a ≤ 0 := by
  set D := iteratedDeriv 2 g a with hD
  -- Taylor's theorem (Peano form) on `univ`, as a limit.
  have hgu : ContDiffOn ℝ 2 g univ := hg.contDiffOn
  have htt := taylor_tendsto (convex_univ) (mem_univ a) hgu
  rw [nhdsWithin_univ] at htt
  -- Explicit second-order Taylor polynomial, using `deriv g a = 0`.
  have hderiv : deriv g a = 0 := hmax.deriv_eq_zero
  have htaylor : ∀ x, taylorWithinEval g 2 univ a x
      = g a + (1 / 2) * (x - a) ^ 2 * D := by
    intro x
    rw [taylor_within_apply]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      iteratedDerivWithin_univ, iteratedDeriv_zero, iteratedDeriv_one, hderiv,
      Nat.factorial, Nat.cast_one, smul_eq_mul, pow_zero,
      pow_one, mul_one, mul_zero, inv_one, one_mul]
    rw [hD]; ring
  -- Rewrite the Taylor limit with the explicit polynomial.
  simp only [htaylor, smul_eq_mul] at htt
  -- Pass to the punctured neighbourhood filter.
  have htt' : Tendsto
      (fun x => ((x - a) ^ 2)⁻¹ * (g x - (g a + (1 / 2) * (x - a) ^ 2 * D)))
      (𝓝[≠] a) (𝓝 0) := htt.mono_left nhdsWithin_le_nhds
  -- On the punctured filter the Taylor quotient equals `(g x - g a)/(x-a)² - D/2`.
  have heq : (fun x => ((x - a) ^ 2)⁻¹ * (g x - (g a + (1 / 2) * (x - a) ^ 2 * D)))
      =ᶠ[𝓝[≠] a] (fun x => ((x - a) ^ 2)⁻¹ * (g x - g a) - D / 2) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hne : (x - a) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.2 hx)
    have key : ((x - a) ^ 2)⁻¹ * (x - a) ^ 2 = 1 := inv_mul_cancel₀ hne
    have expand : ((x - a) ^ 2)⁻¹ * (g x - (g a + (1 / 2) * (x - a) ^ 2 * D))
        = ((x - a) ^ 2)⁻¹ * (g x - g a)
          - (((x - a) ^ 2)⁻¹ * (x - a) ^ 2) * (D / 2) := by ring
    rw [expand, key, one_mul]
  rw [tendsto_congr' heq] at htt'
  -- Eventually the Taylor quotient is `≤ -D/2` (local max ⇒ `g x ≤ g a`).
  have hev : ∀ᶠ x in 𝓝[≠] a,
      ((x - a) ^ 2)⁻¹ * (g x - g a) - D / 2 ≤ -(D / 2) := by
    have hmax' : ∀ᶠ x in 𝓝[≠] a, g x ≤ g a :=
      (hmax.filter_mono nhdsWithin_le_nhds)
    filter_upwards [hmax'] with x hx
    have hinv : 0 ≤ ((x - a) ^ 2)⁻¹ := inv_nonneg.2 (sq_nonneg _)
    have : ((x - a) ^ 2)⁻¹ * (g x - g a) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hinv (by linarith)
    linarith
  -- Limit `0` is `≤ -D/2`, hence `D ≤ 0`.
  have h0 : (0 : ℝ) ≤ -(D / 2) := le_of_tendsto htt' hev
  linarith

/-- **Second-derivative test**, phrased via `deriv (deriv g)`. -/
theorem deriv_deriv_nonpos_of_isLocalMax {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g)
    {a : ℝ} (hmax : IsLocalMax g a) :
    deriv (deriv g) a ≤ 0 := by
  have h := iteratedDeriv_two_nonpos_of_isLocalMax hg hmax
  rwa [iteratedDeriv_succ, iteratedDeriv_one] at h

/-- Localized (`ContDiffAt`) form of the 1D second-derivative test: only local `C²`
smoothness at `a` is needed.  Adapts the global proof to a convex open ball on which
`g` is `ContDiffOn`, using `iteratedDerivWithin_of_isOpen` to identify the Taylor
coefficients with the ordinary iterated derivatives. -/
theorem iteratedDeriv_two_nonpos_of_isLocalMax_of_contDiffAt {g : ℝ → ℝ} {a : ℝ}
    (hg : ContDiffAt ℝ 2 g a) (hmax : IsLocalMax g a) :
    iteratedDeriv 2 g a ≤ 0 := by
  set D := iteratedDeriv 2 g a with hD
  obtain ⟨u, hu_mem, hu_cd⟩ := hg.contDiffOn (le_refl 2) (by simp)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hu_mem
  have hball_open : IsOpen (Metric.ball a δ) := Metric.isOpen_ball
  have ha_mem : a ∈ Metric.ball a δ := Metric.mem_ball_self hδ
  have hgu : ContDiffOn ℝ 2 g (Metric.ball a δ) := hu_cd.mono hball
  have htt := taylor_tendsto (convex_ball a δ) ha_mem hgu
  rw [hball_open.nhdsWithin_eq ha_mem] at htt
  have hderiv : deriv g a = 0 := hmax.deriv_eq_zero
  -- Taylor coefficients on the open ball are the ordinary iterated derivatives at `a`.
  have hidw : ∀ k, iteratedDerivWithin k g (Metric.ball a δ) a = iteratedDeriv k g a :=
    fun k => iteratedDerivWithin_of_isOpen hball_open ha_mem
  have htaylor : ∀ x, taylorWithinEval g 2 (Metric.ball a δ) a x
      = g a + (1 / 2) * (x - a) ^ 2 * D := by
    intro x
    rw [taylor_within_apply]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      hidw, iteratedDeriv_zero, iteratedDeriv_one, hderiv,
      Nat.factorial, Nat.cast_one, smul_eq_mul, pow_zero,
      pow_one, mul_one, mul_zero, inv_one, one_mul]
    rw [hD]; ring
  simp only [htaylor, smul_eq_mul] at htt
  have htt' : Tendsto
      (fun x => ((x - a) ^ 2)⁻¹ * (g x - (g a + (1 / 2) * (x - a) ^ 2 * D)))
      (𝓝[≠] a) (𝓝 0) := htt.mono_left nhdsWithin_le_nhds
  have heq : (fun x => ((x - a) ^ 2)⁻¹ * (g x - (g a + (1 / 2) * (x - a) ^ 2 * D)))
      =ᶠ[𝓝[≠] a] (fun x => ((x - a) ^ 2)⁻¹ * (g x - g a) - D / 2) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hne : (x - a) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.2 hx)
    have key : ((x - a) ^ 2)⁻¹ * (x - a) ^ 2 = 1 := inv_mul_cancel₀ hne
    have expand : ((x - a) ^ 2)⁻¹ * (g x - (g a + (1 / 2) * (x - a) ^ 2 * D))
        = ((x - a) ^ 2)⁻¹ * (g x - g a)
          - (((x - a) ^ 2)⁻¹ * (x - a) ^ 2) * (D / 2) := by ring
    rw [expand, key, one_mul]
  rw [tendsto_congr' heq] at htt'
  have hev : ∀ᶠ x in 𝓝[≠] a,
      ((x - a) ^ 2)⁻¹ * (g x - g a) - D / 2 ≤ -(D / 2) := by
    have hmax' : ∀ᶠ x in 𝓝[≠] a, g x ≤ g a := hmax.filter_mono nhdsWithin_le_nhds
    filter_upwards [hmax'] with x hx
    have hinv : 0 ≤ ((x - a) ^ 2)⁻¹ := inv_nonneg.2 (sq_nonneg _)
    have : ((x - a) ^ 2)⁻¹ * (g x - g a) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hinv (by linarith)
    linarith
  have h0 : (0 : ℝ) ≤ -(D / 2) := le_of_tendsto htt' hev
  linarith

/-- **Line-restriction of the second iterated derivative.** For a `C²` function on `ℂ`,
the pure second-order form `D²f(x)[v, v]` equals the ordinary second derivative at `0`
of the line restriction `t ↦ f (x + t • v)`. This is the bridge from the abstract
`iteratedFDeriv` in Mathlib's Laplacian formula to the one-variable second-derivative
test. -/
theorem iteratedFDeriv_two_apply_diag_eq_iteratedDeriv_line
    {f : ℂ → ℝ} (hf : ContDiff ℝ 2 f) (x v : ℂ) :
    iteratedFDeriv ℝ 2 f x (fun _ : Fin 2 => v)
      = iteratedDeriv 2 (fun t : ℝ => f (x + t • v)) 0 := by
  have hF₁ : ContDiff ℝ 2 (fun z : ℂ => f (x + z)) :=
    hf.comp (contDiff_const.add contDiff_id)
  set g : ℝ →L[ℝ] ℂ := (1 : ℝ →L[ℝ] ℝ).smulRight v with hg
  have hg1 : g 1 = v := by simp [hg]
  have hg0 : g 0 = 0 := by simp [hg]
  have hcomp : (fun t : ℝ => f (x + t • v)) = (fun z : ℂ => f (x + z)) ∘ g := by
    funext t; simp [hg]
  rw [hcomp, iteratedDeriv_eq_iteratedFDeriv,
      ContinuousLinearMap.iteratedFDeriv_comp_right g hF₁ 0 (le_refl 2),
      ContinuousMultilinearMap.compContinuousLinearMap_apply]
  simp only [hg0, hg1, iteratedFDeriv_comp_add_left, add_zero]

/-- Localized (`ContDiffAt`) version of the bridge lemma
`iteratedFDeriv_two_apply_diag_eq_iteratedDeriv_line`.  Only local `C²`-smoothness of `f`
at `x` is required — this is the version consumed by Ahlfors' lemma, whose metric
densities (e.g. `log (1 - ‖z‖²)`) are smooth only on the open disk, never globally.

The proof mirrors the global one but replaces the global composition lemma
`ContinuousLinearMap.iteratedFDeriv_comp_right` by its `Within` analogue on an open ball
where `f (x + ·)` is `ContDiffOn`, transferring back to the un-restricted iterated
derivative via `iteratedFDerivWithin_of_isOpen` (translation invariance is unconditional). -/
theorem iteratedFDeriv_two_apply_diag_eq_iteratedDeriv_line_of_contDiffAt
    {f : ℂ → ℝ} {x : ℂ} (hf : ContDiffAt ℝ 2 f x) (v : ℂ) :
    iteratedFDeriv ℝ 2 f x (fun _ : Fin 2 => v)
      = iteratedDeriv 2 (fun t : ℝ => f (x + t • v)) 0 := by
  -- `F₁ = f (x + ·)` is `C²` at `0`; extract an open ball `s` on which it is `ContDiffOn`.
  have hinner : ContDiffAt ℝ 2 (fun z : ℂ => x + z) 0 :=
    (contDiff_const.add contDiff_id).contDiffAt
  have h0 : ContDiffAt ℝ 2 f ((fun z : ℂ => x + z) 0) := by simpa using hf
  have hF₁at : ContDiffAt ℝ 2 (fun z : ℂ => f (x + z)) 0 := h0.comp 0 hinner
  obtain ⟨u, hu_mem, hu_cd⟩ := hF₁at.contDiffOn (le_refl 2) (by simp)
  obtain ⟨s, hs_sub, hs_open, hs0⟩ := _root_.mem_nhds_iff.mp hu_mem
  have hs_cd : ContDiffOn ℝ 2 (fun z : ℂ => f (x + z)) s := hu_cd.mono hs_sub
  set g : ℝ →L[ℝ] ℂ := (1 : ℝ →L[ℝ] ℝ).smulRight v with hgdef
  have hg1 : g 1 = v := by simp [hgdef]
  have hg0 : g 0 = 0 := by simp [hgdef]
  have hgx : g 0 ∈ s := by rw [hg0]; exact hs0
  have hpre_open : IsOpen (g ⁻¹' s) := hs_open.preimage g.continuous
  have hmem0 : (0 : ℝ) ∈ g ⁻¹' s := by rw [Set.mem_preimage, hg0]; exact hs0
  have hcomp : (fun t : ℝ => f (x + t • v)) = (fun z : ℂ => f (x + z)) ∘ g := by
    funext t; simp [hgdef]
  rw [hcomp, iteratedDeriv_eq_iteratedFDeriv]
  have e0 : iteratedFDerivWithin ℝ 2 ((fun z : ℂ => f (x + z)) ∘ g) (g ⁻¹' s) 0
      = iteratedFDeriv ℝ 2 ((fun z : ℂ => f (x + z)) ∘ g) 0 :=
    iteratedFDerivWithin_of_isOpen 2 hpre_open hmem0
  have ecomp : iteratedFDerivWithin ℝ 2 ((fun z : ℂ => f (x + z)) ∘ g) (g ⁻¹' s) 0
      = (iteratedFDerivWithin ℝ 2 (fun z : ℂ => f (x + z)) s (g 0)).compContinuousLinearMap
          (fun _ => g) :=
    ContinuousLinearMap.iteratedFDerivWithin_comp_right g hs_cd hs_open.uniqueDiffOn
      hpre_open.uniqueDiffOn hgx (le_refl 2)
  have eF₁ : iteratedFDerivWithin ℝ 2 (fun z : ℂ => f (x + z)) s (g 0)
      = iteratedFDeriv ℝ 2 (fun z : ℂ => f (x + z)) (g 0) :=
    iteratedFDerivWithin_of_isOpen 2 hs_open hgx
  rw [← e0, ecomp, ContinuousMultilinearMap.compContinuousLinearMap_apply, eF₁]
  simp only [hg0, hg1, iteratedFDeriv_comp_add_left, add_zero]

open InnerProductSpace in
/-- At an interior local maximum, the pure second-order form `D²u(z)[v, v]` along any
direction `v` is nonpositive (the diagonal of the Hessian is negative semidefinite). -/
theorem iteratedFDeriv_two_diag_nonpos_of_isLocalMax {u : ℂ → ℝ}
    (hu : ContDiff ℝ 2 u) {z : ℂ} (hmax : IsLocalMax u z) (v : ℂ) :
    iteratedFDeriv ℝ 2 u z (fun _ : Fin 2 => v) ≤ 0 := by
  rw [iteratedFDeriv_two_apply_diag_eq_iteratedDeriv_line hu]
  have hφc : ContDiff ℝ 2 (fun t : ℝ => u (z + t • v)) :=
    hu.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  have hc : Continuous (fun t : ℝ => z + t • v) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have htend : Filter.Tendsto (fun t : ℝ => z + t • v) (𝓝 0) (𝓝 z) := by
    have h := hc.tendsto 0; simpa using h
  have hlm : IsLocalMax (fun t : ℝ => u (z + t • v)) 0 := by
    filter_upwards [htend.eventually hmax] with t ht
    simpa using ht
  exact iteratedDeriv_two_nonpos_of_isLocalMax hφc hlm

open InnerProductSpace in
/-- **Laplacian at an interior maximum is nonpositive.** If `u : ℂ → ℝ` is `C²` and has
a local maximum at `z`, then `Δu(z) ≤ 0`. Equivalently, a function with strictly
positive Laplacian has no interior local maximum — the analytic heart of the
subharmonic maximum principle. -/
theorem laplacian_nonpos_of_isLocalMax {u : ℂ → ℝ} (hu : ContDiff ℝ 2 u)
    {z : ℂ} (hmax : IsLocalMax u z) :
    Δ u z ≤ 0 := by
  have hformula := laplacian_eq_iteratedFDeriv_complexPlane u
  have e1 : (![(1 : ℂ), 1]) = (fun _ : Fin 2 => (1 : ℂ)) := by
    funext i; fin_cases i <;> rfl
  have e2 : (![Complex.I, Complex.I]) = (fun _ : Fin 2 => Complex.I) := by
    funext i; fin_cases i <;> rfl
  have h1 := iteratedFDeriv_two_diag_nonpos_of_isLocalMax hu hmax 1
  have h2 := iteratedFDeriv_two_diag_nonpos_of_isLocalMax hu hmax Complex.I
  simp only [hformula, e1, e2]
  linarith

open InnerProductSpace in
/-- **Strictly subharmonic functions have no interior maximum.** If `Δu(z) > 0` then
`u` does not have a local maximum at `z`. This is the strict form used (via a
perturbation `u_ε = u + ε‖·‖²`) to derive the maximum principle for subharmonic `u`
(`Δu ≥ 0`). -/
theorem not_isLocalMax_of_laplacian_pos {u : ℂ → ℝ} (hu : ContDiff ℝ 2 u)
    {z : ℂ} (h : 0 < Δ u z) :
    ¬ IsLocalMax u z := by
  intro hmax
  have := laplacian_nonpos_of_isLocalMax hu hmax
  linarith

open InnerProductSpace in
/-- Localized diagonal-Hessian nonpositivity at an interior local max, under only
`ContDiffAt` at the point. -/
theorem iteratedFDeriv_two_diag_nonpos_of_isLocalMax_of_contDiffAt {u : ℂ → ℝ}
    {z : ℂ} (hu : ContDiffAt ℝ 2 u z) (hmax : IsLocalMax u z) (v : ℂ) :
    iteratedFDeriv ℝ 2 u z (fun _ : Fin 2 => v) ≤ 0 := by
  rw [iteratedFDeriv_two_apply_diag_eq_iteratedDeriv_line_of_contDiffAt hu]
  have hf0 : ContDiffAt ℝ 2 (fun t : ℝ => z + t • v) 0 :=
    (contDiff_const.add (contDiff_id.smul contDiff_const)).contDiffAt
  have hφc : ContDiffAt ℝ 2 (fun t : ℝ => u (z + t • v)) 0 := by
    apply ContDiffAt.comp 0 _ hf0
    simpa using hu
  have hc : Continuous (fun t : ℝ => z + t • v) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have htend : Filter.Tendsto (fun t : ℝ => z + t • v) (𝓝 0) (𝓝 z) := by simpa using hc.tendsto 0
  have hlm : IsLocalMax (fun t : ℝ => u (z + t • v)) 0 := by
    filter_upwards [htend.eventually hmax] with t ht; simpa using ht
  exact iteratedDeriv_two_nonpos_of_isLocalMax_of_contDiffAt hφc hlm

open InnerProductSpace in
/-- **Localized Laplacian-at-maximum principle.** If `u` is `C²` at `z` (only locally)
and has a local maximum at `z`, then `Δu(z) ≤ 0`.  This is the version consumed by
Ahlfors' lemma, whose comparison function is smooth only on the open disk. -/
theorem laplacian_nonpos_of_isLocalMax_of_contDiffAt {u : ℂ → ℝ}
    {z : ℂ} (hu : ContDiffAt ℝ 2 u z) (hmax : IsLocalMax u z) :
    Δ u z ≤ 0 := by
  have hformula := laplacian_eq_iteratedFDeriv_complexPlane u
  have e1 : (![(1 : ℂ), 1]) = (fun _ : Fin 2 => (1 : ℂ)) := by funext i; fin_cases i <;> rfl
  have e2 : (![Complex.I, Complex.I]) = (fun _ : Fin 2 => Complex.I) := by
    funext i; fin_cases i <;> rfl
  have h1 := iteratedFDeriv_two_diag_nonpos_of_isLocalMax_of_contDiffAt hu hmax 1
  have h2 := iteratedFDeriv_two_diag_nonpos_of_isLocalMax_of_contDiffAt hu hmax Complex.I
  simp only [hformula, e1, e2]
  linarith

open InnerProductSpace in
/-- Localized strict subharmonicity: `Δu(z) > 0` (with `u` only `C²` at `z`) rules out a
local maximum at `z`. -/
theorem not_isLocalMax_of_laplacian_pos_of_contDiffAt {u : ℂ → ℝ}
    {z : ℂ} (hu : ContDiffAt ℝ 2 u z) (h : 0 < Δ u z) :
    ¬ IsLocalMax u z := by
  intro hmax
  have := laplacian_nonpos_of_isLocalMax_of_contDiffAt hu hmax
  linarith

open RealInnerProductSpace in
/-- Second derivative of the squared-norm line restriction: `d²/dt² ‖x + t•v‖² = 2‖v‖²`. -/
theorem iteratedDeriv_two_normSq_line (x v : ℂ) :
    iteratedDeriv 2 (fun t : ℝ => ‖x + t • v‖ ^ 2) 0 = 2 * ‖v‖ ^ 2 := by
  -- The line restriction is an explicit quadratic polynomial in `t`.
  have hP : (fun t : ℝ => ‖x + t • v‖ ^ 2)
      = fun t : ℝ => ‖x‖ ^ 2 + 2 * ⟪x, v⟫ * t + ‖v‖ ^ 2 * t ^ 2 := by
    funext t
    have h1 : ⟪x, t • v⟫ = t * ⟪x, v⟫ := real_inner_smul_right x v t
    have h2 : ‖t • v‖ = |t| * ‖v‖ := by rw [norm_smul, Real.norm_eq_abs]
    rw [norm_add_sq_real, h1, h2, mul_pow, sq_abs]; ring
  rw [hP, iteratedDeriv_succ, iteratedDeriv_one]
  -- First derivative.
  have hgd : ∀ t : ℝ,
      HasDerivAt (fun t : ℝ => ‖x‖ ^ 2 + 2 * ⟪x, v⟫ * t + ‖v‖ ^ 2 * t ^ 2)
        (2 * ⟪x, v⟫ + ‖v‖ ^ 2 * (2 * t)) t := by
    intro t
    have e1 : HasDerivAt (fun t : ℝ => 2 * ⟪x, v⟫ * t) (2 * ⟪x, v⟫) t := by
      simpa using (hasDerivAt_id t).const_mul (2 * ⟪x, v⟫)
    have e2 : HasDerivAt (fun t : ℝ => ‖v‖ ^ 2 * t ^ 2) (‖v‖ ^ 2 * (2 * t)) t := by
      simpa using (hasDerivAt_pow 2 t).const_mul (‖v‖ ^ 2)
    have e0 : HasDerivAt (fun _ : ℝ => ‖x‖ ^ 2) 0 t := hasDerivAt_const t _
    simpa using (e0.add e1).add e2
  have hderiv_g : deriv (fun t : ℝ => ‖x‖ ^ 2 + 2 * ⟪x, v⟫ * t + ‖v‖ ^ 2 * t ^ 2)
      = fun t => 2 * ⟪x, v⟫ + ‖v‖ ^ 2 * (2 * t) := funext fun t => (hgd t).deriv
  rw [hderiv_g]
  -- Second derivative.
  have hgd2 : HasDerivAt (fun t : ℝ => 2 * ⟪x, v⟫ + ‖v‖ ^ 2 * (2 * t)) (‖v‖ ^ 2 * 2) 0 := by
    have h : HasDerivAt (fun t : ℝ => ‖v‖ ^ 2 * (2 * t)) (‖v‖ ^ 2 * 2) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_mul (2 : ℝ)).const_mul (‖v‖ ^ 2)
    exact h.const_add (2 * ⟪x, v⟫)
  rw [hgd2.deriv]; ring

open RealInnerProductSpace in
/-- The squared-norm line restriction `t ↦ ‖x + t•v‖²` is `C²` (indeed a real quadratic). -/
theorem contDiff_normSq_line (x v : ℂ) :
    ContDiff ℝ 2 (fun t : ℝ => ‖x + t • v‖ ^ 2) :=
  (contDiff_norm_sq ℝ).comp (contDiff_const.add (contDiff_id.smul contDiff_const))

open RealInnerProductSpace in
/-- First derivative of the squared-norm line restriction at `0`: `d/dt ‖x + t•v‖²|₀ = 2⟪x,v⟫`. -/
theorem deriv_normSq_line (x v : ℂ) :
    deriv (fun t : ℝ => ‖x + t • v‖ ^ 2) 0 = 2 * ⟪x, v⟫ := by
  have hP : (fun t : ℝ => ‖x + t • v‖ ^ 2)
      = fun t : ℝ => ‖x‖ ^ 2 + 2 * ⟪x, v⟫ * t + ‖v‖ ^ 2 * t ^ 2 := by
    funext t
    have h1 : ⟪x, t • v⟫ = t * ⟪x, v⟫ := real_inner_smul_right x v t
    have h2 : ‖t • v‖ = |t| * ‖v‖ := by rw [norm_smul, Real.norm_eq_abs]
    rw [norm_add_sq_real, h1, h2, mul_pow, sq_abs]; ring
  have hgd : HasDerivAt (fun t : ℝ => ‖x‖ ^ 2 + 2 * ⟪x, v⟫ * t + ‖v‖ ^ 2 * t ^ 2)
      (2 * ⟪x, v⟫ + ‖v‖ ^ 2 * (2 * 0)) 0 := by
    have e1 : HasDerivAt (fun t : ℝ => 2 * ⟪x, v⟫ * t) (2 * ⟪x, v⟫) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_mul (2 * ⟪x, v⟫)
    have e2 : HasDerivAt (fun t : ℝ => ‖v‖ ^ 2 * t ^ 2) (‖v‖ ^ 2 * (2 * 0)) 0 := by
      simpa using (hasDerivAt_pow 2 (0 : ℝ)).const_mul (‖v‖ ^ 2)
    have e0 : HasDerivAt (fun _ : ℝ => ‖x‖ ^ 2) 0 0 := hasDerivAt_const 0 _
    simpa using (e0.add e1).add e2
  rw [hP, hgd.deriv]; ring

open RealInnerProductSpace in
/-- Per-direction second derivative of a radial composite along a line, via the second-order
chain rule (`iteratedDeriv_vcomp_two`): for `F` that is `C²` at `‖x‖²`,
`d²/dt² F(‖x + t•v‖²)|₀ = F''(‖x‖²)·(2⟪x,v⟫)² + F'(‖x‖²)·(2‖v‖²)`. -/
theorem iteratedDeriv_two_comp_normSq_line {F : ℝ → ℝ} {x : ℂ}
    (hF : ContDiffAt ℝ 2 F (‖x‖ ^ 2)) (v : ℂ) :
    iteratedDeriv 2 (fun t : ℝ => F (‖x + t • v‖ ^ 2)) 0
      = iteratedDeriv 2 F (‖x‖ ^ 2) * (2 * ⟪x, v⟫) ^ 2 + deriv F (‖x‖ ^ 2) * (2 * ‖v‖ ^ 2) := by
  have hq0 : (fun t : ℝ => ‖x + t • v‖ ^ 2) 0 = ‖x‖ ^ 2 := by simp
  have hFq : ContDiffAt ℝ 2 F ((fun t : ℝ => ‖x + t • v‖ ^ 2) 0) := by rw [hq0]; exact hF
  have hcd : ContDiffAt ℝ 2 (fun t : ℝ => ‖x + t • v‖ ^ 2) 0 := (contDiff_normSq_line x v).contDiffAt
  have hchain := iteratedDeriv_vcomp_two (f := fun t : ℝ => ‖x + t • v‖ ^ 2) (x := (0 : ℝ)) hFq hcd
  rw [show (fun t : ℝ => F (‖x + t • v‖ ^ 2))
        = F ∘ (fun t : ℝ => ‖x + t • v‖ ^ 2) from rfl, hchain,
      iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, fderiv_eq_deriv_mul,
      hq0, deriv_normSq_line, iteratedDeriv_two_normSq_line]
  simp only [Fin.prod_const, smul_eq_mul]
  ring

open InnerProductSpace RealInnerProductSpace in
/-- **Radial Laplacian formula.** For `F` that is `C²` at `‖z‖²`,
`Δ (fun w => F ‖w‖²) z = 4·F'(‖z‖²) + 4‖z‖²·F''(‖z‖²)`.  This is the workhorse that
produces the curvatures of radial conformal metrics (e.g. the Poincaré density) needed
for Ahlfors' generalized Schwarz lemma. -/
theorem laplacian_comp_normSq {F : ℝ → ℝ} {z : ℂ} (hF : ContDiffAt ℝ 2 F (‖z‖ ^ 2)) :
    Δ (fun w : ℂ => F (‖w‖ ^ 2)) z
      = 4 * deriv F (‖z‖ ^ 2) + 4 * ‖z‖ ^ 2 * iteratedDeriv 2 F (‖z‖ ^ 2) := by
  have hcomp : ContDiffAt ℝ 2 (fun w : ℂ => F (‖w‖ ^ 2)) z :=
    hF.comp z (contDiff_norm_sq ℝ).contDiffAt
  have e1 : (![(1 : ℂ), 1]) = (fun _ : Fin 2 => (1 : ℂ)) := by funext i; fin_cases i <;> rfl
  have e2 : (![Complex.I, Complex.I]) = (fun _ : Fin 2 => Complex.I) := by
    funext i; fin_cases i <;> rfl
  have b1 := iteratedFDeriv_two_apply_diag_eq_iteratedDeriv_line_of_contDiffAt hcomp 1
  have b2 := iteratedFDeriv_two_apply_diag_eq_iteratedDeriv_line_of_contDiffAt hcomp Complex.I
  rw [iteratedDeriv_two_comp_normSq_line hF 1] at b1
  rw [iteratedDeriv_two_comp_normSq_line hF Complex.I] at b2
  -- Inner products with the two axis directions recover `‖z‖²`.
  have hi1 : (⟪z, (1 : ℂ)⟫ : ℝ) = z.re := by rw [Complex.inner]; simp
  have hiI : (⟪z, Complex.I⟫ : ℝ) = z.im := by rw [Complex.inner]; simp
  have hnorm : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  rw [laplacian_eq_iteratedFDeriv_complexPlane]
  simp only [e1, e2, b1, b2, hi1, hiI, norm_one, Complex.norm_I]
  linear_combination (-4 * iteratedDeriv 2 F (‖z‖ ^ 2)) * hnorm

open InnerProductSpace in
/-- **Disk curvature computation.** On the open unit disk, the logarithm of the Poincaré
weight `1 - ‖z‖²` is strictly superharmonic: `Δ log(1 - ‖z‖²) = -4/(1 - ‖z‖²)²`.
Instantiates the radial Laplacian formula at `F = log (1 - ·)`.  Feeds the curvature `-1`
identity `Δ log λ = λ²` for the Poincaré density `λ = 2/(1 - ‖z‖²)`. -/
theorem laplacian_log_one_sub_normSq {z : ℂ} (hz : ‖z‖ < 1) :
    Δ (fun w : ℂ => Real.log (1 - ‖w‖ ^ 2)) z = -4 / (1 - ‖z‖ ^ 2) ^ 2 := by
  have hs1 : (0 : ℝ) < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hne : (1 : ℝ) - ‖z‖ ^ 2 ≠ 0 := ne_of_gt hs1
  -- `F a = log (1 - a)`; first derivative `-(1 - a)⁻¹` wherever `1 - a ≠ 0`.
  have hderiv : ∀ a : ℝ, 1 - a ≠ 0 →
      HasDerivAt (fun s : ℝ => Real.log (1 - s)) (-(1 - a)⁻¹) a := by
    intro a ha
    have h1 : HasDerivAt (fun s : ℝ => 1 - s) (-1) a := by
      simpa using (hasDerivAt_id a).const_sub 1
    have := (Real.hasDerivAt_log ha).comp a h1
    simpa [mul_comm] using this
  have hF : ContDiffAt ℝ 2 (fun a : ℝ => Real.log (1 - a)) (‖z‖ ^ 2) :=
    (Real.contDiffAt_log.mpr hne).comp (‖z‖ ^ 2) (contDiff_const.sub contDiff_id).contDiffAt
  have hdF : deriv (fun a : ℝ => Real.log (1 - a)) (‖z‖ ^ 2) = -(1 - ‖z‖ ^ 2)⁻¹ :=
    (hderiv _ hne).deriv
  -- Second derivative via `deriv (deriv F)` on the open set `{a | 1 - a ≠ 0}`.
  have hopen : {a : ℝ | 1 - a ≠ 0} ∈ 𝓝 (‖z‖ ^ 2) :=
    (isOpen_ne.preimage (continuous_const.sub continuous_id)).mem_nhds hne
  have hderivF_eq : deriv (fun a : ℝ => Real.log (1 - a))
      =ᶠ[𝓝 (‖z‖ ^ 2)] fun a => -(1 - a)⁻¹ := by
    filter_upwards [hopen] with a ha using (hderiv a ha).deriv
  have hd2F : iteratedDeriv 2 (fun a : ℝ => Real.log (1 - a)) (‖z‖ ^ 2)
      = -((1 - ‖z‖ ^ 2) ^ 2)⁻¹ := by
    rw [iteratedDeriv_succ, iteratedDeriv_one, hderivF_eq.deriv_eq]
    have h1 : HasDerivAt (fun a : ℝ => 1 - a) (-1) (‖z‖ ^ 2) := by
      simpa using (hasDerivAt_id (‖z‖ ^ 2)).const_sub 1
    have h2 : HasDerivAt (fun a : ℝ => -(1 - a)⁻¹) (-(- -1 / (1 - ‖z‖ ^ 2) ^ 2)) (‖z‖ ^ 2) :=
      (h1.inv hne).neg
    rw [h2.deriv]; field_simp
  rw [laplacian_comp_normSq (F := fun a : ℝ => Real.log (1 - a)) hF, hdF, hd2F]
  field_simp
  ring

open InnerProductSpace in
/-- The Laplacian of a constant vanishes. -/
theorem laplacian_const (c : ℝ) (x : ℂ) : Δ (fun _ : ℂ => c) x = 0 := by
  rw [laplacian_eq_iteratedFDeriv_complexPlane, iteratedFDeriv_const_of_ne (by norm_num) c]
  simp

open InnerProductSpace in
/-- **General-radius disk curvature.** For a constant `R > ‖z‖²`,
`Δ log(R - ‖z‖²) = -4R/(R - ‖z‖²)²`.  With `R = r²` this is the curvature input for the
Poincaré density of the disk of radius `r`, used in the `r → 1` limit of Ahlfors' lemma. -/
theorem laplacian_log_const_sub_normSq {R : ℝ} {z : ℂ} (hz : ‖z‖ ^ 2 < R) :
    Δ (fun w : ℂ => Real.log (R - ‖w‖ ^ 2)) z = -4 * R / (R - ‖z‖ ^ 2) ^ 2 := by
  have hs1 : (0 : ℝ) < R - ‖z‖ ^ 2 := by linarith
  have hne : R - ‖z‖ ^ 2 ≠ 0 := ne_of_gt hs1
  have hderiv : ∀ a : ℝ, R - a ≠ 0 →
      HasDerivAt (fun s : ℝ => Real.log (R - s)) (-(R - a)⁻¹) a := by
    intro a ha
    have h1 : HasDerivAt (fun s : ℝ => R - s) (-1) a := by
      simpa using (hasDerivAt_id a).const_sub R
    have := (Real.hasDerivAt_log ha).comp a h1
    simpa [mul_comm] using this
  have hF : ContDiffAt ℝ 2 (fun a : ℝ => Real.log (R - a)) (‖z‖ ^ 2) :=
    (Real.contDiffAt_log.mpr hne).comp (‖z‖ ^ 2) (contDiff_const.sub contDiff_id).contDiffAt
  have hdF : deriv (fun a : ℝ => Real.log (R - a)) (‖z‖ ^ 2) = -(R - ‖z‖ ^ 2)⁻¹ :=
    (hderiv _ hne).deriv
  have hopen : {a : ℝ | R - a ≠ 0} ∈ 𝓝 (‖z‖ ^ 2) :=
    (isOpen_ne.preimage (continuous_const.sub continuous_id)).mem_nhds hne
  have hderivF_eq : deriv (fun a : ℝ => Real.log (R - a))
      =ᶠ[𝓝 (‖z‖ ^ 2)] fun a => -(R - a)⁻¹ := by
    filter_upwards [hopen] with a ha using (hderiv a ha).deriv
  have hd2F : iteratedDeriv 2 (fun a : ℝ => Real.log (R - a)) (‖z‖ ^ 2)
      = -((R - ‖z‖ ^ 2) ^ 2)⁻¹ := by
    rw [iteratedDeriv_succ, iteratedDeriv_one, hderivF_eq.deriv_eq]
    have h1 : HasDerivAt (fun a : ℝ => R - a) (-1) (‖z‖ ^ 2) := by
      simpa using (hasDerivAt_id (‖z‖ ^ 2)).const_sub R
    have h2 : HasDerivAt (fun a : ℝ => -(R - a)⁻¹) (-(- -1 / (R - ‖z‖ ^ 2) ^ 2)) (‖z‖ ^ 2) :=
      (h1.inv hne).neg
    rw [h2.deriv]; field_simp
  rw [laplacian_comp_normSq (F := fun a : ℝ => Real.log (R - a)) hF, hdF, hd2F]
  field_simp
  ring

open InnerProductSpace in
/-- The Laplacian commutes with negation. -/
theorem laplacian_neg {f : ℂ → ℝ} {x : ℂ} (hf : ContDiffAt ℝ 2 f x) :
    Δ (fun w : ℂ => -f w) x = -(Δ f x) := by
  have hcomp : (fun w : ℂ => -f w) = (-(ContinuousLinearMap.id ℝ ℝ)) ∘ f := by funext w; simp
  rw [hcomp, hf.laplacian_CLM_comp_left]; simp

open InnerProductSpace in
/-- **Curvature `-1` of the Poincaré metric.** The Poincaré log-density
`log λ = log 2 - log(1 - ‖z‖²)` (density `λ = 2/(1 - ‖z‖²)`) satisfies `Δ log λ = λ²`
on the open unit disk — Gaussian curvature identically `-1`.  This is the reference
metric of Ahlfors' generalized Schwarz lemma. -/
theorem laplacian_log_poincareDensity {z : ℂ} (hz : ‖z‖ < 1) :
    Δ (fun w : ℂ => Real.log 2 - Real.log (1 - ‖w‖ ^ 2)) z
      = (2 / (1 - ‖z‖ ^ 2)) ^ 2 := by
  have hs1 : (0 : ℝ) < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hg : ContDiffAt ℝ 2 (fun w : ℂ => Real.log (1 - ‖w‖ ^ 2)) z := by
    have hF : ContDiffAt ℝ 2 (fun a : ℝ => Real.log (1 - a)) (‖z‖ ^ 2) :=
      (Real.contDiffAt_log.mpr (ne_of_gt hs1)).comp _
        (contDiff_const.sub contDiff_id).contDiffAt
    exact hF.comp z (contDiff_norm_sq ℝ).contDiffAt
  have hrw : (fun w : ℂ => Real.log 2 - Real.log (1 - ‖w‖ ^ 2))
      = (fun _ : ℂ => Real.log 2) + (fun w : ℂ => -Real.log (1 - ‖w‖ ^ 2)) := by
    funext w; simp only [Pi.add_apply]; ring
  rw [hrw, ContDiffAt.laplacian_add contDiffAt_const hg.neg, laplacian_const,
      laplacian_neg hg, laplacian_log_one_sub_normSq hz]
  rw [zero_add]; field_simp; norm_num

open InnerProductSpace in
/-- **General-radius Poincaré curvature `-1`.** For the disk of radius `r`, the
log-density `log λ_r = log(2r) - log(r² - ‖z‖²)` (density `λ_r = 2r/(r² - ‖z‖²)`)
satisfies `Δ log λ_r = λ_r²`.  This is the family of reference metrics used in the
`r → 1` exhaustion of Ahlfors' generalized Schwarz lemma. -/
theorem laplacian_log_poincareDensity_radius {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : ‖z‖ < r) :
    Δ (fun w : ℂ => Real.log (2 * r) - Real.log (r ^ 2 - ‖w‖ ^ 2)) z
      = (2 * r / (r ^ 2 - ‖z‖ ^ 2)) ^ 2 := by
  have hz2 : ‖z‖ ^ 2 < r ^ 2 := by nlinarith [norm_nonneg z]
  have hs1 : (0 : ℝ) < r ^ 2 - ‖z‖ ^ 2 := by linarith
  have hg : ContDiffAt ℝ 2 (fun w : ℂ => Real.log (r ^ 2 - ‖w‖ ^ 2)) z := by
    have hF : ContDiffAt ℝ 2 (fun a : ℝ => Real.log (r ^ 2 - a)) (‖z‖ ^ 2) :=
      (Real.contDiffAt_log.mpr (ne_of_gt hs1)).comp _
        (contDiff_const.sub contDiff_id).contDiffAt
    exact hF.comp z (contDiff_norm_sq ℝ).contDiffAt
  have hrw : (fun w : ℂ => Real.log (2 * r) - Real.log (r ^ 2 - ‖w‖ ^ 2))
      = (fun _ : ℂ => Real.log (2 * r)) + (fun w : ℂ => -Real.log (r ^ 2 - ‖w‖ ^ 2)) := by
    funext w; simp only [Pi.add_apply]; ring
  rw [hrw, ContDiffAt.laplacian_add contDiffAt_const hg.neg, laplacian_const,
      laplacian_neg hg, laplacian_log_const_sub_normSq hz2]
  rw [zero_add]; field_simp; ring

open InnerProductSpace in
/-- **Laplacian of the squared norm.** `Δ(‖·‖²) = 4` on `ℂ`. The engine of the
perturbation `u_ε = u + ε‖·‖²` used to upgrade the strict maximum principle to the
subharmonic one. -/
theorem laplacian_normSq (x : ℂ) : Δ (fun z : ℂ => ‖z‖ ^ 2) x = 4 := by
  have hcd : ContDiff ℝ 2 (fun z : ℂ => ‖z‖ ^ 2) := contDiff_norm_sq ℝ
  have e1 : (![(1 : ℂ), 1]) = (fun _ : Fin 2 => (1 : ℂ)) := by
    funext i; fin_cases i <;> rfl
  have e2 : (![Complex.I, Complex.I]) = (fun _ : Fin 2 => Complex.I) := by
    funext i; fin_cases i <;> rfl
  have b1 := iteratedFDeriv_two_apply_diag_eq_iteratedDeriv_line hcd x 1
  have b2 := iteratedFDeriv_two_apply_diag_eq_iteratedDeriv_line hcd x Complex.I
  rw [iteratedDeriv_two_normSq_line] at b1 b2
  rw [laplacian_eq_iteratedFDeriv_complexPlane]
  simp only [e1, e2, b1, b2, norm_one, Complex.norm_I]
  norm_num

open InnerProductSpace in
/-- **Strict maximum principle.** A `C²` function that is *strictly* subharmonic
(`Δu > 0`) on an open ball attains its maximum over the closed ball on the boundary
sphere: no interior point can be a maximum. -/
theorem exists_isMaxOn_sphere_of_laplacian_pos {u : ℂ → ℝ} (hu : ContDiff ℝ 2 u)
    {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hpos : ∀ z ∈ ball c r, 0 < Δ u z) :
    ∃ w ∈ sphere c r, IsMaxOn u (closedBall c r) w := by
  have hcompact : IsCompact (closedBall c r) := isCompact_closedBall c r
  have hne : (closedBall c r).Nonempty := ⟨c, by simp [hr.le]⟩
  obtain ⟨p, hp, hpmax⟩ := hcompact.exists_isMaxOn hne hu.continuous.continuousOn
  refine ⟨p, ?_, hpmax⟩
  by_contra hps
  -- `p` is not on the sphere, so it lies in the open ball.
  have hpint : p ∈ ball c r := by
    rw [mem_ball]
    rcases lt_or_eq_of_le (mem_closedBall.1 hp) with h | h
    · exact h
    · exact absurd (mem_sphere.2 h) hps
  -- A global maximum over the closed ball at an interior point is a local maximum.
  have hnhd : closedBall c r ∈ 𝓝 p :=
    Filter.mem_of_superset (isOpen_ball.mem_nhds hpint) ball_subset_closedBall
  exact not_isLocalMax_of_laplacian_pos hu (hpos p hpint) (hpmax.isLocalMax hnhd)

open InnerProductSpace in
/-- **Subharmonic maximum principle.** A `C²` subharmonic function (`Δu ≥ 0` on an open
ball) attains its maximum over the closed ball on the boundary sphere. Proved from the
strict case by the perturbation `u_ε = u + ε‖·‖²` (`Δu_ε > 0`) and letting `ε → 0`. -/
theorem exists_isMaxOn_sphere_of_laplacian_nonneg {u : ℂ → ℝ} (hu : ContDiff ℝ 2 u)
    {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hsub : ∀ z ∈ ball c r, 0 ≤ Δ u z) :
    ∃ w ∈ sphere c r, IsMaxOn u (closedBall c r) w := by
  -- Maximum of `u` over the compact, nonempty boundary sphere.
  have hsphne : (sphere c r).Nonempty := NormedSpace.sphere_nonempty.mpr hr.le
  obtain ⟨w, hwmem, hwmax⟩ :=
    (isCompact_sphere c r).exists_isMaxOn hsphne hu.continuous.continuousOn
  refine ⟨w, hwmem, isMaxOn_iff.mpr fun z hz => ?_⟩
  set B : ℝ := (‖c‖ + r) ^ 2 with hB
  have hBpos : 0 < B := by rw [hB]; positivity
  -- For every `ε > 0`, `u z ≤ u w + ε·B`, using the strict maximum principle on `u_ε`.
  have key : ∀ ε : ℝ, 0 < ε → u z ≤ u w + ε * B := by
    intro ε hε
    have hΔpos : ∀ y ∈ ball c r, 0 < Δ (u + ε • fun p : ℂ => ‖p‖ ^ 2) y := by
      intro y hy
      have h₂ : ContDiffAt ℝ 2 (ε • fun p : ℂ => ‖p‖ ^ 2) y :=
        ((contDiff_norm_sq ℝ).const_smul ε).contDiffAt
      rw [(hu.contDiffAt).laplacian_add h₂,
          laplacian_smul ε (contDiff_norm_sq ℝ).contDiffAt, laplacian_normSq]
      have h4 : (0 : ℝ) < ε • (4 : ℝ) := by rw [smul_eq_mul]; positivity
      have := hsub y hy
      linarith
    have hpertCD : ContDiff ℝ 2 (u + ε • fun p : ℂ => ‖p‖ ^ 2) :=
      hu.add ((contDiff_norm_sq ℝ).const_smul ε)
    obtain ⟨wε, hwεmem, hwεmax⟩ :=
      exists_isMaxOn_sphere_of_laplacian_pos hpertCD hr hΔpos
    have h1 : (u + ε • fun p : ℂ => ‖p‖ ^ 2) z ≤ (u + ε • fun p : ℂ => ‖p‖ ^ 2) wε :=
      hwεmax hz
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1
    have hwε_u : u wε ≤ u w := hwmax hwεmem
    have hwε_norm : ‖wε‖ ^ 2 ≤ B := by
      have hd : ‖wε - c‖ = r := by rwa [mem_sphere_iff_norm] at hwεmem
      have hle : ‖wε‖ ≤ ‖c‖ + r := by
        calc ‖wε‖ = ‖(wε - c) + c‖ := by rw [sub_add_cancel]
          _ ≤ ‖wε - c‖ + ‖c‖ := norm_add_le _ _
          _ = ‖c‖ + r := by rw [hd]; ring
      rw [hB]; nlinarith [norm_nonneg wε]
    have hεnorm : ε * ‖wε‖ ^ 2 ≤ ε * B := mul_le_mul_of_nonneg_left hwε_norm hε.le
    have hz_nonneg : 0 ≤ ε * ‖z‖ ^ 2 := by positivity
    linarith
  -- Let `ε → 0`.
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  have hk := key (δ / B) (by positivity)
  rw [div_mul_cancel₀ _ (ne_of_gt hBpos)] at hk
  linarith

end MLC.Quadratic
