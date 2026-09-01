import Mlc.Quadratic.Complex.Bottcher.SubharmonicMaxPrinciple

/-!
# The conformal Laplacian chain rule

This file supplies the single analytic fact that Mathlib lacks for **step 4** of the Schottky
route toward discharging axiom A: the *conformal* transformation law of the Laplacian under a
holomorphic change of variables,

`Δ (g ∘ f) x = ‖deriv f x‖² · (Δ g) (f x)`

for `f` holomorphic (analytic) at `x` and `g : ℂ → ℝ` twice continuously differentiable at
`f x`.  This is the mechanism by which negative curvature is preserved under holomorphic
pullback: pulling back a metric of curvature `≤ -1` on `ℂ \ {0,1}` via a holomorphic map keeps
curvature `≤ -1`, which is exactly what feeds `ahlfors_schwarz`.

## Proof outline

Working in the complexPlane Laplacian formula
`Δ h x = D²h(x)[1,1] + D²h(x)[I,I]` and using the line-restriction bridge
`iteratedFDeriv_two_apply_diag_eq_iteratedDeriv_line_of_contDiffAt`, each diagonal second
derivative `D²(g∘f)(x)[v,v]` becomes `iteratedDeriv 2 (t ↦ g (f (x + t • v))) 0`.  The
second-order chain rule `iteratedDeriv_vcomp_two` splits this into a Hessian term
`D²g(f x)[f' v, f' v]` and a gradient term `Dg(f x)[f'' v²]`.  Summing over the two directions
`v ∈ {1, I}`:

* the gradient term cancels because `1² + I² = 0` (`hgrad`);
* the Hessian term collapses to `‖f'‖² · Δg(f x)` because, for a symmetric-or-not bilinear form
  `D2`, the diagonal sum `D2 w w + D2 (w·I) (w·I)` equals `‖w‖² · (D2 1 1 + D2 I I)` — the cross
  terms cancel with no symmetry needed (`bilin_diag_sum`).
-/

namespace MLC.Quadratic

open Complex
open scoped Laplacian

variable {f : ℂ → ℂ} {x v : ℂ}

/-- The first derivative of a holomorphic map restricted to a real line through `x` in the
complex direction `v`: `d/ds f(x + s • v) = f'(x + t • v) · v`. -/
theorem line_deriv (t : ℝ) (hf : DifferentiableAt ℂ f (x + t • v)) :
    HasDerivAt (fun s : ℝ => f (x + s • v)) (deriv f (x + t • v) * v) t := by
  have hρ : HasDerivAt (fun s : ℝ => x + s • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  simpa [mul_comm] using (hf.hasDerivAt).scomp t hρ

/-- The second derivative of a holomorphic map along a real line through `x`:
`(d/ds)² f(x + s • v)|₀ = v² · f''(x)`. -/
theorem line_iteratedDeriv_two (hf : AnalyticAt ℂ f x) :
    iteratedDeriv 2 (fun s : ℝ => f (x + s • v)) 0 = v ^ 2 * deriv (deriv f) x := by
  have hopen : ∀ᶠ t : ℝ in nhds 0, AnalyticAt ℂ f (x + t • v) := by
    have hcont : Continuous (fun t : ℝ => x + t • v) := by fun_prop
    have h0 : (fun t : ℝ => x + t • v) 0 = x := by simp
    have := hf.eventually_analyticAt
    rw [← h0] at this
    exact hcont.continuousAt.eventually this
  have hderivEq : deriv (fun s : ℝ => f (x + s • v))
      =ᶠ[nhds 0] fun t : ℝ => deriv f (x + t • v) * v := by
    filter_upwards [hopen] with t ht
    exact (line_deriv t ht.differentiableAt).deriv
  rw [iteratedDeriv_succ, iteratedDeriv_one, hderivEq.deriv_eq]
  have hg : DifferentiableAt ℂ (deriv f) x := hf.deriv.differentiableAt
  have hpt : x + (0 : ℝ) • v = x := by simp
  have hρ : HasDerivAt (fun s : ℝ => x + s • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hgat : HasDerivAt (deriv f) (deriv (deriv f) x) (x + (0 : ℝ) • v) := by
    rw [hpt]; exact hg.hasDerivAt
  have hline2 : HasDerivAt (fun s : ℝ => deriv f (x + s • v)) (v • deriv (deriv f) x) 0 := by
    simpa [Function.comp] using hgat.scomp (0 : ℝ) hρ
  have hfin : HasDerivAt (fun t : ℝ => deriv f (x + t • v) * v)
      ((v • deriv (deriv f) x) * v) 0 := hline2.mul_const v
  rw [hfin.deriv, smul_eq_mul]; ring

/-- **Diagonal sum of a real bilinear form on `ℂ`.** For any continuous `ℝ`-bilinear form `D2`
on `ℂ`, `D2 w w + D2 (w·I) (w·I) = ‖w‖² · (D2 1 1 + D2 I I)`.  The cross terms cancel
automatically — no symmetry of `D2` is required. -/
theorem bilin_diag_sum (D2 : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) (w : ℂ) :
    D2 w w + D2 (w * I) (w * I) = ‖w‖ ^ 2 * (D2 1 1 + D2 I I) := by
  have key : ∀ a b : ℂ, D2 a b
      = a.re * b.re * D2 1 1 + a.re * b.im * D2 1 I
        + a.im * b.re * D2 I 1 + a.im * b.im * D2 I I := by
    intro a b
    have ha : a = a.re • (1 : ℂ) + a.im • I := by apply Complex.ext <;> simp
    have hb : b = b.re • (1 : ℂ) + b.im • I := by apply Complex.ext <;> simp
    conv_lhs => rw [ha, hb]
    simp only [map_add, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul]
    ring
  have hnorm : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  rw [key w w, key (w * I) (w * I), hnorm]
  simp only [Complex.mul_I_re, Complex.mul_I_im]
  ring

open InnerProductSpace in
/-- **Conformal Laplacian chain rule.** For `f` holomorphic at `x` and `g : ℂ → ℝ` twice
continuously differentiable at `f x`,
`Δ (g ∘ f) x = ‖deriv f x‖² · (Δ g) (f x)`.
This is the transformation law that makes negative curvature invariant under holomorphic
pullback. -/
theorem laplacian_comp_analytic {g : ℂ → ℝ} {f : ℂ → ℂ} {x : ℂ}
    (hf : AnalyticAt ℂ f x) (hg : ContDiffAt ℝ 2 g (f x)) :
    Δ (fun z => g (f z)) x = ‖deriv f x‖ ^ 2 * Δ g (f x) := by
  set A := deriv f x with hA
  set B := deriv (deriv f) x with hB
  have hfR : ContDiffAt ℝ 2 f x := (hf.contDiffAt).restrict_scalars ℝ
  have hgf : ContDiffAt ℝ 2 (fun z => g (f z)) x := hg.comp x hfR
  set D2 := fderiv ℝ (fderiv ℝ g) (f x) with hD2
  have hquad : ∀ w : ℂ, iteratedFDeriv ℝ 2 g (f x) (fun _ : Fin 2 => w) = D2 w w := by
    intro w; rw [iteratedFDeriv_two_apply]
  have hstep : ∀ v : ℂ, iteratedFDeriv ℝ 2 (fun z => g (f z)) x (fun _ : Fin 2 => v)
      = D2 (A * v) (A * v) + fderiv ℝ g (f x) (v ^ 2 * B) := by
    intro v
    rw [iteratedFDeriv_two_apply_diag_eq_iteratedDeriv_line_of_contDiffAt hgf v]
    have hinner : ContDiffAt ℝ 2 (fun t : ℝ => x + t • v) 0 :=
      (contDiff_const.add (contDiff_id.smul contDiff_const)).contDiffAt
    have hfRpt : ContDiffAt ℝ 2 f ((fun t : ℝ => x + t • v) 0) := by simpa using hfR
    have hφ : ContDiffAt ℝ 2 (fun t : ℝ => f (x + t • v)) 0 := by
      simpa [Function.comp] using hfRpt.comp 0 hinner
    have hvcomp := iteratedDeriv_vcomp_two (f := fun t : ℝ => f (x + t • v))
      (x := (0 : ℝ)) (g := g) (by simpa using hg) hφ
    have hcomp_eq : (fun t : ℝ => g (f (x + t • v))) = g ∘ (fun t => f (x + t • v)) := rfl
    rw [hcomp_eq, hvcomp]
    simp only []
    have h0v : x + (0 : ℝ) • v = x := by simp
    rw [h0v]
    have hd1 : deriv (fun t : ℝ => f (x + t • v)) 0 = A * v := by
      rw [(line_deriv 0 (by simpa using hf.differentiableAt)).deriv]; simp [hA, mul_comm]
    have hd2 : iteratedDeriv 2 (fun t : ℝ => f (x + t • v)) 0 = v ^ 2 * B :=
      line_iteratedDeriv_two hf
    rw [hd1, hd2, hquad (A * v)]
  have hlapg : Δ g (f x) = D2 1 1 + D2 I I := by
    rw [laplacian_eq_iteratedFDeriv_complexPlane]
    simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one, hD2]
  rw [laplacian_eq_iteratedFDeriv_complexPlane]
  simp only
  have e1 : (![(1 : ℂ), 1]) = fun _ : Fin 2 => (1 : ℂ) := by funext i; fin_cases i <;> rfl
  have eI : (![Complex.I, Complex.I]) = fun _ : Fin 2 => Complex.I := by
    funext i; fin_cases i <;> rfl
  rw [e1, eI, hstep 1, hstep I, hlapg]
  have hgrad : fderiv ℝ g (f x) ((1 : ℂ) ^ 2 * B) + fderiv ℝ g (f x) (I ^ 2 * B) = 0 := by
    rw [one_pow, one_mul, Complex.I_sq, show (-1 : ℂ) * B = -B by ring, map_neg]
    ring
  have hhess : D2 (A * 1) (A * 1) + D2 (A * I) (A * I) = ‖A‖ ^ 2 * (D2 1 1 + D2 I I) := by
    rw [mul_one]; exact bilin_diag_sum D2 A
  calc D2 (A * 1) (A * 1) + fderiv ℝ g (f x) ((1 : ℂ) ^ 2 * B)
        + (D2 (A * I) (A * I) + fderiv ℝ g (f x) (I ^ 2 * B))
      = (D2 (A * 1) (A * 1) + D2 (A * I) (A * I))
        + (fderiv ℝ g (f x) ((1 : ℂ) ^ 2 * B) + fderiv ℝ g (f x) (I ^ 2 * B)) := by ring
    _ = ‖A‖ ^ 2 * (D2 1 1 + D2 I I) := by rw [hhess, hgrad]; ring

end MLC.Quadratic
