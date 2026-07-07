import Mlc.Quadratic.Complex.Bottcher.LittlePicardFull

/-!
# The spherical derivative and its rescaling law (Zalcman foundations)

Toward **strong Montel** (a holomorphic family omitting two values is normal) via the modern
Zalcman route, this file introduces the **spherical derivative**

  `g#(z) = ‖g'(z)‖ / (1 + ‖g z‖²)`

— the norm of the derivative of `g` measured in the spherical (chordal) metric on the Riemann
sphere `ℂ ∪ {∞}`.  Its two defining features for Zalcman's rescaling lemma are:

* it is **nonnegative** and continuous where `g` is `C¹`;
* it obeys the **affine rescaling law**: if `h ζ = g (z₀ + ρ·ζ)` then
  `h#(ζ) = ‖ρ‖ · g#(z₀ + ρ·ζ)`.

The rescaling law is exactly the invariance that makes Zalcman's normalization `g#(0) = 1`
achievable: shrinking the scale `ρ` scales the spherical derivative by `‖ρ‖`, so a blow-up of
the spherical derivative can always be renormalized to value `1` at the centre.

All results are sorry-free and use only the Lean-core axioms.
-/

namespace MLC.Quadratic

open Complex

/-- **Spherical (chordal) derivative** of `g : ℂ → ℂ` at `z`:
`g#(z) = ‖g'(z)‖ / (1 + ‖g z‖²)`, the norm of `g'(z)` in the spherical metric of the Riemann
sphere. -/
noncomputable def sphericalDeriv (g : ℂ → ℂ) (z : ℂ) : ℝ :=
  ‖deriv g z‖ / (1 + ‖g z‖ ^ 2)

/-- The spherical derivative is nonnegative. -/
theorem sphericalDeriv_nonneg (g : ℂ → ℂ) (z : ℂ) : 0 ≤ sphericalDeriv g z :=
  div_nonneg (norm_nonneg _) (by positivity)

/-- The denominator `1 + ‖g z‖²` of the spherical derivative is strictly positive. -/
theorem one_add_normSq_pos (g : ℂ → ℂ) (z : ℂ) : (0 : ℝ) < 1 + ‖g z‖ ^ 2 := by positivity

/-- **Affine rescaling law for the spherical derivative.** If `h ζ = g (z₀ + ρ·ζ)`, then
`h#(ζ) = ‖ρ‖ · g#(z₀ + ρ·ζ)`.  This is the scale-covariance that underlies Zalcman's
renormalization `g#(0) = 1`. -/
theorem sphericalDeriv_comp_affine (g : ℂ → ℂ) (z₀ ρ ζ : ℂ)
    (hg : DifferentiableAt ℂ g (z₀ + ρ * ζ)) :
    sphericalDeriv (fun ζ => g (z₀ + ρ * ζ)) ζ = ‖ρ‖ * sphericalDeriv g (z₀ + ρ * ζ) := by
  have hin : HasDerivAt (fun ζ : ℂ => z₀ + ρ * ζ) ρ ζ := by
    simpa using ((hasDerivAt_id ζ).const_mul ρ).const_add z₀
  have hderiv : deriv (fun ζ => g (z₀ + ρ * ζ)) ζ = deriv g (z₀ + ρ * ζ) * ρ :=
    (hg.hasDerivAt.comp ζ hin).deriv
  rw [sphericalDeriv, sphericalDeriv, hderiv, norm_mul, mul_div_assoc]
  ring

/-- **The spherical derivative is continuous** where `g` is analytic (`C¹` suffices). -/
theorem continuousAt_sphericalDeriv {g : ℂ → ℂ} {z : ℂ} (hg : AnalyticAt ℂ g z) :
    ContinuousAt (sphericalDeriv g) z := by
  refine ContinuousAt.div (hg.deriv.continuousAt.norm)
    (continuousAt_const.add (hg.continuousAt.norm.pow 2)) ?_
  exact (one_add_normSq_pos g z).ne'

end MLC.Quadratic
