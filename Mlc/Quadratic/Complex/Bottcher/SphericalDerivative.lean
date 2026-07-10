import Mlc.Quadratic.Complex.Bottcher.LittlePicardFull
import Mathlib.Analysis.Complex.LocallyUniformLimit

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

/-- **Zalcman normalization.**  Rescaling a function by `ρ = 1/f#(a)` about the point `a`
normalizes the spherical derivative of the renormalized function at the origin to `1`.  This is
the `g#(0) = 1` clause of Zalcman's rescaling lemma: with `g ζ = f (a + ρ·ζ)` and
`ρ = (f#(a))⁻¹` we get `g#(0) = 1`. -/
theorem sphericalDeriv_renormalize (f : ℂ → ℂ) (a : ℂ) (hf : DifferentiableAt ℂ f a)
    (hne : sphericalDeriv f a ≠ 0) :
    sphericalDeriv (fun ζ => f (a + ((sphericalDeriv f a : ℂ))⁻¹ * ζ)) 0 = 1 := by
  have h := sphericalDeriv_comp_affine f a ((sphericalDeriv f a : ℂ))⁻¹ 0 (by simpa using hf)
  simp only [mul_zero, add_zero] at h
  rw [h, norm_inv]
  rw [show ‖(sphericalDeriv f a : ℂ)‖ = sphericalDeriv f a by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sphericalDeriv_nonneg f a)]]
  rw [inv_mul_cancel₀ hne]

/-- **A spherical-derivative maximizer exists on a compact set.**  If `f` is analytic on a
nonempty compact set `K`, its spherical derivative — being continuous there — attains its maximum
on `K`.  This is the point-selection step of Zalcman's rescaling lemma: one renormalizes about a
point where the spherical derivative is largest. -/
theorem exists_isMaxOn_sphericalDeriv {f : ℂ → ℂ} {K : Set ℂ} (hK : IsCompact K)
    (hne : K.Nonempty) (hf : ∀ z ∈ K, AnalyticAt ℂ f z) :
    ∃ a ∈ K, IsMaxOn (sphericalDeriv f) K a :=
  hK.exists_isMaxOn hne (fun z hz => (continuousAt_sphericalDeriv (hf z hz)).continuousWithinAt)

/-- **The rescaled spherical-derivative bound of Zalcman's lemma.**  Suppose `a` maximizes the
weighted spherical derivative `(1-‖z‖²)·f#(z)` (so the pointwise inequality `hmax` holds at the
pullback point `w = a + ρ·ζ`, `ρ = 1/f#(a)`), and `w` lies strictly inside the unit disk.  Then
the renormalized function `g w = f (a + ρ·w)` obeys `g#(ζ) ≤ (1-‖a‖²)/(1-‖w‖²)`.  As `f#(a) → ∞`
the point `w → a` uniformly on compacta, so the right side `→ 1`, giving the locally uniform
bound `g_n#(ζ) ≲ 1` that feeds Marty/Arzelà–Ascoli in the rescaling lemma. -/
theorem sphericalDeriv_rescaled_le {f : ℂ → ℂ} {a ζ : ℂ}
    (hpos : 0 < sphericalDeriv f a)
    (hw : DifferentiableAt ℂ f (a + ((sphericalDeriv f a : ℂ))⁻¹ * ζ))
    (hwpos : 0 < 1 - ‖a + ((sphericalDeriv f a : ℂ))⁻¹ * ζ‖ ^ 2)
    (hmax : (1 - ‖a + ((sphericalDeriv f a : ℂ))⁻¹ * ζ‖ ^ 2)
              * sphericalDeriv f (a + ((sphericalDeriv f a : ℂ))⁻¹ * ζ)
            ≤ (1 - ‖a‖ ^ 2) * sphericalDeriv f a) :
    sphericalDeriv (fun w => f (a + ((sphericalDeriv f a : ℂ))⁻¹ * w)) ζ
      ≤ (1 - ‖a‖ ^ 2) / (1 - ‖a + ((sphericalDeriv f a : ℂ))⁻¹ * ζ‖ ^ 2) := by
  set s := sphericalDeriv f a with hs
  have hnorm : ‖((s : ℂ))⁻¹‖ = s⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpos.le]
  rw [sphericalDeriv_comp_affine f a ((s : ℂ))⁻¹ ζ hw, hnorm, inv_mul_eq_div,
    div_le_div_iff₀ hpos hwpos]
  calc sphericalDeriv f (a + ((s : ℂ))⁻¹ * ζ) * (1 - ‖a + ((s : ℂ))⁻¹ * ζ‖ ^ 2)
      = (1 - ‖a + ((s : ℂ))⁻¹ * ζ‖ ^ 2) * sphericalDeriv f (a + ((s : ℂ))⁻¹ * ζ) := by ring
    _ ≤ (1 - ‖a‖ ^ 2) * s := hmax

/-- **The Zalcman bound tends to `1` as the scale blows up.**  For `a` strictly inside the unit
disk, the pullback point `w = a + ζ/s` tends to `a` as `s → ∞`, so the rescaled bound
`(1-‖a‖²)/(1-‖w‖²)` of `sphericalDeriv_rescaled_le` tends to `1`.  Combined with that lemma this
is the locally uniform control `g_n#(ζ) → 1` used in Zalcman's rescaling lemma. -/
theorem tendsto_rescaled_ratio_one {a ζ : ℂ} (ha : ‖a‖ < 1) :
    Filter.Tendsto (fun s : ℝ => (1 - ‖a‖ ^ 2) / (1 - ‖a + ((s : ℂ))⁻¹ * ζ‖ ^ 2))
      Filter.atTop (nhds 1) := by
  have hden : (1 : ℝ) - ‖a‖ ^ 2 ≠ 0 := by nlinarith [norm_nonneg a]
  have h0 : Filter.Tendsto (fun s : ℝ => ((s : ℂ))⁻¹) Filter.atTop (nhds 0) := by
    have h : Filter.Tendsto (fun s : ℝ => (((s⁻¹ : ℝ)) : ℂ)) Filter.atTop (nhds (((0 : ℝ)) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto 0).comp tendsto_inv_atTop_zero
    simpa [Complex.ofReal_inv] using h
  have hw : Filter.Tendsto (fun s : ℝ => a + ((s : ℂ))⁻¹ * ζ) Filter.atTop (nhds a) := by
    have h1 : Filter.Tendsto (fun s : ℝ => ((s : ℂ))⁻¹ * ζ) Filter.atTop (nhds 0) := by
      simpa using h0.mul_const ζ
    simpa using (tendsto_const_nhds (x := a)).add h1
  have hnum : Filter.Tendsto (fun s : ℝ => (1 : ℝ) - ‖a + ((s : ℂ))⁻¹ * ζ‖ ^ 2)
      Filter.atTop (nhds (1 - ‖a‖ ^ 2)) :=
    tendsto_const_nhds.sub ((hw.norm.pow 2))
  have := (tendsto_const_nhds (x := 1 - ‖a‖ ^ 2)).div hnum hden
  simpa [div_self hden] using this

/-- **The spherical derivative is continuous under locally uniform limits of holomorphic maps.**
If `F i → g` locally uniformly on an open set `U` with each `F i` holomorphic on `U`, then at any
`z₀ ∈ U` the spherical derivatives converge: `(F i)#(z₀) → g#(z₀)`.  This uses Weierstrass
convergence of derivatives (`TendstoLocallyUniformlyOn.deriv`) together with pointwise
convergence of values.  In Zalcman's rescaling lemma it yields the crucial `g#(0) = 1`
(nonconstancy) for the limit of the renormalized family. -/
theorem tendsto_sphericalDeriv_of_tendstoLocallyUniformlyOn {ι : Type*} {p : Filter ι}
    {F : ι → ℂ → ℂ} {g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hF : TendstoLocallyUniformlyOn F g p U)
    (hFh : ∀ᶠ i in p, DifferentiableOn ℂ (F i) U) {z₀ : ℂ} (hz : z₀ ∈ U) :
    Filter.Tendsto (fun i => sphericalDeriv (F i) z₀) p (nhds (sphericalDeriv g z₀)) := by
  have hderiv : Filter.Tendsto (fun i => deriv (F i) z₀) p (nhds (deriv g z₀)) :=
    (TendstoLocallyUniformlyOn.deriv hF hFh hU).tendsto_at hz
  have hval : Filter.Tendsto (fun i => F i z₀) p (nhds (g z₀)) := hF.tendsto_at hz
  have hnum : Filter.Tendsto (fun i => ‖deriv (F i) z₀‖) p (nhds ‖deriv g z₀‖) := hderiv.norm
  have hden : Filter.Tendsto (fun i => 1 + ‖F i z₀‖ ^ 2) p (nhds (1 + ‖g z₀‖ ^ 2)) :=
    tendsto_const_nhds.add (hval.norm.pow 2)
  exact hnum.div hden (one_add_normSq_pos g z₀).ne'

end MLC.Quadratic
