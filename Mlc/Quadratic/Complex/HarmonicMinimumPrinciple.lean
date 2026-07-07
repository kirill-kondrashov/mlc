import Mathlib.Analysis.Complex.Harmonic.Analytic
import Mathlib.Analysis.Complex.Harmonic.MeanValue
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Minimum principle for harmonic functions on the complex plane

A real-valued function that is harmonic on a connected open set and attains an
interior minimum is constant on that set.

The proof is the standard reduction to the maximum modulus principle: locally a
harmonic `f` equals `Re ∘ F` for a holomorphic `F`
(`harmonic_is_realOfHolomorphic`), so `‖exp (-F)‖ = exp (-f)`.  An interior
minimum of `f` is a local maximum of `‖exp (-F)‖`, hence
`norm_eventually_eq_of_isLocalMax` forces `f` to be locally constant.  A
connectedness (clopen) argument globalises this to the whole set.

This is `LINCHPIN 2` of route (a) in `plan/PLAN_00_frontier_overview.md`: it is one
of the two analysis inputs needed to prove `{z | G_c z < ε}` connected directly,
discharging the unsound radial-proxy axioms 2 and 3.
-/

open Complex Metric Set Filter Topology InnerProductSpace

namespace MLC

/-- Local form of the harmonic minimum principle: if `f` is harmonic on an open
set `s`, `x ∈ s`, and `f` has a minimum on `s` at `x`, then `f` is eventually
equal to `f x` near `x`. -/
theorem HarmonicOnNhd.eventuallyEq_of_isMinOn {f : ℂ → ℝ} {s : Set ℂ}
    (hs : IsOpen s) (hf : HarmonicOnNhd f s) {x : ℂ} (hx : x ∈ s)
    (hmin : ∀ y ∈ s, f x ≤ f y) :
    ∀ᶠ y in 𝓝 x, f y = f x := by
  -- Pick a ball around `x` inside `s`.
  obtain ⟨R, hR, hsub⟩ := Metric.mem_nhds_iff.mp (hs.mem_nhds hx)
  have hballs : ball x R ⊆ s := hsub
  have hfball : HarmonicOnNhd f (ball x R) := fun z hz => hf z (hballs hz)
  -- Represent `f` as the real part of a holomorphic function on the ball.
  obtain ⟨F, hFan, hFeq⟩ := harmonic_is_realOfHolomorphic hfball
  -- `g = exp (-F)`, with `‖g z‖ = exp (- f z)` on the ball.
  set g : ℂ → ℂ := fun z => Complex.exp (-(F z)) with hg
  have hnorm : ∀ z ∈ ball x R, ‖g z‖ = Real.exp (- f z) := by
    intro z hz
    have : (-(F z)).re = - f z := by
      simp [Complex.neg_re, hFeq hz]
    rw [hg]
    simp only [Complex.norm_exp, this]
  -- `g` is differentiable near `x`.
  have hxball : x ∈ ball x R := by simp [hR]
  have hgdiff : ∀ᶠ z in 𝓝 x, DifferentiableAt ℂ g z := by
    refine (isOpen_ball.eventually_mem hxball).mono ?_
    intro z hz
    have hFdiff : DifferentiableAt ℂ F z := (hFan z hz).differentiableAt
    exact (Complex.differentiable_exp _).comp z hFdiff.neg
  -- `‖g‖` has a local maximum at `x`.
  have hloc : IsLocalMax (fun y => ‖g y‖) x := by
    have hmem : ∀ᶠ y in 𝓝 x, y ∈ ball x R := isOpen_ball.eventually_mem hxball
    refine hmem.mono ?_
    intro y hy
    simp only
    rw [hnorm y hy, hnorm x hxball]
    exact Real.exp_le_exp.mpr (by
      have := hmin y (hballs hy)
      linarith)
  -- Maximum modulus principle: `‖g‖` is eventually constant near `x`.
  have hev : ∀ᶠ y in 𝓝 x, ‖g y‖ = ‖g x‖ :=
    norm_eventually_eq_of_isLocalMax hgdiff hloc
  -- Translate back to `f`.
  have hmemball : ∀ᶠ y in 𝓝 x, y ∈ ball x R := isOpen_ball.eventually_mem hxball
  filter_upwards [hev, hmemball] with y hy hyb
  have h1 : Real.exp (- f y) = Real.exp (- f x) := by
    rw [← hnorm y hyb, ← hnorm x hxball]; exact hy
  have : - f y = - f x := by
    have := congrArg Real.log h1
    rwa [Real.log_exp, Real.log_exp] at this
  linarith

/-- **Minimum principle for harmonic functions.** If `f` is harmonic on a
preconnected open set `s` and attains a minimum over `s` at some `x₀ ∈ s`, then
`f` is constant on `s`. -/
theorem HarmonicOnNhd.eqOn_const_of_isMinOn {f : ℂ → ℝ} {s : Set ℂ}
    (hs : IsOpen s) (hpc : IsPreconnected s) (hf : HarmonicOnNhd f s)
    {x₀ : ℂ} (hx₀ : x₀ ∈ s) (hmin : ∀ y ∈ s, f x₀ ≤ f y) :
    Set.EqOn f (fun _ => f x₀) s := by
  -- Continuity of `f` on `s`.
  have hcont : ContinuousOn f s := fun x hx =>
    ((hf x hx).1.continuousAt).continuousWithinAt
  -- Work in the subtype `s`.
  haveI : PreconnectedSpace s := (isPreconnected_iff_preconnectedSpace.mp hpc)
  set A : Set s := {p | f p.1 = f x₀} with hA
  have hA_ne : A.Nonempty := ⟨⟨x₀, hx₀⟩, rfl⟩
  -- `A` is closed: preimage of a point under the continuous restriction.
  have hrestr : Continuous (s.restrict f) := continuousOn_iff_continuous_restrict.mp hcont
  have hclo : IsClosed A := by
    have : A = (s.restrict f) ⁻¹' {f x₀} := by
      ext p; simp [hA, Set.restrict_apply]
    rw [this]
    exact isClosed_singleton.preimage hrestr
  -- `A` is open: local constancy near each of its points.
  have hop : IsOpen A := by
    rw [isOpen_iff_mem_nhds]
    intro p hp
    have hps : p.1 ∈ s := p.2
    have hpx : f p.1 = f x₀ := hp
    -- `f` has a minimum over `s` at `p.1` (same value as at `x₀`).
    have hminp : ∀ y ∈ s, f p.1 ≤ f y := by
      intro y hy; rw [hpx]; exact hmin y hy
    have hev : ∀ᶠ y in 𝓝 p.1, f y = f p.1 :=
      HarmonicOnNhd.eventuallyEq_of_isMinOn hs hf hps hminp
    -- Turn `{y | f y = f x₀}` (a neighbourhood of `p.1`) into a neighbourhood of `p` in `s`.
    have hW : {y | f y = f x₀} ∈ 𝓝 p.1 := by
      filter_upwards [hev] with y hy; rw [hy, hpx]
    have : A = Subtype.val ⁻¹' {y | f y = f x₀} := by
      ext q; simp [hA]
    rw [this]
    exact continuousAt_subtype_val.preimage_mem_nhds hW
  -- Clopen + nonempty + preconnected ⇒ all of `s`.
  have huniv : A = Set.univ := (IsClopen.eq_univ ⟨hclo, hop⟩ hA_ne)
  intro x hx
  have : (⟨x, hx⟩ : s) ∈ A := by rw [huniv]; trivial
  simpa [hA] using this
