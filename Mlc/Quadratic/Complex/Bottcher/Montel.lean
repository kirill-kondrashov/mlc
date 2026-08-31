import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Montel equicontinuity for locally bounded holomorphic families

This file proves the **analytic heart of Montel's theorem**: a family of
holomorphic functions that is uniformly bounded on a disc is *uniformly
Lipschitz* (hence equicontinuous) on the concentric half-radius disc, with a
Lipschitz constant that depends only on the bound and the radius — **not** on the
index of the family.

This is a genuine, reusable prerequisite for the normal-families machinery that
the Mañé–Sad–Sullivan / Słodkowski λ-lemma continuity step consumes (the residual
input isolated in `LambdaLemma.lean`). It is proved sorry-free and axiom-clean
from Mathlib's Cauchy first-derivative estimate
(`Complex.norm_deriv_le_of_forall_mem_sphere_norm_le`) and the convex mean-value
inequality (`norm_image_sub_le_of_norm_deriv_le`).

Combined with Arzelà–Ascoli (`Mathlib.Topology.UniformSpace.Ascoli`), the uniform
equicontinuity below upgrades a locally-bounded holomorphic family to a normal
family; that is the classical basic Montel theorem. The *strong* Montel theorem
(families omitting two values are normal) additionally requires the hyperbolic
metric / modular function of `ℂ ∖ {0,1}`, which is not yet in Mathlib and is the
remaining foundational gap toward discharging the parameter-puzzle straddling
axiom.
-/

namespace MLC.Quadratic.Montel

open Complex Metric Set

variable {c : ℂ} {R C : ℝ}

/-- **Cauchy derivative estimate on an interior point of a disc.** If `f` is
holomorphic on `ball c R` and bounded there by `C`, then at any point of the
half-radius disc `ball c (R/2)` the derivative is bounded by `2C/R`. -/
lemma norm_deriv_le_of_ball_bound {f : ℂ → ℂ} (hR : 0 < R)
    (hd : DifferentiableOn ℂ f (ball c R))
    (hb : ∀ z ∈ ball c R, ‖f z‖ ≤ C)
    {z₀ : ℂ} (hz₀ : z₀ ∈ ball c (R / 2)) :
    ‖deriv f z₀‖ ≤ 2 * C / R := by
  have hR2 : (0 : ℝ) < R / 2 := by linarith
  -- The closed half-disc around `z₀` sits inside the open disc `ball c R`.
  have hz₀' : dist z₀ c < R / 2 := mem_ball.mp hz₀
  have hsub_closed : closedBall z₀ (R / 2) ⊆ ball c R := by
    intro w hw
    have hw' : dist w z₀ ≤ R / 2 := mem_closedBall.mp hw
    have : dist w c < R := by
      calc dist w c ≤ dist w z₀ + dist z₀ c := dist_triangle _ _ _
        _ < R / 2 + R / 2 := by linarith
        _ = R := by ring
    exact mem_ball.mpr this
  have hsub_open : ball z₀ (R / 2) ⊆ ball c R :=
    (ball_subset_closedBall).trans hsub_closed
  -- `f` is differentiable on and continuous up to the closure of `ball z₀ (R/2)`.
  have hdcc : DiffContOnCl ℂ f (ball z₀ (R / 2)) := by
    refine ⟨hd.mono hsub_open, ?_⟩
    rw [closure_ball z₀ (ne_of_gt hR2)]
    exact hd.continuousOn.mono hsub_closed
  -- Bound on the boundary sphere.
  have hCsphere : ∀ z ∈ sphere z₀ (R / 2), ‖f z‖ ≤ C := by
    intro z hz
    exact hb z (hsub_closed (sphere_subset_closedBall hz))
  have hkey := norm_deriv_le_of_forall_mem_sphere_norm_le hR2 hdcc hCsphere
  -- `C / (R/2) = 2C/R`.
  calc ‖deriv f z₀‖ ≤ C / (R / 2) := hkey
    _ = 2 * C / R := by field_simp

/-- **Montel equicontinuity (uniform Lipschitz bound).** Let `f i` be a family of
functions, each holomorphic on `ball c R` and uniformly bounded there by `C`
(bound independent of `i`). Then every member is `(2C/R)`-Lipschitz on the
half-radius disc `ball c (R/2)`, with the **same** constant for all `i`. This is
the equicontinuity that drives Montel's normal-families theorem via Arzelà–Ascoli. -/
theorem norm_image_sub_le_of_uniform_ball_bound {ι : Type*} {f : ι → ℂ → ℂ}
    (hR : 0 < R)
    (hd : ∀ i, DifferentiableOn ℂ (f i) (ball c R))
    (hb : ∀ i, ∀ z ∈ ball c R, ‖f i z‖ ≤ C)
    (i : ι) {x y : ℂ} (hx : x ∈ ball c (R / 2)) (hy : y ∈ ball c (R / 2)) :
    ‖f i y - f i x‖ ≤ (2 * C / R) * ‖y - x‖ := by
  have hhalf : ball c (R / 2) ⊆ ball c R :=
    ball_subset_ball (by linarith)
  refine (convex_ball c (R / 2)).norm_image_sub_le_of_norm_deriv_le ?_ ?_ hx hy
  · intro z hz
    exact (hd i).differentiableAt (isOpen_ball.mem_nhds (hhalf hz))
  · intro z hz
    exact norm_deriv_le_of_ball_bound hR (hd i) (hb i) hz

/-- **Montel equicontinuity, `LipschitzOnWith` form.** Under the same hypotheses,
each `f i` is `LipschitzOnWith` the constant `(2C/R).toNNReal` on `ball c (R/2)`,
uniformly in `i`. -/
theorem lipschitzOnWith_of_uniform_ball_bound {ι : Type*} {f : ι → ℂ → ℂ}
    (hR : 0 < R) (hC : 0 ≤ C)
    (hd : ∀ i, DifferentiableOn ℂ (f i) (ball c R))
    (hb : ∀ i, ∀ z ∈ ball c R, ‖f i z‖ ≤ C)
    (i : ι) :
    LipschitzOnWith (Real.toNNReal (2 * C / R)) (f i) (ball c (R / 2)) := by
  have hconst : (0 : ℝ) ≤ 2 * C / R := by positivity
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro x hx y hy
  rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hconst]
  simpa [norm_sub_rev] using
    norm_image_sub_le_of_uniform_ball_bound hR hd hb i hx hy

open Filter Topology

/-- **A pointwise limit of uniformly Lipschitz maps is Lipschitz.** If every `f i`
is `LipschitzOnWith L` on `s` (same constant `L`) and `f i z → g z` pointwise on
`s` along a nontrivial filter, then the limit `g` is `LipschitzOnWith L` on `s`.
The uniform Lipschitz bound of a normal family thus passes to its limits. -/
theorem lipschitzOnWith_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    {f : ι → ℂ → ℂ} {g : ℂ → ℂ} {s : Set ℂ} {L : NNReal}
    (hf : ∀ i, LipschitzOnWith L (f i) s)
    (hg : ∀ z ∈ s, Tendsto (fun i => f i z) l (𝓝 (g z))) :
    LipschitzOnWith L g s := by
  intro x hx y hy
  have h1 : Tendsto (fun i => edist (f i x) (f i y)) l (𝓝 (edist (g x) (g y))) :=
    (hg x hx).edist (hg y hy)
  exact le_of_tendsto h1 (Eventually.of_forall (fun i => hf i hx hy))

/-- **Weierstrass + Montel packaging.** Any locally-uniform limit `g` of a
uniformly-bounded holomorphic family `f i` on `ball c R` is itself holomorphic on
the half-radius disc and inherits the uniform `(2C/R)`-Lipschitz bound. This is
the shape in which basic Montel feeds normal-family limit arguments: the limit is
holomorphic (Weierstrass) with controlled modulus of continuity. -/
theorem differentiableOn_and_lipschitzOnWith_of_tendstoLocallyUniformly
    {ι : Type*} {l : Filter ι} [l.NeBot] {f : ι → ℂ → ℂ} {g : ℂ → ℂ}
    (hR : 0 < R) (hC : 0 ≤ C)
    (hd : ∀ i, DifferentiableOn ℂ (f i) (ball c R))
    (hb : ∀ i, ∀ z ∈ ball c R, ‖f i z‖ ≤ C)
    (hlim : TendstoLocallyUniformlyOn f g l (ball c (R / 2))) :
    DifferentiableOn ℂ g (ball c (R / 2)) ∧
      LipschitzOnWith (Real.toNNReal (2 * C / R)) g (ball c (R / 2)) := by
  have hhalf : ball c (R / 2) ⊆ ball c R := ball_subset_ball (by linarith)
  refine ⟨?_, ?_⟩
  · refine hlim.differentiableOn ?_ isOpen_ball
    exact Eventually.of_forall (fun i => (hd i).mono hhalf)
  · refine lipschitzOnWith_of_tendsto (l := l)
      (fun i => lipschitzOnWith_of_uniform_ball_bound hR hC hd hb i) ?_
    intro z hz
    exact hlim.tendsto_at hz
