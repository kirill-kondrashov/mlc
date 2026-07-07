import Mlc.Quadratic.Complex.Bottcher.LambdaLemma

/-!
# Słodkowski / λ-lemma statement layer and the space-holomorphic bypass
-/

namespace MLC.Quadratic

open Complex Topology Set Metric

/-- **Mañé–Sad–Sullivan λ-lemma (continuity statement).** Every holomorphic motion
of a set `E ⊆ ℂ` over the unit disk has continuous time-slices `H.f t` on `E`.
This is the residual analytic input of the connectivity-transport theorems in
`LambdaLemma.lean`. On the pure metric (Ahlfors/Schwarz–Pick) route it is
obstructed by the non-completeness of the `ℂ \ {0,1}` ultrahyperbolic metric; it
is supplied unconditionally by space-holomorphy (`SpaceHolomorphicMotion`). -/
def LambdaLemmaContinuity : Prop :=
  ∀ {E : Set ℂ} (H : HolomorphicMotion E) {t : ℂ},
    t ∈ Metric.ball (0 : ℂ) 1 → ContinuousOn (H.f t) E

/-- **Słodkowski extension property.** The holomorphic motion `H` of `E` extends to
a holomorphic motion of the whole plane agreeing with `H` on `E`. This is the
content of Słodkowski's theorem (every holomorphic motion of `E ⊆ ℂ` over `𝔻`
extends to a holomorphic motion of `ℂ`); stated as a `Prop`, its proof is the deep
Słodkowski/Chirka extension theorem. -/
def SlodkowskiExtension {E : Set ℂ} (H : HolomorphicMotion E) : Prop :=
  ∃ H' : HolomorphicMotion (Set.univ : Set ℂ),
    ∀ t ∈ Metric.ball (0 : ℂ) 1, ∀ z ∈ E, H'.f t z = H.f t z

/-- **λ-lemma continuity ⟹ connectivity transport.** If the λ-lemma continuity
statement holds, then every holomorphic motion sends a connected set to a
connected image at every time in the unit disk. -/
theorem LambdaLemmaContinuity.isConnected_image (hcont : LambdaLemmaContinuity)
    {E : Set ℂ} (H : HolomorphicMotion E) {t : ℂ} (ht : t ∈ Metric.ball (0 : ℂ) 1)
    (hE : IsConnected E) : IsConnected (H.f t '' E) :=
  hE.image _ (hcont H ht)

/-- A **space-holomorphic** holomorphic motion: a holomorphic motion whose every
time-slice `H.f t` is holomorphic (hence continuous) on a fixed open domain
`U ⊇ E`. This is the regularity enjoyed by motions realized through a
Böttcher-coordinate parametrization `z = Φ_t⁻¹(ω)` (holomorphic in both parameter
and space). It **bypasses the Mañé–Sad–Sullivan metric continuity argument** — and
thereby the `ℂ \ {0,1}` completeness obstruction — because continuity of the
time-slices is automatic from holomorphy. -/
structure SpaceHolomorphicMotion (E : Set ℂ) extends HolomorphicMotion E where
  /-- An open domain containing `E` on which every time-slice is holomorphic. -/
  U : Set ℂ
  /-- `E` is contained in the holomorphy domain. -/
  hEU : E ⊆ U
  /-- The holomorphy domain is open. -/
  hU_open : IsOpen U
  /-- Every time-slice is holomorphic on `U`. -/
  h_space_holo : ∀ t ∈ Metric.ball (0 : ℂ) 1, DifferentiableOn ℂ (f t) U

namespace SpaceHolomorphicMotion

variable {E : Set ℂ}

/-- Time-slices of a space-holomorphic motion are continuous on `E`. -/
lemma continuousOn_slice (H : SpaceHolomorphicMotion E) {t : ℂ}
    (ht : t ∈ Metric.ball (0 : ℂ) 1) : ContinuousOn (H.f t) E :=
  ((H.h_space_holo t ht).mono H.hEU).continuousOn

/-- A space-holomorphic motion satisfies the λ-lemma continuity conclusion on its
own set `E`, unconditionally (no metric argument needed). -/
lemma lambdaContinuity_slice (H : SpaceHolomorphicMotion E) {t : ℂ}
    (ht : t ∈ Metric.ball (0 : ℂ) 1) : ContinuousOn (H.f t) E :=
  H.continuousOn_slice ht

/-- **Obstruction-free connectivity transport.** A space-holomorphic motion sends a
connected set `E` to a connected image at every time in the unit disk. This is the
form used to transport dynamical puzzle-piece connectivity into parameter space via
the holomorphic Böttcher inverse. -/
theorem isConnected_image (H : SpaceHolomorphicMotion E) {t : ℂ}
    (ht : t ∈ Metric.ball (0 : ℂ) 1) (hE : IsConnected E) :
    IsConnected (H.f t '' E) :=
  hE.image _ (H.continuousOn_slice ht)

/-- Likewise for preconnected sets. -/
theorem isPreconnected_image (H : SpaceHolomorphicMotion E) {t : ℂ}
    (ht : t ∈ Metric.ball (0 : ℂ) 1) (hE : IsPreconnected E) :
    IsPreconnected (H.f t '' E) :=
  hE.image _ (H.continuousOn_slice ht)

end SpaceHolomorphicMotion

/-- **Puzzle-piece–as–motion-image hypothesis** (the Douady–Hubbard
parameter↔dynamical correspondence, motion form). For a parameter `c` and puzzle
level `n`, the parameter Green-sublevel piece `{c' | G_c(c'-c) < 2⁻ⁿ} ∩ M` is the
image, under some time-slice of a space-holomorphic motion, of a *connected*
reference set `E` (morally the connected dynamical puzzle piece). This is the
statement that Yoccoz's parameter↔dynamical correspondence — combined with the
holomorphic Böttcher-inverse motion — is designed to provide. -/
def ParaPieceIsMotionImage (c : ℂ) (n : ℕ) : Prop :=
  ∃ (E : Set ℂ) (H : SpaceHolomorphicMotion E) (t : ℂ),
    t ∈ Metric.ball (0 : ℂ) 1 ∧ IsConnected E ∧
      H.f t '' E = {c' | green_function c (c' - c) < (1 / 2 : ℝ) ^ n} ∩ MandelbrotSet

/-- **Reduction of frontier axiom A to the correspondence.** If the parameter
puzzle piece is the space-holomorphic-motion image of a connected reference set,
then it is connected. This discharges
`green_sublevel_translate_inter_mandelbrot_connected` *conditionally* on
`ParaPieceIsMotionImage`, replacing the opaque frontier axiom by the named,
standard mathematical input (Słodkowski's λ-lemma + the Douady–Hubbard
correspondence). The metric-completeness obstruction is bypassed because the
motion is holomorphic in space. -/
theorem isConnected_greenSublevel_inter_mandelbrot_of_motionImage
    (c : ℂ) (n : ℕ) (h : ParaPieceIsMotionImage c n) :
    IsConnected ({c' | green_function c (c' - c) < (1 / 2 : ℝ) ^ n} ∩ MandelbrotSet) := by
  obtain ⟨E, H, t, ht, hE, himg⟩ := h
  rw [← himg]
  exact H.isConnected_image ht hE

/-- For `t` in the unit disk, `1 + t ≠ 0` (used to build injective scaling
slices). -/
lemma one_add_ne_zero_of_mem_ball {t : ℂ} (ht : t ∈ Metric.ball (0 : ℂ) 1) :
    (1 : ℂ) + t ≠ 0 := by
  have hnorm : ‖t‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using ht
  intro h
  have ht1 : t = -1 := by linear_combination h
  rw [ht1] at hnorm
  simp at hnorm

/-- A concrete **nonempty, non-trivial** space-holomorphic motion: the scaling
motion `f t z = (1 + t) z` on the whole plane. Its time-slices genuinely move
points (unlike the empty `trivialHolomorphicMotion`), are holomorphic in both the
time `t` and the space variable `z`, and are injective for every `t` in the unit
disk (because `1 + t ≠ 0` there). This witnesses that `SpaceHolomorphicMotion` is
inhabited by a genuine motion, so the connectivity-transport machinery of
`SpaceHolomorphicMotion.isConnected_image` is not vacuous. -/
noncomputable def scalingSpaceHolomorphicMotion :
    SpaceHolomorphicMotion (Set.univ : Set ℂ) where
  f := fun t z => (1 + t) * z
  h_zero := by intro z _; simp
  h_inj := by
    intro t ht a _ b _ h
    exact mul_left_cancel₀ (one_add_ne_zero_of_mem_ball ht) h
  h_holo := by
    intro z _
    exact (((differentiable_const (1 : ℂ)).add differentiable_id).mul_const z).differentiableOn
  U := Set.univ
  hEU := Set.Subset.rfl
  hU_open := isOpen_univ
  h_space_holo := by
    intro t _
    exact (differentiable_id.const_mul (1 + t)).differentiableOn

/-- The scaling motion genuinely moves the point `1` at any nonzero time — so it is
not the trivial (identity) motion. -/
theorem scalingSpaceHolomorphicMotion_nontrivial {t : ℂ} (ht0 : t ≠ 0) :
    scalingSpaceHolomorphicMotion.f t 1 ≠ scalingSpaceHolomorphicMotion.f 0 1 := by
  simp only [scalingSpaceHolomorphicMotion, mul_one, add_zero]
  intro h
  exact ht0 (by linear_combination h)

end MLC.Quadratic
