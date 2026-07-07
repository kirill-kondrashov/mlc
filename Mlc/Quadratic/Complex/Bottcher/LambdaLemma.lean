import Mlc.Quadratic.Complex.Axioms
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.Connected.Basic
import Mathlib.Analysis.Complex.Schwarz

/-!
# Foundations for the λ-lemma (Mañé–Sad–Sullivan / Słodkowski)

This file develops genuine, fully-proven foundations for holomorphic motions,
building toward the parameter-puzzle connectivity input
(`green_sublevel_translate_inter_mandelbrot_connected`, "axiom A").

The `HolomorphicMotion E` structure (in `Axioms.lean`) packages a map
`f : ℂ → ℂ → ℂ` with

* `f 0 = id` on `E`,
* `f t` injective on `E` for every `t` in the unit disk,
* `t ↦ f t z` holomorphic on the unit disk for every `z ∈ E`.

The **λ-lemma** upgrades this to: `f` is jointly continuous, each `f t` is a
homeomorphism onto its image (indeed quasiconformal), and the motion extends to
the whole plane. Its analytic heart is that any *three-point normalized*
trajectory `t ↦ (f t z - f t u)/(f t w - f t u)` avoids `0` and `1`, so lands in
the thrice-punctured plane `ℂ \ {0,1}`; the Schwarz–Pick estimate on the
hyperbolic metric of `ℂ \ {0,1}` then forces equicontinuity in `z`.

What is proved here (all sorry-free):

* `HolomorphicMotion.continuousOn_track` — each time-track is continuous.
* `HolomorphicMotion.apply_ne` — injectivity as an inequality.
* `HolomorphicMotion.crossTrack_mem_compl` — the three-point normalized
  trajectory lands in `ℂ \ {0,1}` (the analytic core of the λ-lemma).
* `HolomorphicMotion.differentiableOn_crossTrack` — that trajectory is
  holomorphic in time.
* `HolomorphicMotion.isPreconnected_image` / `isConnected_image` — the
  **connectivity-transport theorem**: given continuity in `z` (the residual
  λ-lemma step), a motion sends a (pre)connected set to a (pre)connected image.
* `HolomorphicMotion.isConnected_trajectory` — each individual trajectory is
  connected.

The remaining step to close axiom A is the continuity-in-`z` estimate
(`ContinuousOn (H.f t) E`), i.e. the Mañé–Sad–Sullivan continuity theorem, which
consumes `crossTrack_mem_compl` together with the hyperbolic metric of
`ℂ \ {0,1}`. It is isolated as the single hypothesis of the transport theorems.
-/

namespace MLC.Quadratic

open Complex Topology Set Metric

variable {E : Set ℂ}

/-- The unit disk in the time variable is connected. -/
lemma isConnected_time_ball : IsConnected (Metric.ball (0 : ℂ) 1) :=
  ⟨⟨0, by simp⟩,
    (convex_ball (0 : ℂ) 1).isPreconnected⟩

namespace HolomorphicMotion

/-- Each time-track `t ↦ f t z` is continuous on the unit disk. -/
lemma continuousOn_track (H : HolomorphicMotion E) {z : ℂ} (hz : z ∈ E) :
    ContinuousOn (fun t => H.f t z) (Metric.ball 0 1) :=
  (H.h_holo z hz).continuousOn

/-- Injectivity of the time-`t` map, phrased as an inequality: distinct points of
`E` have distinct images at every time in the unit disk. -/
lemma apply_ne (H : HolomorphicMotion E) {t : ℂ} (ht : t ∈ Metric.ball 0 1)
    {z w : ℂ} (hz : z ∈ E) (hw : w ∈ E) (hzw : z ≠ w) :
    H.f t z ≠ H.f t w := by
  intro hcontra
  exact hzw (H.h_inj t ht hz hw hcontra)

/-- The three-point normalized trajectory
`t ↦ (f t z - f t u) / (f t w - f t u)`. This is the object whose values drive
the λ-lemma: it avoids `0` and `1` (see `crossTrack_mem_compl`). -/
noncomputable def crossTrack (H : HolomorphicMotion E) (z w u : ℂ) (t : ℂ) : ℂ :=
  (H.f t z - H.f t u) / (H.f t w - H.f t u)

/-- The denominator of `crossTrack` is nonzero throughout the unit disk when
`w ≠ u`. -/
lemma crossTrack_den_ne (H : HolomorphicMotion E) {t : ℂ} (ht : t ∈ Metric.ball 0 1)
    {w u : ℂ} (hw : w ∈ E) (hu : u ∈ E) (hwu : w ≠ u) :
    H.f t w - H.f t u ≠ 0 :=
  sub_ne_zero.2 (H.apply_ne ht hw hu hwu)

/-- **Analytic core of the λ-lemma.** For three distinct points `z, w, u ∈ E`,
the normalized trajectory `crossTrack` lands in the thrice-punctured plane
`ℂ \ {0, 1}` at every time in the unit disk: it is never `0` (since `z ≠ u`) and
never `1` (since `z ≠ w`), and it is well defined (since `w ≠ u`). -/
lemma crossTrack_mem_compl (H : HolomorphicMotion E) {t : ℂ}
    (ht : t ∈ Metric.ball 0 1) {z w u : ℂ}
    (hz : z ∈ E) (hw : w ∈ E) (hu : u ∈ E)
    (hzw : z ≠ w) (hzu : z ≠ u) (hwu : w ≠ u) :
    H.crossTrack z w u t ∈ ({0, 1} : Set ℂ)ᶜ := by
  have hden : H.f t w - H.f t u ≠ 0 := H.crossTrack_den_ne ht hw hu hwu
  have hnum : H.f t z - H.f t u ≠ 0 := sub_ne_zero.2 (H.apply_ne ht hz hu hzu)
  -- not `0`
  have h0 : H.crossTrack z w u t ≠ 0 := by
    simp only [crossTrack]
    exact div_ne_zero hnum hden
  -- not `1`
  have h1 : H.crossTrack z w u t ≠ 1 := by
    simp only [crossTrack]
    intro hcontra
    rw [div_eq_iff hden, one_mul] at hcontra
    -- `f t z - f t u = f t w - f t u` forces `f t z = f t w`, impossible since `z ≠ w`.
    have hzw' : H.f t z = H.f t w := by
      have := congrArg (· + H.f t u) hcontra
      simpa using this
    exact (H.apply_ne ht hz hw hzw) hzw'
  simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  exact ⟨h0, h1⟩

/-- The normalized trajectory `crossTrack` is holomorphic in time on the unit
disk (the analytic regularity underlying the Schwarz–Pick step of the λ-lemma). -/
lemma differentiableOn_crossTrack (H : HolomorphicMotion E) {z w u : ℂ}
    (hz : z ∈ E) (hw : w ∈ E) (hu : u ∈ E) (hwu : w ≠ u) :
    DifferentiableOn ℂ (H.crossTrack z w u) (Metric.ball 0 1) := by
  have hnum : DifferentiableOn ℂ (fun t => H.f t z - H.f t u) (Metric.ball 0 1) :=
    (H.h_holo z hz).sub (H.h_holo u hu)
  have hden : DifferentiableOn ℂ (fun t => H.f t w - H.f t u) (Metric.ball 0 1) :=
    (H.h_holo w hw).sub (H.h_holo u hu)
  exact hnum.div hden (fun t ht => H.crossTrack_den_ne ht hw hu hwu)

/-- **Connectivity transport (preconnected form).** Given the residual λ-lemma
continuity input `ContinuousOn (H.f t) E`, the time-`t` map sends a preconnected
set to a preconnected image. -/
lemma isPreconnected_image (H : HolomorphicMotion E) {t : ℂ}
    (hcont : ContinuousOn (H.f t) E) (hE : IsPreconnected E) :
    IsPreconnected (H.f t '' E) :=
  hE.image _ hcont

/-- **Connectivity transport (connected form).** Given the residual λ-lemma
continuity input `ContinuousOn (H.f t) E`, the time-`t` map sends a connected set
to a connected image. This is the shape used to transport dynamical
puzzle-piece connectivity to the parameter plane. -/
lemma isConnected_image (H : HolomorphicMotion E) {t : ℂ}
    (hcont : ContinuousOn (H.f t) E) (hE : IsConnected E) :
    IsConnected (H.f t '' E) :=
  hE.image _ hcont

/-- **Connectivity transport from space-holomorphy (Böttcher route).** If the time-`t` map
`H.f t` is *holomorphic in the space variable* on a set `S` containing `E` (as happens when the
motion is realized through a Böttcher-coordinate parametrization `z = Φ_t⁻¹(ω)`, holomorphic in
both parameter and space), then the required continuity input is automatic and the image of a
connected set is connected.  This **bypasses the Mañé–Sad–Sullivan metric argument**: the
Schwarz–Pick/completeness machinery is only needed to obtain `ContinuousOn (H.f t) E` for a motion
that is a priori merely injective; when the motion is genuinely holomorphic in space, continuity is
free. -/
lemma isConnected_image_of_differentiableOn (H : HolomorphicMotion E) {t : ℂ} {S : Set ℂ}
    (hsub : E ⊆ S) (hdiff : DifferentiableOn ℂ (H.f t) S) (hE : IsConnected E) :
    IsConnected (H.f t '' E) :=
  hE.image _ ((hdiff.mono hsub).continuousOn)

/-- Space-holomorphy connectivity transport, stated for a bare parametrization map `g` (e.g. the
boundary parametrization `ω ↦ Φ_t⁻¹(ω)` of a moving equipotential) holomorphic on an open domain
`U` containing the connected reference set `S`. -/
lemma isConnected_image_of_analytic {g : ℂ → ℂ} {S U : Set ℂ}
    (hsub : S ⊆ U) (hg : DifferentiableOn ℂ g U) (hS : IsConnected S) :
    IsConnected (g '' S) :=
  hS.image _ ((hg.mono hsub).continuousOn)


lemma isConnected_trajectory (H : HolomorphicMotion E) {z : ℂ} (hz : z ∈ E) :
    IsConnected ((fun t => H.f t z) '' Metric.ball 0 1) :=
  isConnected_time_ball.image _ (H.continuousOn_track hz)

/-- **Schwarz–Pick bound on a motion track.** If the time-track `t ↦ f t z` maps
the unit disk into the closed disk of radius `R` about its start `z`, then it is
`R`-Lipschitz from the origin: `dist (f t z) z ≤ R · ‖t‖`. This is the disk half
of the λ-lemma estimate (the Schwarz lemma applied to a single track); the full
equicontinuity in `z` additionally requires the hyperbolic contraction of the
target `ℂ \ {0,1}` (Schottky), which is the remaining foundation. -/
lemma track_dist_le_of_mapsTo (H : HolomorphicMotion E) {z : ℂ} (hz : z ∈ E)
    {R : ℝ}
    (hmaps : MapsTo (fun t => H.f t z) (Metric.ball 0 1) (Metric.closedBall z R))
    {t : ℂ} (ht : t ∈ Metric.ball 0 1) :
    dist (H.f t z) z ≤ R * ‖t‖ := by
  have hz0 : H.f 0 z = z := H.h_zero z hz
  have hd : DifferentiableOn ℂ (fun s => H.f s z) (Metric.ball 0 1) := H.h_holo z hz
  have hmaps' : MapsTo (fun s => H.f s z) (Metric.ball (0 : ℂ) 1)
      (Metric.closedBall ((fun s => H.f s z) 0) R) := by
    simpa [hz0] using hmaps
  have hkey := dist_le_div_mul_dist_of_mapsTo_ball hd hmaps' ht
  simp only [hz0] at hkey
  simpa [dist_zero_right] using hkey

end HolomorphicMotion

end MLC.Quadratic
