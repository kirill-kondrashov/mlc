import Mlc.Quadratic.Complex.Bottcher.LambdaLemma
import Mlc.Quadratic.Complex.Bottcher.UltrahyperbolicPullback

/-!
# Schwarz–Pick contraction of holomorphic-motion trajectories

This file bridges the two halves of the λ-lemma foundation:

* the **abstract** holomorphic-motion machinery of `LambdaLemma.lean` — in particular the
  three-point normalized trajectory `crossTrack z w u t = (f t z - f t u)/(f t w - f t u)`,
  which is holomorphic in time on the unit disk and takes values in the thrice-punctured plane
  `ℂ \ {0,1}` (`crossTrack_mem_compl`, `differentiableOn_crossTrack`);

* the **analytic** Schwarz–Pick contraction of `UltrahyperbolicPullback.lean` — the pointwise
  bound `‖f' z‖ ≤ 2/((1-‖z‖²)·m)` valid for holomorphic immersions `𝔻 → ℂ \ {0,1}` whose image
  keeps the rescaled ultrahyperbolic density above `m > 0` (`deriv_norm_bound_of_density_lower`).

## Main result

* `norm_deriv_crossTrack_le` — applying the derivative bound to the (holomorphic, `ℂ\{0,1}`-valued)
  trajectory `crossTrack z w u`, its time derivative is uniformly controlled by the disk Poincaré
  density: `‖∂ₜ crossTrack z w u t‖ ≤ 2/((1-‖t‖²)·m)` whenever the trajectory stays in a region of
  density `≥ m > 0`.  When the trajectories of a holomorphic motion stay in a fixed compact subset
  `K ⊂ ℂ\{0,1}` (so `m := min_K (√(1/1000)·σ) > 0`), this is a *uniform in `z,w,u`* Lipschitz bound
  in time — the equicontinuity-in-time input for the Mañé–Sad–Sullivan continuity argument.

The immersion hypothesis `∂ₜ crossTrack ≠ 0` is inherited from
`deriv_norm_bound_of_density_lower`; it is the standing `f'≠0` flag of the Ahlfors route (a
trajectory may have isolated time-critical points), to be discharged by the subharmonic
generalization of Ahlfors' lemma.
-/

namespace MLC.Quadratic

open Complex Metric

namespace HolomorphicMotion

variable {E : Set ℂ}

/-- **Schwarz–Pick derivative bound on a normalized trajectory.** For three distinct points
`z, w, u ∈ E`, if the normalized trajectory `crossTrack z w u` (holomorphic in time, valued in
`ℂ \ {0,1}`) stays in a region where the rescaled ultrahyperbolic density is `≥ m > 0` and is a
time-immersion, then its time derivative is bounded by the disk Poincaré density:
`‖∂ₜ crossTrack z w u t‖ ≤ 2/((1-‖t‖²)·m)` for every `‖t‖ < 1`. -/
theorem norm_deriv_crossTrack_le (H : HolomorphicMotion E) {z w u : ℂ}
    (hz : z ∈ E) (hw : w ∈ E) (hu : u ∈ E)
    (hzw : z ≠ w) (hzu : z ≠ u) (hwu : w ≠ u)
    {m : ℝ} (hm0 : 0 < m)
    (hdens : ∀ t ∈ ball (0 : ℂ) 1, m ≤ ultraDensityScaled (H.crossTrack z w u t))
    (himm : ∀ t ∈ ball (0 : ℂ) 1, deriv (H.crossTrack z w u) t ≠ 0)
    {t : ℂ} (ht : ‖t‖ < 1) :
    ‖deriv (H.crossTrack z w u) t‖ ≤ 2 / ((1 - ‖t‖ ^ 2) * m) := by
  have hdiff : DifferentiableOn ℂ (H.crossTrack z w u) (ball (0 : ℂ) 1) :=
    H.differentiableOn_crossTrack hz hw hu hwu
  have hball : ∀ s ∈ ball (0 : ℂ) 1, ball (0 : ℂ) 1 ∈ nhds s := fun s hs =>
    isOpen_ball.mem_nhds hs
  refine deriv_norm_bound_of_density_lower
    (f := H.crossTrack z w u)
    (fun s hs => hdiff.analyticAt (hball s hs)) ?_ ?_ himm hm0 hdens ht
  · intro s hs
    have hmem := H.crossTrack_mem_compl hs hz hw hu hzw hzu hwu
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hmem
    exact hmem.1
  · intro s hs
    have hmem := H.crossTrack_mem_compl hs hz hw hu hzw hzu hwu
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hmem
    exact hmem.2

end HolomorphicMotion

end MLC.Quadratic
