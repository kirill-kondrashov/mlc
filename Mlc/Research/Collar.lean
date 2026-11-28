import Mlc.Research.QuasiInvariance
import Mlc.Research.DivergentNest

/-!
# Collars: a quasi-round annulus bounds the modulus from below

The modulus of the annulus `V ∖ E` is the extremal width of the `C¹` loops in it that separate `E`
from the complement of `V` (`loopFamily`); for a nest this is the modulus of each of its annuli
(`ConnectedNest.loops`), and for a level `f : U → V` of a renormalization tower with filled Julia
set `E = K_f` it is `mod⁺(f)`, the reciprocal of the degeneration `W(f)` of the survey (3.2), (4.1).
`Mlc/Research/QuasiInvariance.lean` proves that this modulus is quasi-invariant under `C¹` embeddings
of bounded dilatation. This module uses it for the basic estimate of the theory of the degeneration:
an annulus that contains a quasi-round collar has a definite modulus.

* **Definition `IsCollar E V Kd r R`**: a `C¹` embedding `ψ` of dilatation at most `Kd`, defined on a
  neighbourhood of the closed disk `B̄(w₀, R)`, such that `E` lies in `ψ(B̄(w₀, r))` and
  `ψ(B̄(w₀, R))` lies in `V`. The round annulus `r < |w − w₀| < R` has modulus `log (R/r) / 2π`.
* **Theorem `IsCollar.ofReal_le_extWidth`** (the collar estimate): the modulus of `V ∖ E` is at
  least `log (R/r) / (2π Kd)`. It is Grötzsch's monotonicity of the modulus together with the
  quasi-invariance: the loops of the round annulus go to loops of `V ∖ E`
  (`extWidth_loopFamily_le_map`), and the circles bound the modulus of the round annulus from below
  (`extWidth_loopFamily_ge_radii`).
* **Theorem `ConnectedNest.divergentModuli_of_collars`**: a nest whose annuli all have collars of
  dilatation at most `K₀` and modulus at least `μ₀ / 2π` has divergent moduli, so it shrinks to its
  point (`DivergentModuli.shrinking`).

A collar is a quasi-conformal chart, in the `C¹` sense, between a round annulus and a part of the
annulus: for a degenerating annulus no such chart exists with a definite modulus, so a collar is
the geometric content of a bound on the degeneration.
-/

namespace MLC.Research

open MeasureTheory ENNReal Set Real Topology Metric

noncomputable section

/-- **A collar of the annulus `V ∖ E`.** There is a `C¹` embedding `ψ` of an open set `Ω ⊇ B̄(w₀, R)`
with dilatation at most `Kd` such that `E ⊆ ψ(B̄(w₀, r))` and `ψ(B̄(w₀, R)) ⊆ V`: the annulus
`V ∖ E` contains the image of the round annulus `r < |w − w₀| ≤ R`, which has modulus
`log (R/r) / 2π`, and the image goes around `E`. -/
def IsCollar (E V : Set ℂ) (Kd r R : ℝ) : Prop :=
  0 < Kd ∧ 0 < r ∧ r < R ∧ ∃ (Ω : Set ℂ) (ψ : ℂ → ℂ) (w₀ : ℂ), QcEmbedding Ω ψ Kd ∧
    Measurable ψ ∧ closedBall w₀ R ⊆ Ω ∧ E ⊆ ψ '' closedBall w₀ r ∧ ψ '' closedBall w₀ R ⊆ V

/-- **The collar estimate.** If the annulus `V ∖ E` has a collar of dilatation `Kd` and modulus
`log (R/r) / 2π`, its modulus is at least `log (R/r) / (2π Kd)`. -/
theorem IsCollar.ofReal_le_extWidth {E V : Set ℂ} {Kd r R : ℝ} (h : IsCollar E V Kd r R) :
    ENNReal.ofReal (Real.log (R / r) / (2 * π) / Kd) ≤
      extWidth volume (loopFamily (V \ E) E V) := by
  obtain ⟨hKd, hr, hrR, Ω, ψ, w₀, hψ, hψm, hΩ, hE, hV⟩ := h
  have hR : 0 < R := hr.trans hrR
  have hmodel := extWidth_loopFamily_ge_radii (A := closedBall w₀ R \ closedBall w₀ r)
    (K := closedBall w₀ r) (O := ball w₀ R) (c := w₀) hr hrR
    (fun z hz => mem_closedBall_iff_norm.1 hz)
    (fun w hw => by rwa [mem_ball_iff_norm, not_lt] at hw)
    (fun s hs t => by
      have hn : ‖circleLoop s t‖ = s := norm_pol (hr.trans hs.1).le _
      refine ⟨?_, ?_⟩
      · rw [mem_closedBall_iff_norm, add_sub_cancel_left, hn]
        exact hs.2
      · rw [mem_closedBall_iff_norm, add_sub_cancel_left, hn, not_le]
        exact hs.1)
  have hqc := extWidth_loopFamily_le_map hψ hKd hψm (A := closedBall w₀ R \ closedBall w₀ r)
    (K := closedBall w₀ r) (O := ball w₀ R) (A' := V \ E) (K' := E) (O' := V) isOpen_ball
    (by rw [closure_ball w₀ hR.ne']; exact isCompact_closedBall _ _)
    (by rw [closure_ball w₀ hR.ne']; exact hΩ) (diff_subset.trans hΩ)
    (Or.inl (closedBall_subset_ball hrR))
    (by
      rintro _ ⟨x, ⟨hx1, hx2⟩, rfl⟩
      refine ⟨hV ⟨x, hx1, rfl⟩, fun hmem => hx2 ?_⟩
      obtain ⟨y, hy, hyx⟩ := hE hmem
      have hyΩ : y ∈ Ω := hΩ (closedBall_subset_closedBall hrR.le hy)
      exact (hψ.injOn hyΩ (hΩ hx1) hyx) ▸ hy)
    hE ((image_mono ball_subset_closedBall).trans hV)
  rw [ENNReal.ofReal_div_of_pos hKd]
  exact ENNReal.div_le_of_le_mul' (hmodel.trans hqc)

/-- **Nests with uniform collars have divergent moduli.** If every annulus `Pⱼ ∖ cl P_{j+1}` of
the nest has a collar of dilatation at most `K₀` and modulus at least `μ₀ / 2π`, the moduli of the
annuli are bounded below by `μ₀ / (2π K₀)`, so they add up to infinity and the pieces shrink to
the point. -/
theorem ConnectedNest.divergentModuli_of_collars {S : Set ℂ} {c : ℂ} (D : ConnectedNest S c)
    {K₀ μ₀ : ℝ} (hK₀ : 0 < K₀) (hμ₀ : 0 < μ₀)
    (h : ∀ j, ∃ Kd r R : ℝ, Kd ≤ K₀ ∧ μ₀ ≤ Real.log (R / r) ∧
      IsCollar (closure (D.piece (j + 1))) (D.piece j) Kd r R) :
    D.DivergentModuli := by
  refine D.divergentModuli_of_uniform
    (w := ENNReal.ofReal (μ₀ / (2 * π) / K₀))
    (ENNReal.ofReal_pos.2 (by positivity)).ne' fun j => ?_
  obtain ⟨Kd, r, R, hKd, hμ, hcol⟩ := h j
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) hcol.ofReal_le_extWidth
  have hKd0 : 0 < Kd := hcol.1
  have hlog : 0 ≤ Real.log (R / r) / (2 * π) := div_nonneg (hμ₀.le.trans hμ) (by positivity)
  calc μ₀ / (2 * π) / K₀ ≤ Real.log (R / r) / (2 * π) / K₀ := by gcongr
    _ ≤ Real.log (R / r) / (2 * π) / Kd := by gcongr
