import Mlc.Research.DivergentNest

/-!
# The modulus of the round annulus as the extremal width of its loops

The modulus of an annulus is, in this development, the extremal width of the `C¹` loops in it that
separate the inner set from the complement of the outer one (`loopFamily`). `DivergentNest.lean`
proves that the circles bound this width from below by `log (R/r) / 2π`
(`extWidth_loopFamily_ge_radii`). This module proves the upper bound for the round annulus, so that
the width of its loops is exactly the classical modulus.

* `rhoArea_ringMetric_eq`: the metric `1 / |z − c|` on the closed ring `r ≤ |z − c| ≤ R` has area
  exactly `2π log (R/r)`; the ring metric and the annulus metric of `AnnulusModulus.lean` differ only
  on a circle, a null set.
* `ofReal_two_pi_le_minLength_round`: every loop of the ring that goes around the disk has length at
  least `2π` for that metric (the argument of `γ − c` sweeps `(−π, π)`, because the loop meets every
  ray from `c`).
* **Theorem `extWidth_loopFamily_round`**: the extremal width of the `C¹` loops of the ring
  `r < |z − c| ≤ R` that separate the disk of radius `r` from the complement of the disk of radius
  `R` is exactly `log (R/r) / 2π`.
* **Theorem `extWidth_loopFamily_round_open`**: the same for the open ring `r < |z − c| < R`, the
  annulus `target ∖ filled` of a level of a `LevelTower`.

So the dictionary of `LevelTower.lean` is exact on the round annuli: the degeneration of a round
level `K = B̄(c, r)`, `V = B(c, R)` is `2π / log (R/r)`, the reciprocal of the classical modulus
(`LevelTower.width_eq_of_round`).
-/

namespace MLC.Research

open MeasureTheory ENNReal Set Real Metric Topology

noncomputable section

/-- **The metric `1 / |z − c|` on the closed ring has area exactly `2π log (R/r)`.** The ring metric
and the annulus metric of `AnnulusModulus.lean` differ only on a circle, a null set. -/
lemma rhoArea_ringMetric_eq (c : ℂ) {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) :
    rhoArea volume (ringMetric c r R) =
      ENNReal.ofReal (2 * π) * ENNReal.ofReal (Real.log (R / r)) := by
  have hae : (fun z => ringMetric c r R z ^ 2) =ᵐ[volume]
      fun z => annulusMetric r R (z - c) ^ 2 := by
    have hnull : volume (sphere c r) = 0 := Measure.addHaar_sphere_of_ne_zero volume c hr.ne'
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with z hz
    unfold ringMetric annulusMetric
    have hz' : ‖z - c‖ ≠ r := fun h => hz (by simpa [mem_sphere, dist_eq_norm] using h)
    by_cases h : r ≤ ‖z - c‖ ∧ ‖z - c‖ ≤ R
    · have h' : r < ‖z - c‖ ∧ ‖z - c‖ ≤ R := ⟨lt_of_le_of_ne h.1 (Ne.symm hz'), h.2⟩
      simp [h, h']
    · have h' : ¬ (r < ‖z - c‖ ∧ ‖z - c‖ ≤ R) := fun h2 => h ⟨h2.1.le, h2.2⟩
      simp [h, h']
  calc rhoArea volume (ringMetric c r R) = ∫⁻ z, annulusMetric r R (z - c) ^ 2 :=
        lintegral_congr_ae hae
    _ = rhoArea volume (annulusMetric r R) :=
        lintegral_sub_right_eq_self (fun z => annulusMetric r R z ^ 2) c
    _ = _ := rhoArea_annulusMetric hr hrR

/-- Every loop of the round annulus that goes around the disk has length at least `2π` for the
metric `1 / |z − c|`. -/
lemma ofReal_two_pi_le_minLength_round {c : ℂ} {r R : ℝ} (hr : 0 < r) :
    ENNReal.ofReal (2 * π) ≤ minLength (ringMetric c r R)
      (loopFamily (closedBall c R \ closedBall c r) (closedBall c r) (ball c R)) := by
  refine le_minLength fun μ hμ => ?_
  obtain ⟨γ, hγ, hA, hsep, rfl⟩ := hμ
  refine two_pi_le_rhoLength hγ hr (fun t => ?_) (fun t => ?_) fun u hu => ?_
  · have h := (hA t).2
    rw [mem_closedBall_iff_norm, not_le] at h
    exact h.le
  · exact mem_closedBall_iff_norm.1 (hA t).1
  · exact hsep.exists_ray (isBounded_ball) (fun s => (hA s).2) (mem_closedBall_self hr.le) hu

/-- The modulus of the round annulus is at most `log (R/r) / 2π`, as the extremal width of its
separating `C¹` loops. -/
theorem extWidth_loopFamily_round_le {c : ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    extWidth volume (loopFamily (closedBall c R \ closedBall c r) (closedBall c r) (ball c R)) ≤
      ENNReal.ofReal (Real.log (R / r) / (2 * π)) := by
  have hL : 0 < Real.log (R / r) := Real.log_pos ((one_lt_div hr).2 hrR)
  have harea := rhoArea_ringMetric_eq c hr hrR.le
  have hfin : ENNReal.ofReal (2 * π) * ENNReal.ofReal (Real.log (R / r)) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hne : ENNReal.ofReal (2 * π) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (ENNReal.ofReal_pos.2 (by positivity)).ne'
  have h1 := ratio_le_extLength (m := volume)
    (Γ := loopFamily (closedBall c R \ closedBall c r) (closedBall c r) (ball c R))
    (measurable_ringMetric c r R) (harea.trans_lt hfin.lt_top)
  have h2 := le_trans (ENNReal.div_le_div (pow_le_pow_left' (ofReal_two_pi_le_minLength_round
    (c := c) (R := R) hr) 2) harea.le) h1
  unfold extWidth
  refine (ENNReal.inv_le_inv.2 h2).trans (le_of_eq ?_)
  rw [ENNReal.inv_div (Or.inl hfin) (Or.inr hne), ← ENNReal.ofReal_pow (by positivity),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_div_of_pos (by positivity)]
  congr 1
  field_simp

/-- **The modulus of the round annulus.** The extremal width of the `C¹` loops of the closed ring
`r < |z − c| ≤ R` that separate the disk of radius `r` from the complement of the disk of radius `R`
is exactly `log (R/r) / 2π`, the classical modulus. -/
theorem extWidth_loopFamily_round {c : ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    extWidth volume (loopFamily (closedBall c R \ closedBall c r) (closedBall c r) (ball c R)) =
      ENNReal.ofReal (Real.log (R / r) / (2 * π)) :=
  le_antisymm (extWidth_loopFamily_round_le hr hrR)
    (extWidth_loopFamily_ge_radii hr hrR (fun z hz => mem_closedBall_iff_norm.1 hz)
      (fun w hw => by rwa [mem_ball_iff_norm, not_lt] at hw)
      (fun s hs t => by
        have hn : ‖circleLoop s t‖ = s := norm_pol (hr.trans hs.1).le _
        refine ⟨?_, ?_⟩
        · rw [mem_closedBall_iff_norm, add_sub_cancel_left, hn]
          exact hs.2
        · rw [mem_closedBall_iff_norm, add_sub_cancel_left, hn, not_le]
          exact hs.1))

/-- **The modulus of the open round annulus.** The same value for the annulus `r < |z − c| < R` of
the level of a `LevelTower` with `filled = B̄(c, r)` and `target = B(c, R)`: the loops of the open
ring have extremal width `log (R/r) / 2π`. The circles of radius `s < R` lie in the open ring, and
`s` can be taken as close to `R` as wanted. -/
theorem extWidth_loopFamily_round_open {c : ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    extWidth volume (loopFamily (ball c R \ closedBall c r) (closedBall c r) (ball c R)) =
      ENNReal.ofReal (Real.log (R / r) / (2 * π)) := by
  refine le_antisymm ?_ ?_
  · exact (extWidth_mono (loopFamily_mono (diff_subset_diff_left ball_subset_closedBall)
      subset_rfl subset_rfl)).trans (extWidth_loopFamily_round hr hrR).le
  · have hc : ContinuousAt (fun R' : ℝ => Real.log (R' / r) / (2 * π)) R := by
      have hne : R / r ≠ 0 := (div_pos (hr.trans hrR) hr).ne'
      exact ((continuousAt_id.div_const r).log hne).div_const _
    have hcont : Filter.Tendsto (fun R' : ℝ => ENNReal.ofReal (Real.log (R' / r) / (2 * π)))
        (nhdsWithin R (Set.Iio R)) (nhds (ENNReal.ofReal (Real.log (R / r) / (2 * π)))) :=
      ((ENNReal.continuous_ofReal.continuousAt.tendsto.comp hc.tendsto).mono_left
        nhdsWithin_le_nhds)
    refine le_of_tendsto hcont ?_
    filter_upwards [Ioo_mem_nhdsLT hrR] with R' hR'
    refine extWidth_loopFamily_ge_radii hr hR'.1 (fun z hz => mem_closedBall_iff_norm.1 hz)
      (fun w hw => ?_) (fun s hs t => ?_)
    · rw [mem_ball_iff_norm, not_lt] at hw
      exact hR'.2.le.trans hw
    · have hn : ‖circleLoop s t‖ = s := norm_pol (hr.trans hs.1).le _
      refine ⟨?_, ?_⟩
      · rw [mem_ball_iff_norm, add_sub_cancel_left, hn]
        exact hs.2.trans_lt hR'.2
      · rw [mem_closedBall_iff_norm, add_sub_cancel_left, hn, not_le]
        exact hs.1

end

end MLC.Research
