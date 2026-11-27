import Mlc.GridCertificate
import Mathlib.MeasureTheory.Covering.DensityTheorem
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Route Z, the measure step: a porous set has measure zero

A set `E` of the plane is porous at `c` with constant `α` when, at arbitrarily small
scales `r`, the ball `B(c, r)` contains a ball of radius `α r` that misses `E`. At a
Lebesgue density point of `E` the proportion of `E` in small balls tends to `1`, which a
hole of proportional size forbids. So a measurable set that is porous at each of its points
has measure zero.

This is the last step of the route to the area of `∂M` described in `ROADMAP.md`. The
programme of Dudko has to supply the holes: substantial hyperbolic components at all
scales, or the porosity of `J_c` transferred to the parameter plane. Nothing here is a
hypothesis of `MLC.mlc_conjecture`; the porosity of the unresolved set is the explicit
hypothesis of `unresolved_volume_eq_zero_of_porous`.
-/

open MeasureTheory Metric Set Filter Topology

namespace MLC.Research

/-- `E` is `α`-porous at `c`: at arbitrarily small scales `r` there is a ball of radius
`α r` inside `B(c, r)` that misses `E`. -/
def PorousAt (E : Set ℂ) (c : ℂ) (α : ℝ) : Prop :=
  ∀ ε > 0, ∃ r y, 0 < r ∧ r < ε ∧ ball y (α * r) ⊆ ball c r ∧ Disjoint (ball y (α * r)) E

theorem PorousAt.mono {E : Set ℂ} {c : ℂ} {α β : ℝ} (hβα : β ≤ α)
    (h : PorousAt E c α) : PorousAt E c β := by
  intro ε hε
  obtain ⟨r, y, hr, hrε, hsub, hdisj⟩ := h ε hε
  have hball : ball y (β * r) ⊆ ball y (α * r) :=
    ball_subset_ball (mul_le_mul_of_nonneg_right hβα hr.le)
  exact ⟨r, y, hr, hrε, hball.trans hsub, hdisj.mono_left hball⟩

/-- The points of a measurable set `E` where `E` is `α`-porous form a null set. -/
theorem volume_porousLevel_eq_zero {E : Set ℂ} (hE : MeasurableSet E) {α : ℝ} (hα : 0 < α) :
    volume {c | c ∈ E ∧ PorousAt E c α} = 0 := by
  have hae := IsUnifLocDoublingMeasure.ae_tendsto_measure_inter_div
    (volume : Measure ℂ) E (2 / α)
  rw [ae_iff, Measure.restrict_apply' hE] at hae
  refine measure_mono_null ?_ hae
  rintro x ⟨hxE, hpor⟩
  refine ⟨?_, hxE⟩
  intro hprop
  choose r y hr hrε hsub hdisj using fun n : ℕ => hpor (1 / ((n : ℝ) + 1)) (by positivity)
  have hδpos : ∀ n : ℕ, 0 < α * r n / 2 := fun n => by have := hr n; positivity
  have hδlim : Tendsto (fun n : ℕ => α * r n / 2) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall hδpos⟩
    have hr0 : Tendsto r atTop (𝓝 0) := by
      refine squeeze_zero (fun n => (hr n).le) (fun n => (hrε n).le) ?_
      exact tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using (hr0.const_mul α).div_const 2
  have hmem : ∀ᶠ n in atTop, x ∈ closedBall (y n) (2 / α * (α * r n / 2)) := by
    refine Eventually.of_forall fun n => ?_
    have hyx : y n ∈ ball x (r n) := hsub n (mem_ball_self (by have := hr n; positivity))
    have hK : 2 / α * (α * r n / 2) = r n := by field_simp
    rw [hK, mem_closedBall, dist_comm]
    exact (mem_ball.mp hyx).le
  have hlim := hprop (fun n => y n) (fun n => α * r n / 2) hδlim hmem
  have hzero : ∀ n : ℕ,
      volume (E ∩ closedBall (y n) (α * r n / 2)) / volume (closedBall (y n) (α * r n / 2)) = 0 := by
    intro n
    have hsubset : closedBall (y n) (α * r n / 2) ⊆ ball (y n) (α * r n) :=
      closedBall_subset_ball (by have := hr n; nlinarith [mul_pos hα (hr n)])
    have hempty : E ∩ closedBall (y n) (α * r n / 2) = ∅ :=
      Set.eq_empty_of_forall_notMem fun z hz =>
        Set.disjoint_left.mp (hdisj n) (hsubset hz.2) hz.1
    simp [hempty]
  have hconst : Tendsto (fun n : ℕ =>
      volume (E ∩ closedBall (y n) (α * r n / 2)) / volume (closedBall (y n) (α * r n / 2)))
      atTop (𝓝 (0 : ENNReal)) := by
    simp only [hzero]
    exact tendsto_const_nhds
  exact zero_ne_one (tendsto_nhds_unique hconst hlim)

/-- A measurable set that is porous at each of its points, with a constant that may depend
on the point, has measure zero. -/
theorem volume_eq_zero_of_porous {E : Set ℂ} (hE : MeasurableSet E)
    (h : ∀ c ∈ E, ∃ α > 0, PorousAt E c α) : volume E = 0 := by
  have hcover : E ⊆ ⋃ k : ℕ, {c | c ∈ E ∧ PorousAt E c (1 / ((k : ℝ) + 1))} := by
    intro c hc
    obtain ⟨α, hα, hpor⟩ := h c hc
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hα
    exact mem_iUnion.mpr ⟨k, hc, hpor.mono hk.le⟩
  refine measure_mono_null hcover (measure_iUnion_null fun k => ?_)
  exact volume_porousLevel_eq_zero hE (by positivity)

/-- If the unresolved set, that is the boundary of the Mandelbrot set, is porous at each of
its points, it has area zero: the certified bound of the grid can be taken to be `0`. -/
theorem unresolved_volume_eq_zero_of_porous
    (h : ∀ c ∈ MLC.Certified.Unresolved, ∃ α > 0, PorousAt MLC.Certified.Unresolved c α) :
    volume MLC.Certified.Unresolved = 0 :=
  volume_eq_zero_of_porous MLC.Certified.measurableSet_unresolved h

end MLC.Research
