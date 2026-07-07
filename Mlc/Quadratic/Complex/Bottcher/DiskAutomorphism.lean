import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Disk automorphisms (Blaschke factors) for the λ-lemma foundation

Toward the λ-lemma foundation (`LambdaLemma.lean`) for parameter-puzzle
connectivity, this file builds the disk hyperbolic layer that Mathlib lacks: the
**Blaschke automorphisms** `blaschke a z = (z - a)/(1 - conj a · z)` of the unit
disk — the Möbius group of the disk, the substrate on which the invariant
(pseudo-hyperbolic) Schwarz–Pick lemma is built.

Mathlib provides the *Euclidean* disk Schwarz lemma
(`Complex.dist_le_dist_of_mapsTo_ball`) but neither the Blaschke automorphisms nor
their Möbius-invariant Schwarz–Pick form; the latter is the correct disk-side input
for constructing the hyperbolic metric that a full λ-lemma proof pulls back from
`ℂ \ {0,1}`.

Main results (all sorry-free):

* `blaschke_den_ne_zero`, `blaschke_self`, `blaschke_zero_right`, `blaschke_neg_zero`
  — basic algebra.
* `normSq_one_sub_conj_mul_sub_normSq_sub` — the pivotal identity
  `‖1 - conj a·z‖² − ‖z − a‖² = (1 − ‖a‖²)(1 − ‖z‖²)`.
* `norm_blaschke_lt_one` — `blaschke a` maps the open disk into itself.
* `differentiableAt_blaschke` — `blaschke a` is holomorphic off the pole.
* `blaschke_neg_blaschke` — `blaschke (-a)` is the inverse automorphism: it undoes
  `blaschke a` on the open disk. This exhibits `blaschke a` as a disk *automorphism*
  and is the composition backbone for the invariant Schwarz–Pick lemma.
* `norm_blaschke_comp_le` — the **invariant (pseudo-hyperbolic) Schwarz–Pick lemma**:
  a holomorphic self-map `f` of the disk contracts `‖blaschke a z‖`,
  i.e. `‖blaschke (f a) (f z)‖ ≤ ‖blaschke a z‖`. This is the disk-side contraction
  the λ-lemma continuity step ultimately pulls back from `ℂ \ {0,1}`.
* `norm_blaschke_symm` — symmetry `‖blaschke a z‖ = ‖blaschke z a‖`.
* `norm_blaschke_comp_eq` — **Möbius-invariance**: a Blaschke automorphism preserves
  the pseudo-hyperbolic metric, `‖blaschke (blaschke b a) (blaschke b z)‖ = ‖blaschke a z‖`.
-/

namespace MLC.Quadratic

open Complex

noncomputable section

/-- The Blaschke automorphism of the unit disk with zero at `a`:
`blaschke a z = (z - a) / (1 - conj a · z)`. -/
noncomputable def blaschke (a z : ℂ) : ℂ :=
  (z - a) / (1 - (starRingEnd ℂ) a * z)

/-- For `‖a‖ < 1` and `‖z‖ ≤ 1` the Blaschke denominator is nonzero. -/
lemma blaschke_den_ne_zero {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) :
    1 - (starRingEnd ℂ) a * z ≠ 0 := by
  have hlt : ‖(starRingEnd ℂ) a * z‖ < 1 := by
    rw [norm_mul, RCLike.norm_conj]
    calc ‖a‖ * ‖z‖ ≤ ‖a‖ * 1 := by
            apply mul_le_mul_of_nonneg_left hz (norm_nonneg a)
      _ = ‖a‖ := mul_one _
      _ < 1 := ha
  intro h
  have heq : (starRingEnd ℂ) a * z = 1 := (sub_eq_zero.1 h).symm
  rw [heq] at hlt
  simp at hlt

/-- `blaschke a a = 0`. -/
@[simp] lemma blaschke_self (a : ℂ) : blaschke a a = 0 := by
  simp [blaschke]

/-- The pivotal identity behind disk-invariance:
`‖1 - conj a·z‖² − ‖z − a‖² = (1 − ‖a‖²)(1 − ‖z‖²)`, written with `normSq`. -/
lemma normSq_one_sub_conj_mul_sub_normSq_sub (a z : ℂ) :
    normSq (1 - (starRingEnd ℂ) a * z) - normSq (z - a)
      = (1 - normSq a) * (1 - normSq z) := by
  simp only [normSq_apply, sub_re, sub_im, mul_re, mul_im, conj_re, conj_im,
    one_re, one_im]
  ring

/-- `blaschke a 0 = -a`. -/
@[simp] lemma blaschke_zero_right (a : ℂ) : blaschke a 0 = -a := by
  simp [blaschke]

/-- `blaschke (-a) 0 = a` (the inverse automorphism sends `0` back to `a`). -/
@[simp] lemma blaschke_neg_zero (a : ℂ) : blaschke (-a) 0 = a := by
  simp [blaschke]

/-- **Disk invariance.** `blaschke a` maps the open unit disk into itself. -/
lemma norm_blaschke_lt_one {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    ‖blaschke a z‖ < 1 := by
  have hden : (1 - (starRingEnd ℂ) a * z) ≠ 0 := blaschke_den_ne_zero ha hz.le
  have hdenpos : 0 < ‖1 - (starRingEnd ℂ) a * z‖ := norm_pos_iff.2 hden
  rw [blaschke, norm_div, div_lt_one hdenpos]
  -- Reduce to `normSq (z - a) < normSq (1 - conj a · z)`.
  have hna : normSq a < 1 := by
    rw [normSq_eq_norm_sq]; nlinarith [norm_nonneg a, ha]
  have hnz : normSq z < 1 := by
    rw [normSq_eq_norm_sq]; nlinarith [norm_nonneg z, hz]
  have hpos : 0 < (1 - normSq a) * (1 - normSq z) := by
    apply mul_pos <;> linarith
  have key := normSq_one_sub_conj_mul_sub_normSq_sub a z
  have hlt2 : normSq (z - a) < normSq (1 - (starRingEnd ℂ) a * z) := by
    linarith [key, hpos]
  -- Convert `normSq` inequality to the norm inequality.
  rw [normSq_eq_norm_sq, normSq_eq_norm_sq] at hlt2
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) hlt2

/-- **Holomorphy.** `blaschke a` is complex-differentiable at every point off its
pole. -/
lemma differentiableAt_blaschke (a : ℂ) {z : ℂ}
    (hden : 1 - (starRingEnd ℂ) a * z ≠ 0) :
    DifferentiableAt ℂ (blaschke a) z := by
  unfold blaschke
  apply DifferentiableAt.div
  · exact differentiableAt_id.sub_const a
  · exact (differentiableAt_const 1).sub
      ((differentiableAt_const ((starRingEnd ℂ) a)).mul differentiableAt_id)
  · exact hden

/-- `1 - conj a · a ≠ 0` when `‖a‖ < 1` (equals `1 - ‖a‖²`). -/
lemma one_sub_conj_mul_self_ne_zero {a : ℂ} (ha : ‖a‖ < 1) :
    1 - (starRingEnd ℂ) a * a ≠ 0 := by
  rw [mul_comm, Complex.mul_conj]
  have h1 : normSq a < 1 := by rw [normSq_eq_norm_sq]; nlinarith [norm_nonneg a, ha]
  intro h
  rw [sub_eq_zero] at h
  have : (normSq a : ℝ) = 1 := by exact_mod_cast h.symm
  linarith

/-- **Inverse identity.** `blaschke (-a)` is the inverse automorphism of
`blaschke a`: it undoes it on the open disk. -/
lemma blaschke_neg_blaschke {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    blaschke (-a) (blaschke a z) = z := by
  have hden : (1 - (starRingEnd ℂ) a * z) ≠ 0 := blaschke_den_ne_zero ha hz.le
  set w := blaschke a z with hw
  have hwnorm : ‖w‖ < 1 := norm_blaschke_lt_one ha hz
  have hden2' : 1 + (starRingEnd ℂ) a * w ≠ 0 := by
    have h := blaschke_den_ne_zero (a := -a) (z := w) (by simpa using ha) hwnorm.le
    simpa [map_neg] using h
  have key : blaschke (-a) w = (w + a) / (1 + (starRingEnd ℂ) a * w) := by
    unfold blaschke
    rw [map_neg]
    congr 1 <;> ring
  rw [key, div_eq_iff hden2', hw, blaschke]
  have hden'' : 1 - z * (starRingEnd ℂ) a ≠ 0 := by rw [mul_comm]; exact hden
  field_simp
  ring

open Metric Set in
/-- `blaschke b` maps the open unit disk into itself (as a `MapsTo`). -/
lemma mapsTo_blaschke {b : ℂ} (hb : ‖b‖ < 1) :
    MapsTo (blaschke b) (ball 0 1) (ball 0 1) := by
  intro w hw
  exact mem_ball_zero_iff.2 (norm_blaschke_lt_one hb (mem_ball_zero_iff.1 hw))

open Metric Set in
/-- `blaschke b` is holomorphic on the open unit disk. -/
lemma differentiableOn_blaschke {b : ℂ} (hb : ‖b‖ < 1) :
    DifferentiableOn ℂ (blaschke b) (ball 0 1) := by
  intro w hw
  exact (differentiableAt_blaschke b
    (blaschke_den_ne_zero hb (mem_ball_zero_iff.1 hw).le)).differentiableWithinAt

/-- **Symmetry of the pseudo-hyperbolic metric.** `‖blaschke a z‖ = ‖blaschke z a‖`. -/
lemma norm_blaschke_symm (a z : ℂ) : ‖blaschke a z‖ = ‖blaschke z a‖ := by
  rw [blaschke, blaschke, norm_div, norm_div, norm_sub_rev z a]
  congr 1
  rw [← RCLike.norm_conj (1 - (starRingEnd ℂ) z * a)]
  congr 1
  simp only [map_sub, map_one, map_mul, Complex.conj_conj]
  ring

open Metric Set in
/-- **Invariant (pseudo-hyperbolic) Schwarz–Pick lemma.** If `f` is holomorphic on
the open unit disk and maps it into itself, then it contracts the pseudo-hyperbolic
distance `‖blaschke a z‖`:
`‖blaschke (f a) (f z)‖ ≤ ‖blaschke a z‖` for all `a, z` in the disk.

Proved by conjugating `f` to fix the origin: `g = blaschke (f a) ∘ f ∘ blaschke (-a)`
maps the disk into itself with `g 0 = 0`, so Mathlib's origin-centred Schwarz lemma
gives `‖g w‖ ≤ ‖w‖`; evaluate at `w = blaschke a z` and use the inverse identity. -/
theorem norm_blaschke_comp_le (f : ℂ → ℂ)
    (hd : DifferentiableOn ℂ f (ball 0 1))
    (h_maps : MapsTo f (ball 0 1) (ball 0 1))
    {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    ‖blaschke (f a) (f z)‖ ≤ ‖blaschke a z‖ := by
  have hna : ‖-a‖ < 1 := by simpa using ha
  set g : ℂ → ℂ := fun w => blaschke (f a) (f (blaschke (-a) w)) with hg_def
  have hfa : ‖f a‖ < 1 := mem_ball_zero_iff.1 (h_maps (mem_ball_zero_iff.2 ha))
  -- Differentiability of the conjugated map on the disk.
  have hg : DifferentiableOn ℂ g (ball 0 1) := by
    intro w hw
    have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.1 hw
    have hbw : ‖blaschke (-a) w‖ < 1 := norm_blaschke_lt_one hna hw1
    have hffw : ‖f (blaschke (-a) w)‖ < 1 :=
      mem_ball_zero_iff.1 (h_maps (mem_ball_zero_iff.2 hbw))
    have hb1 : DifferentiableAt ℂ (blaschke (-a)) w :=
      differentiableAt_blaschke (-a) (blaschke_den_ne_zero hna hw1.le)
    have hf : DifferentiableAt ℂ f (blaschke (-a) w) :=
      (hd _ (mem_ball_zero_iff.2 hbw)).differentiableAt
        (isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hbw))
    have hb2 : DifferentiableAt ℂ (blaschke (f a)) (f (blaschke (-a) w)) :=
      differentiableAt_blaschke (f a) (blaschke_den_ne_zero hfa hffw.le)
    exact (hb2.comp w (hf.comp w hb1)).differentiableWithinAt
  -- The conjugated map sends the disk into its closure.
  have hmap : MapsTo g (ball 0 1) (closedBall 0 1) := by
    intro w hw
    have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.1 hw
    have hbw : ‖blaschke (-a) w‖ < 1 := norm_blaschke_lt_one hna hw1
    have hffw : ‖f (blaschke (-a) w)‖ < 1 :=
      mem_ball_zero_iff.1 (h_maps (mem_ball_zero_iff.2 hbw))
    exact mem_closedBall_zero_iff.2 (norm_blaschke_lt_one hfa hffw).le
  -- `g` fixes the origin.
  have hg0 : g 0 = 0 := by
    simp only [hg_def, blaschke_neg_zero]
    exact blaschke_self (f a)
  have hmain := norm_le_norm_of_mapsTo_ball hg hmap hg0 (z := blaschke a z)
    (norm_blaschke_lt_one ha hz)
  have hgz : g (blaschke a z) = blaschke (f a) (f z) := by
    simp only [hg_def, blaschke_neg_blaschke ha hz]
  rwa [hgz] at hmain

open Metric Set in
/-- **Möbius-invariance of the pseudo-hyperbolic metric.** A Blaschke automorphism
preserves `‖blaschke a z‖`:
`‖blaschke (blaschke b a) (blaschke b z)‖ = ‖blaschke a z‖`.

Follows from the invariant Schwarz–Pick lemma applied to `blaschke b` and to its
inverse `blaschke (-b)`. -/
theorem norm_blaschke_comp_eq {b : ℂ} (hb : ‖b‖ < 1) {a z : ℂ}
    (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    ‖blaschke (blaschke b a) (blaschke b z)‖ = ‖blaschke a z‖ := by
  have hnb : ‖-b‖ < 1 := by simpa using hb
  have hle := norm_blaschke_comp_le (blaschke b) (differentiableOn_blaschke hb)
    (mapsTo_blaschke hb) ha hz
  have hba : ‖blaschke b a‖ < 1 := norm_blaschke_lt_one hb ha
  have hbz : ‖blaschke b z‖ < 1 := norm_blaschke_lt_one hb hz
  have hge := norm_blaschke_comp_le (blaschke (-b)) (differentiableOn_blaschke hnb)
    (mapsTo_blaschke hnb) hba hbz
  rw [blaschke_neg_blaschke hb ha, blaschke_neg_blaschke hb hz] at hge
  exact le_antisymm hle hge

end

end MLC.Quadratic