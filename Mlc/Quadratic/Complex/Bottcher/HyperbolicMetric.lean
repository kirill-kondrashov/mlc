import Mlc.Quadratic.Complex.Bottcher.DiskAutomorphism
import Mathlib.Analysis.SpecialFunctions.Artanh

/-!
# The Poincaré (hyperbolic) distance on the disk, and the Schottky pipeline

This file opens the **`ℂ \ {0,1}` / Schottky** stage of the λ-lemma foundation.
The end goal is the missing *continuity-in-`z`* step of the λ-lemma
(`LambdaLemma.lean`), which follows from a Schwarz–Pick contraction for holomorphic
maps into `ℂ \ {0,1}` — a statement about the hyperbolic metric of the
thrice-punctured sphere.

## Architecture (Ahlfors route, avoiding the modular λ-function)

1. **Disk model metric** (this file): the Poincaré distance
   `poincareDist a z = 2 · artanh ‖blaschke a z‖` of constant curvature `-1`, and
   the disk Schwarz–Pick contraction `poincareDist (f a) (f z) ≤ poincareDist a z`
   for holomorphic self-maps `f` of the disk. This is the *model target metric*:
   Ahlfors' lemma compares any curvature `≤ -1` metric to it.
2. **Ahlfors' generalized Schwarz lemma** (future): a holomorphic map from the disk
   into a domain carrying a conformal metric of Gaussian curvature `≤ -1` contracts
   that metric relative to the Poincaré metric here.
3. **Ultrahyperbolic metric on `ℂ \ {0,1}`** (future): an explicit conformal density
   `σ(w)|dw|` with curvature `≤ -1`, built without the modular λ-function.
4. **Combine**: Schwarz–Pick for `𝔻 → ℂ \ {0,1}`, then apply to the `crossTrack`
   trajectory of `LambdaLemma.lean` to obtain continuity-in-`z`, discharging axiom A.

## Identified Mathlib gap

Step 2 (Ahlfors' lemma) rests on the **maximum principle for subharmonic
functions**, which Mathlib does not yet have (it has the Laplacian `Δ`, harmonic
functions, and the holomorphic maximum-modulus principle, but no subharmonic
theory). Building that maximum principle is the next infrastructure prerequisite.

## This file (all sorry-free)

* `poincareDist` — the Poincaré distance on the open unit disk.
* `poincareDist_symm`, `poincareDist_self`, `poincareDist_nonneg`,
  `poincareDist_triangle` — the four metric axioms: `poincareDist` is a genuine
  metric of curvature `-1` on the disk.
* `poincareDist_schwarzPick` — **disk Schwarz–Pick** in distance form: holomorphic
  self-maps of the disk are `poincareDist`-nonexpanding.
* `poincareDist_blaschke_isometry` — Blaschke automorphisms are `poincareDist`
  isometries.
* `norm_blaschke_le_add_div` — the pseudo-hyperbolic triangle inequality; `artanh_add`
  — the `artanh` addition formula (ingredients for `poincareDist_triangle`).
-/

namespace MLC.Quadratic

open Complex Metric Set

noncomputable section

/-- The **Poincaré (hyperbolic) distance** on the open unit disk, of constant
curvature `-1`: `poincareDist a z = 2 · artanh ‖blaschke a z‖`, where
`‖blaschke a z‖` is the pseudo-hyperbolic distance. -/
noncomputable def poincareDist (a z : ℂ) : ℝ := 2 * Real.artanh ‖blaschke a z‖

/-- The Poincaré distance is symmetric. -/
lemma poincareDist_symm (a z : ℂ) : poincareDist a z = poincareDist z a := by
  unfold poincareDist; rw [norm_blaschke_symm]

/-- The Poincaré distance from a point to itself is zero. -/
@[simp] lemma poincareDist_self (a : ℂ) : poincareDist a a = 0 := by
  simp [poincareDist]

/-- The Poincaré distance is nonnegative on the disk. -/
lemma poincareDist_nonneg {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    0 ≤ poincareDist a z := by
  have h1 : ‖blaschke a z‖ < 1 := norm_blaschke_lt_one ha hz
  have h2 : Real.artanh 0 ≤ Real.artanh ‖blaschke a z‖ :=
    Real.artanh_le_artanh (by norm_num) h1 (norm_nonneg _)
  rw [Real.artanh_zero] at h2
  unfold poincareDist; linarith

/-- **Disk Schwarz–Pick in distance form.** A holomorphic self-map of the unit disk
does not increase the Poincaré distance. This is the disk (curvature `-1`) model of
the contraction the full λ-lemma pulls back from `ℂ \ {0,1}`. -/
theorem poincareDist_schwarzPick (f : ℂ → ℂ)
    (hd : DifferentiableOn ℂ f (ball 0 1))
    (h_maps : MapsTo f (ball 0 1) (ball 0 1))
    {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    poincareDist (f a) (f z) ≤ poincareDist a z := by
  have hle := norm_blaschke_comp_le f hd h_maps ha hz
  have hy : ‖blaschke a z‖ < 1 := norm_blaschke_lt_one ha hz
  have hx : -1 < ‖blaschke (f a) (f z)‖ :=
    lt_of_lt_of_le (by norm_num) (norm_nonneg _)
  have := Real.artanh_le_artanh hx hy hle
  unfold poincareDist; linarith

/-- **Blaschke automorphisms are Poincaré isometries.** -/
theorem poincareDist_blaschke_isometry {b : ℂ} (hb : ‖b‖ < 1) {a z : ℂ}
    (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    poincareDist (blaschke b a) (blaschke b z) = poincareDist a z := by
  unfold poincareDist; rw [norm_blaschke_comp_eq hb ha hz]

/-- The **pseudo-hyperbolic triangle inequality** (with `0` as the midpoint):
`‖blaschke x y‖ ≤ (‖x‖ + ‖y‖) / (1 + ‖x‖·‖y‖)`.

The proof reduces, via the Blaschke norm identity
`‖1 - conj x·y‖² − ‖y − x‖² = (1−‖x‖²)(1−‖y‖²)`, to the ordinary triangle
inequality `‖y − x‖ ≤ ‖x‖ + ‖y‖`. -/
lemma norm_blaschke_le_add_div {x y : ℂ} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) :
    ‖blaschke x y‖ ≤ (‖x‖ + ‖y‖) / (1 + ‖x‖ * ‖y‖) := by
  have hp0 : (0:ℝ) ≤ ‖x‖ := norm_nonneg x
  have hq0 : (0:ℝ) ≤ ‖y‖ := norm_nonneg y
  have hden : (0:ℝ) < 1 + ‖x‖ * ‖y‖ := by positivity
  have hbden : (0:ℝ) < ‖1 - (starRingEnd ℂ) x * y‖ :=
    norm_pos_iff.2 (blaschke_den_ne_zero hx hy.le)
  -- Norm-squared identity `Dn − N = (1−p²)(1−q²)`.
  have hid : ‖1 - (starRingEnd ℂ) x * y‖ ^ 2 - ‖y - x‖ ^ 2
      = (1 - ‖x‖ ^ 2) * (1 - ‖y‖ ^ 2) := by
    have h := normSq_one_sub_conj_mul_sub_normSq_sub x y
    simpa only [Complex.normSq_eq_norm_sq] using h
  -- Ordinary triangle inequality, squared: `N ≤ (p+q)²`.
  have hN : ‖y - x‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 := by
    have h := norm_sub_le y x
    have : ‖y - x‖ ≤ ‖x‖ + ‖y‖ := by rw [add_comm]; exact h
    nlinarith [norm_nonneg (y - x), this]
  -- Nonnegativity of the two square factors.
  have h1p : (0:ℝ) ≤ 1 - ‖x‖ ^ 2 := by nlinarith
  have h1q : (0:ℝ) ≤ 1 - ‖y‖ ^ 2 := by nlinarith
  -- Compare squares.
  have hsq : ‖blaschke x y‖ ^ 2 ≤ ((‖x‖ + ‖y‖) / (1 + ‖x‖ * ‖y‖)) ^ 2 := by
    rw [blaschke, norm_div, div_pow, div_pow]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg h1p h1q)
      (sub_nonneg.2 hN), hid, hN, hbden.le]
  have hBnn : (0:ℝ) ≤ (‖x‖ + ‖y‖) / (1 + ‖x‖ * ‖y‖) := by positivity
  exact (abs_le_of_sq_le_sq' hsq hBnn).2

/-- **Addition formula for `artanh`** on `[0,1)`:
`artanh a + artanh b = artanh ((a+b)/(1+ab))`. -/
lemma artanh_add {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hb0 : 0 ≤ b) (hb1 : b < 1) :
    Real.artanh a + Real.artanh b = Real.artanh ((a + b) / (1 + a * b)) := by
  have hpab : (0:ℝ) < 1 + a * b := by positivity
  have hT1 : (a + b) / (1 + a * b) < 1 := by rw [div_lt_one hpab]; nlinarith
  have hT0 : 0 ≤ (a + b) / (1 + a * b) := by positivity
  have ha' : (0:ℝ) < 1 - a := by linarith
  have hb' : (0:ℝ) < 1 - b := by linarith
  rw [Real.artanh_eq_half_log ⟨by linarith, by linarith⟩,
      Real.artanh_eq_half_log ⟨by linarith, by linarith⟩,
      Real.artanh_eq_half_log ⟨by linarith, by linarith⟩,
      ← mul_add, ← Real.log_mul (by positivity) (by positivity)]
  congr 2
  have hane : (1 - a) ≠ 0 := ne_of_gt ha'
  have hbne : (1 - b) ≠ 0 := ne_of_gt hb'
  have hpne : (1 + a * b) ≠ 0 := ne_of_gt hpab
  rw [show (1 + (a + b) / (1 + a * b)) = ((1 + a) * (1 + b)) / (1 + a * b) by
        field_simp; ring,
      show (1 - (a + b) / (1 + a * b)) = ((1 - a) * (1 - b)) / (1 + a * b) by
        field_simp; ring]
  field_simp

/-- **Triangle inequality for the Poincaré distance.** Together with symmetry,
nonnegativity and `poincareDist_self`, this makes `poincareDist` a genuine metric
on the open unit disk (the hyperbolic metric of curvature `-1`).

Proved by the isometry reduction: normalise the midpoint `b` to the origin via the
Blaschke automorphism `blaschke b`, then combine `norm_blaschke_le_add_div` with the
`artanh` addition formula. -/
theorem poincareDist_triangle {a b c : ℂ} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1)
    (hc : ‖c‖ < 1) :
    poincareDist a c ≤ poincareDist a b + poincareDist b c := by
  set u := blaschke b a with hu
  set v := blaschke b c with hv
  have hunorm : ‖u‖ < 1 := norm_blaschke_lt_one hb ha
  have hvnorm : ‖v‖ < 1 := norm_blaschke_lt_one hb hc
  rw [← poincareDist_blaschke_isometry hb ha hc,
      ← poincareDist_blaschke_isometry hb ha hb,
      ← poincareDist_blaschke_isometry hb hb hc, blaschke_self b]
  have hu0 : poincareDist u 0 = 2 * Real.artanh ‖u‖ := by
    simp [poincareDist, blaschke_zero_right]
  have h0v : poincareDist 0 v = 2 * Real.artanh ‖v‖ := by
    simp [poincareDist, blaschke]
  have hadd := artanh_add (norm_nonneg u) hunorm (norm_nonneg v) hvnorm
  have hle := norm_blaschke_le_add_div hunorm hvnorm
  have hT1 : (‖u‖ + ‖v‖) / (1 + ‖u‖ * ‖v‖) < 1 := by
    rw [div_lt_one (by positivity)]
    nlinarith [mul_pos (sub_pos.2 hunorm) (sub_pos.2 hvnorm)]
  have hmono := Real.artanh_le_artanh
    (lt_of_lt_of_le (by norm_num) (norm_nonneg (blaschke u v))) hT1 hle
  rw [hu0, h0v]
  simp only [poincareDist]
  linarith [hmono, hadd]

end

end MLC.Quadratic
