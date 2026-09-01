import Mlc.Quadratic.Complex.Bottcher.SubharmonicMaxPrinciple
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# The Ahlfors ultrahyperbolic metric on `ℂ \ {0,1}`

This file builds **step 3** of the Schottky route toward discharging axiom A
(see `HyperbolicMetric.lean` for the architecture and `AhlforsSchwarz.lean` for the
generalized Schwarz lemma that consumes this metric): an explicit conformal density on the
twice-punctured plane `ℂ \ {0,1}` whose Gaussian curvature is bounded above by a negative
constant, built **without** the modular `λ`-function.

## The density

Following Ahlfors, the density is a product of two single-puncture factors, one at `0` and
one at `1`.  In terms of `t = ‖w‖` the single-puncture log-factor is
`ahlforsLogPiece t = ½ log(1 + t^{1/3}) − ⅚ log t`, and

`ultraLogDensity w = ahlforsLogPieceSq ‖w‖² + ahlforsLogPieceSq ‖w-1‖²`,
`ultraDensity   w = exp (ultraLogDensity w)`,

where `ahlforsLogPieceSq s = ½ log(1 + s^{1/6}) − 5/12 log s` is the same factor written as a
function of `s = t²` (so that `ahlforsLogPieceSq ‖w‖² = ahlforsLogPiece ‖w‖`).  Working in the
`s = ‖w‖²` variable lets the radial Laplacian formula `laplacian_comp_normSq` apply directly.
Defining the density as `exp` of the log makes positivity immediate.

## Contents (this increment)

* `ahlforsLogPieceSq`, `ultraLogDensity`, `ultraDensity` — the definitions.
* `ultraDensity_pos` — the density is everywhere positive.
* `contDiffAt_ahlforsLogPieceSq` — the single-puncture log-factor is `C^∞` for `s > 0`.
* `contDiffAt_ultraLogDensity` — `ultraLogDensity` is `C^∞` on `ℂ \ {0,1}`.

The curvature inequality `Δ (ultraLogDensity) ≥ c · ultraDensity²` (curvature `≤ -c < 0`) is
the substantial analytic content still to come.
-/

namespace MLC.Quadratic

open Complex Set
open scoped Laplacian

noncomputable section

/-- The single-puncture Ahlfors log-factor, written as a function of `s = ‖w‖²`:
`ahlforsLogPieceSq s = ½ log(1 + s^{1/6}) − 5/12 log s`. -/
noncomputable def ahlforsLogPieceSq (s : ℝ) : ℝ :=
  (1 / 2) * Real.log (1 + s ^ ((1 : ℝ) / 6)) - (5 / 12) * Real.log s

/-- The logarithm of the Ahlfors ultrahyperbolic density on `ℂ \ {0,1}`: a sum of two
single-puncture factors, at `0` and at `1`. -/
noncomputable def ultraLogDensity (w : ℂ) : ℝ :=
  ahlforsLogPieceSq (‖w‖ ^ 2) + ahlforsLogPieceSq (‖w - 1‖ ^ 2)

/-- The Ahlfors ultrahyperbolic density on `ℂ \ {0,1}`, defined as `exp` of its logarithm so
that it is manifestly positive. -/
noncomputable def ultraDensity (w : ℂ) : ℝ := Real.exp (ultraLogDensity w)

/-- The Ahlfors density is everywhere positive. -/
theorem ultraDensity_pos (w : ℂ) : 0 < ultraDensity w := Real.exp_pos _

/-- The single-puncture log-factor is `C^∞` away from the puncture (`s > 0`). -/
theorem contDiffAt_ahlforsLogPieceSq {s : ℝ} (hs : 0 < s) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n ahlforsLogPieceSq s := by
  have hs' : s ≠ 0 := ne_of_gt hs
  have hpow : ContDiffAt ℝ n (fun s : ℝ => s ^ ((1 : ℝ) / 6)) s :=
    Real.contDiffAt_rpow_const_of_ne hs'
  have hpow_pos : (0 : ℝ) < s ^ ((1 : ℝ) / 6) := Real.rpow_pos_of_pos hs _
  have hlog1 : ContDiffAt ℝ n (fun s : ℝ => Real.log (1 + s ^ ((1 : ℝ) / 6))) s := by
    refine Real.contDiffAt_log.mpr (by positivity) |>.comp s ?_
    exact contDiffAt_const.add hpow
  have hlog2 : ContDiffAt ℝ n (fun s : ℝ => Real.log s) s := Real.contDiffAt_log.mpr hs'
  exact (contDiffAt_const.mul hlog1).sub (contDiffAt_const.mul hlog2)

/-- `ultraLogDensity` is `C^∞` on `ℂ \ {0,1}`. -/
theorem contDiffAt_ultraLogDensity {w : ℂ} (h0 : w ≠ 0) (h1 : w ≠ 1) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n ultraLogDensity w := by
  have hw0 : (0 : ℝ) < ‖w‖ ^ 2 := by positivity
  have hw1 : (0 : ℝ) < ‖w - 1‖ ^ 2 := by
    have : w - 1 ≠ 0 := sub_ne_zero.mpr h1
    positivity
  have hs0 : ContDiffAt ℝ n (fun w : ℂ => ‖w‖ ^ 2) w := (contDiff_norm_sq ℝ).contDiffAt
  have hs1 : ContDiffAt ℝ n (fun w : ℂ => ‖w - 1‖ ^ 2) w :=
    ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)).contDiffAt
  exact ((contDiffAt_ahlforsLogPieceSq hw0).comp w hs0).add
    ((contDiffAt_ahlforsLogPieceSq hw1).comp w hs1)

open InnerProductSpace in
/-- **Harmonicity of `log ‖·‖²`.** Away from the origin, `Δ (log ‖w‖²) = 0`.  This is the
real part of `2 log w` and is the harmonic contribution to the Ahlfors log-density: it lets
us discard the `-5/12 log s` term when computing the curvature. -/
theorem laplacian_log_normSq {w : ℂ} (hw : w ≠ 0) :
    Δ (fun z : ℂ => Real.log (‖z‖ ^ 2)) w = 0 := by
  have hs : (0 : ℝ) < ‖w‖ ^ 2 := by positivity
  have hs' : ‖w‖ ^ 2 ≠ 0 := ne_of_gt hs
  have hFC2 : ContDiffAt ℝ 2 Real.log (‖w‖ ^ 2) := Real.contDiffAt_log.mpr hs'
  rw [laplacian_comp_normSq hFC2]
  have hd1 : deriv Real.log (‖w‖ ^ 2) = (‖w‖ ^ 2)⁻¹ := Real.deriv_log _
  have hd2 : iteratedDeriv 2 Real.log (‖w‖ ^ 2) = -(((‖w‖ ^ 2)) ^ 2)⁻¹ := by
    rw [iteratedDeriv_succ, iteratedDeriv_one, Real.deriv_log']
    exact (hasDerivAt_inv hs').deriv
  rw [hd1, hd2]
  field_simp
  ring

/-- First derivative of the single-puncture log-factor, for `s > 0`. -/
noncomputable def pieceD1 (s : ℝ) : ℝ :=
  (1 / 12) * s ^ (-(5 : ℝ) / 6) / (1 + s ^ ((1 : ℝ) / 6)) - 5 / 12 * s⁻¹

/-- Second derivative of the single-puncture log-factor, for `s > 0`
(the raw output of differentiating `pieceD1`). -/
noncomputable def pieceD2 (s : ℝ) : ℝ :=
  ((1 / 12) * (-(5 : ℝ) / 6 * s ^ (-(5 : ℝ) / 6 - 1)) * (1 + s ^ ((1 : ℝ) / 6)) -
      (1 / 12) * s ^ (-(5 : ℝ) / 6) * (1 / 6 * s ^ ((1 : ℝ) / 6 - 1))) /
      (1 + s ^ ((1 : ℝ) / 6)) ^ 2 -
    5 / 12 * -((s ^ 2)⁻¹)

/-- `pieceD1` is the derivative of `ahlforsLogPieceSq` at `s > 0`. -/
theorem hasDerivAt_ahlforsLogPieceSq {s : ℝ} (hs : 0 < s) :
    HasDerivAt ahlforsLogPieceSq (pieceD1 s) s := by
  have hs' : s ≠ 0 := ne_of_gt hs
  have hden_pos : (0 : ℝ) < 1 + s ^ ((1 : ℝ) / 6) := by positivity
  have hb : HasDerivAt (fun x : ℝ => x ^ ((1 : ℝ) / 6)) (1 / 6 * s ^ ((1 : ℝ) / 6 - 1)) s :=
    Real.hasDerivAt_rpow_const (Or.inl hs')
  have hlog1 : HasDerivAt (fun x : ℝ => Real.log (1 + x ^ ((1 : ℝ) / 6)))
      (1 / 6 * s ^ ((1 : ℝ) / 6 - 1) / (1 + s ^ ((1 : ℝ) / 6))) s :=
    (hb.const_add (1 : ℝ)).log (ne_of_gt hden_pos)
  have hlog2 : HasDerivAt Real.log s⁻¹ s := Real.hasDerivAt_log hs'
  have hcomp : HasDerivAt ahlforsLogPieceSq
      (1 / 2 * (1 / 6 * s ^ ((1 : ℝ) / 6 - 1) / (1 + s ^ ((1 : ℝ) / 6))) - 5 / 12 * s⁻¹) s :=
    (hlog1.const_mul (1 / 2)).sub (hlog2.const_mul (5 / 12))
  have hval : 1 / 2 * (1 / 6 * s ^ ((1 : ℝ) / 6 - 1) / (1 + s ^ ((1 : ℝ) / 6))) - 5 / 12 * s⁻¹
      = pieceD1 s := by
    rw [pieceD1, show ((1 : ℝ) / 6 - 1) = -(5 : ℝ) / 6 by norm_num]; ring
  rwa [hval] at hcomp

/-- `pieceD2` is the derivative of `pieceD1` at `s > 0`. -/
theorem hasDerivAt_pieceD1 {s : ℝ} (hs : 0 < s) :
    HasDerivAt pieceD1 (pieceD2 s) s := by
  have hs' : s ≠ 0 := ne_of_gt hs
  have hden_pos : (0 : ℝ) < 1 + s ^ ((1 : ℝ) / 6) := by positivity
  have ha : HasDerivAt (fun x : ℝ => x ^ (-(5 : ℝ) / 6))
      (-(5 : ℝ) / 6 * s ^ (-(5 : ℝ) / 6 - 1)) s := Real.hasDerivAt_rpow_const (Or.inl hs')
  have hnum : HasDerivAt (fun x : ℝ => 1 / 12 * x ^ (-(5 : ℝ) / 6))
      (1 / 12 * (-(5 : ℝ) / 6 * s ^ (-(5 : ℝ) / 6 - 1))) s := ha.const_mul (1 / 12)
  have hb : HasDerivAt (fun x : ℝ => x ^ ((1 : ℝ) / 6)) (1 / 6 * s ^ ((1 : ℝ) / 6 - 1)) s :=
    Real.hasDerivAt_rpow_const (Or.inl hs')
  have hden : HasDerivAt (fun x : ℝ => 1 + x ^ ((1 : ℝ) / 6)) (1 / 6 * s ^ ((1 : ℝ) / 6 - 1)) s :=
    hb.const_add (1 : ℝ)
  have hq := hnum.div hden (ne_of_gt hden_pos)
  have hinv : HasDerivAt (fun x : ℝ => 5 / 12 * x⁻¹) (5 / 12 * -((s ^ 2)⁻¹)) s :=
    (hasDerivAt_inv hs').const_mul (5 / 12)
  have hfinal := hq.sub hinv
  exact hfinal

/-- The algebraic core of the single-puncture Laplacian: with `s = q^6`, the radial
combination `4 F' + 4 s F''` collapses (the harmonic `log s` part cancels) to
`q / (18 s (1+q)²)`. -/
theorem four_pieceD1_add_pieceD2_algebra {s : ℝ} (hs : 0 < s) :
    4 * pieceD1 s + 4 * s * pieceD2 s
      = s ^ ((1 : ℝ) / 6) / (18 * s * (1 + s ^ ((1 : ℝ) / 6)) ^ 2) := by
  simp only [pieceD1, pieceD2]
  set q : ℝ := s ^ ((1 : ℝ) / 6) with hqdef
  have hq_pos : (0 : ℝ) < q := Real.rpow_pos_of_pos hs _
  have hden_pos : (0 : ℝ) < 1 + q := by positivity
  have hpow : ∀ n : ℕ, s ^ ((n : ℝ) / 6) = q ^ n := by
    intro n
    rw [hqdef, ← Real.rpow_natCast (s ^ ((1 : ℝ) / 6)) n, ← Real.rpow_mul hs.le]
    congr 1
    ring
  have h1 : s ^ (-(5 : ℝ) / 6) = (q ^ 5)⁻¹ := by
    rw [show (-(5 : ℝ) / 6) = -((5 : ℝ) / 6) by ring, Real.rpow_neg hs.le,
      show (5 : ℝ) / 6 = ((5 : ℕ) : ℝ) / 6 by norm_num, hpow 5]
  have h2 : s ^ (-(5 : ℝ) / 6 - 1) = (q ^ 11)⁻¹ := by
    rw [show (-(5 : ℝ) / 6 - 1) = -((11 : ℝ) / 6) by ring, Real.rpow_neg hs.le,
      show (11 : ℝ) / 6 = ((11 : ℕ) : ℝ) / 6 by norm_num, hpow 11]
  have h3 : s ^ ((1 : ℝ) / 6 - 1) = (q ^ 5)⁻¹ := by
    rw [show ((1 : ℝ) / 6 - 1) = -((5 : ℝ) / 6) by ring, Real.rpow_neg hs.le,
      show (5 : ℝ) / 6 = ((5 : ℕ) : ℝ) / 6 by norm_num, hpow 5]
  have h6 : s = q ^ 6 := by
    have := hpow 6
    rwa [show ((6 : ℕ) : ℝ) / 6 = 1 by norm_num, Real.rpow_one] at this
  rw [h1, h2, h3, h6]
  clear_value q
  have hqne : q ≠ 0 := ne_of_gt hq_pos
  have hdne : (1 : ℝ) + q ≠ 0 := ne_of_gt hden_pos
  field_simp
  ring

open InnerProductSpace in
/-- **Single-puncture Laplacian.** For `w ≠ 0`,
`Δ (ahlforsLogPieceSq ‖·‖²) w = (‖w‖²)^{1/6} / (18 ‖w‖² (1 + (‖w‖²)^{1/6})²)`.
This is the (positive) curvature contribution of one puncture; the full log-density's
Laplacian is the sum of this term at `0` and the analogous term at `1`. -/
theorem laplacian_ahlforsLogPieceSq_normSq {w : ℂ} (hw : w ≠ 0) :
    Δ (fun z : ℂ => ahlforsLogPieceSq (‖z‖ ^ 2)) w
      = (‖w‖ ^ 2) ^ ((1 : ℝ) / 6) /
          (18 * ‖w‖ ^ 2 * (1 + (‖w‖ ^ 2) ^ ((1 : ℝ) / 6)) ^ 2) := by
  set s : ℝ := ‖w‖ ^ 2 with hsdef
  have hs : (0 : ℝ) < s := by rw [hsdef]; positivity
  have hFC2 : ContDiffAt ℝ 2 ahlforsLogPieceSq s := contDiffAt_ahlforsLogPieceSq hs
  rw [laplacian_comp_normSq hFC2]
  have hderivF : deriv ahlforsLogPieceSq s = pieceD1 s := (hasDerivAt_ahlforsLogPieceSq hs).deriv
  have hEqOn : Set.EqOn (deriv ahlforsLogPieceSq) pieceD1 {x | 0 < x} :=
    fun x hx => (hasDerivAt_ahlforsLogPieceSq hx).deriv
  have hmem : {x : ℝ | 0 < x} ∈ nhds s :=
    (isOpen_lt continuous_const continuous_id).mem_nhds hs
  have hev : deriv ahlforsLogPieceSq =ᶠ[nhds s] pieceD1 := hEqOn.eventuallyEq_of_mem hmem
  have hiter2 : iteratedDeriv 2 ahlforsLogPieceSq s = pieceD2 s := by
    rw [iteratedDeriv_succ, iteratedDeriv_one, hev.deriv_eq]
    exact (hasDerivAt_pieceD1 hs).deriv
  rw [hderivF, hiter2]
  exact four_pieceD1_add_pieceD2_algebra hs

open InnerProductSpace in
/-- **Translation invariance of the Laplacian.** `Δ (fun z => g (z - a)) w = Δ g (w - a)`.
The Laplacian on `ℂ` is a sum of second iterated derivatives, each of which commutes with a
constant shift. -/
theorem laplacian_comp_sub (g : ℂ → ℝ) (a w : ℂ) :
    Δ (fun z : ℂ => g (z - a)) w = Δ g (w - a) := by
  simp only [laplacian_eq_iteratedFDeriv_complexPlane, iteratedFDeriv_comp_sub]

open InnerProductSpace in
/-- **Second single-puncture Laplacian (at `1`).** For `w ≠ 1`,
`Δ (ahlforsLogPieceSq ‖·-1‖²) w = (‖w-1‖²)^{1/6} / (18 ‖w-1‖² (1 + (‖w-1‖²)^{1/6})²)`. -/
theorem laplacian_ahlforsLogPieceSq_normSq_sub_one {w : ℂ} (hw : w ≠ 1) :
    Δ (fun z : ℂ => ahlforsLogPieceSq (‖z - 1‖ ^ 2)) w
      = (‖w - 1‖ ^ 2) ^ ((1 : ℝ) / 6) /
          (18 * ‖w - 1‖ ^ 2 * (1 + (‖w - 1‖ ^ 2) ^ ((1 : ℝ) / 6)) ^ 2) := by
  have hne : w - 1 ≠ 0 := sub_ne_zero.mpr hw
  rw [laplacian_comp_sub (fun z : ℂ => ahlforsLogPieceSq (‖z‖ ^ 2)) 1 w,
    laplacian_ahlforsLogPieceSq_normSq hne]

open InnerProductSpace in
/-- **Full ultrahyperbolic Laplacian.** On `ℂ \ {0,1}`, the Laplacian of the log-density is
the sum of the two positive single-puncture contributions (at `0` and at `1`). In particular
`Δ ultraLogDensity w > 0`, so the density is subharmonic (negative curvature). -/
theorem laplacian_ultraLogDensity {w : ℂ} (h0 : w ≠ 0) (h1 : w ≠ 1) :
    Δ ultraLogDensity w
      = (‖w‖ ^ 2) ^ ((1 : ℝ) / 6) /
          (18 * ‖w‖ ^ 2 * (1 + (‖w‖ ^ 2) ^ ((1 : ℝ) / 6)) ^ 2)
        + (‖w - 1‖ ^ 2) ^ ((1 : ℝ) / 6) /
          (18 * ‖w - 1‖ ^ 2 * (1 + (‖w - 1‖ ^ 2) ^ ((1 : ℝ) / 6)) ^ 2) := by
  have hp0 : ContDiffAt ℝ 2 (fun z : ℂ => ahlforsLogPieceSq (‖z‖ ^ 2)) w :=
    (contDiffAt_ahlforsLogPieceSq (by positivity)).comp w (contDiff_norm_sq ℝ).contDiffAt
  have hp1 : ContDiffAt ℝ 2 (fun z : ℂ => ahlforsLogPieceSq (‖z - 1‖ ^ 2)) w := by
    have hne : (0 : ℝ) < ‖w - 1‖ ^ 2 := by
      have : w - 1 ≠ 0 := sub_ne_zero.mpr h1; positivity
    exact (contDiffAt_ahlforsLogPieceSq hne).comp w
      ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)).contDiffAt
  have hsum : ultraLogDensity
      = (fun z : ℂ => ahlforsLogPieceSq (‖z‖ ^ 2))
        + (fun z : ℂ => ahlforsLogPieceSq (‖z - 1‖ ^ 2)) := by
    funext z; rfl
  rw [hsum, ContDiffAt.laplacian_add hp0 hp1,
    laplacian_ahlforsLogPieceSq_normSq h0, laplacian_ahlforsLogPieceSq_normSq_sub_one h1]

/-- **The curvature polynomial inequality.** For `a, b > 0` with `a³ + b³ ≥ 1` (the shape of the
triangle constraint `‖w‖ + ‖w-1‖ ≥ 1` after the substitution `a = ‖w‖^{1/3}`, `b = ‖w-1‖^{1/3}`),
`(9/500)(1+a)³(1+b)³ ≤ a⁵(1+a)² + b⁵(1+b)²`.  This is the cleared-denominator form of the
ultrahyperbolic curvature bound `Δ log σ ≥ (1/1000) σ²`; the constant `9/500 = 18/1000` lies just
below the true infimum `≈ 0.0608` of the ratio, attained at the symmetric point `a = b = 2^{-1/3}`.
The triangle constraint is essential: without it the ratio would degenerate to `0` as `a,b → 0`. -/
theorem curvature_poly {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : 1 ≤ a ^ 3 + b ^ 3) :
    (9 / 500) * (1 + a) ^ 3 * (1 + b) ^ 3 ≤ a ^ 5 * (1 + a) ^ 2 + b ^ 5 * (1 + b) ^ 2 := by
  have H : ∀ x y : ℝ, 0 < x → 0 < y → x ≤ y → 1 ≤ x ^ 3 + y ^ 3 →
      (9 / 500) * (1 + x) ^ 3 * (1 + y) ^ 3 ≤ x ^ 5 * (1 + x) ^ 2 + y ^ 5 * (1 + y) ^ 2 := by
    intro x y hx hy hxy _
    have hxle : x ^ 3 ≤ y ^ 3 := by gcongr
    have hy3 : 1 / 2 ≤ y ^ 3 := by nlinarith [hxle]
    by_cases hx1 : x ≤ 1
    · have hy5 : (18 / 125) * (1 + y) ≤ y ^ 5 := by
        nlinarith [hy3, hy, sq_nonneg y, sq_nonneg (y - 1), mul_pos hy hy,
          mul_pos (mul_pos hy hy) hy]
      have hcube : (1 + x) ^ 3 ≤ 8 := by nlinarith [hx1, hx.le, sq_nonneg x]
      have h1b2 : (0 : ℝ) ≤ (1 + y) ^ 2 := sq_nonneg _
      have h1b3 : (0 : ℝ) ≤ (1 + y) ^ 3 := by positivity
      have hterm : (0 : ℝ) ≤ x ^ 5 * (1 + x) ^ 2 := by positivity
      nlinarith [mul_nonneg (sub_nonneg.2 hy5) h1b2, mul_nonneg (sub_nonneg.2 hcube) h1b3,
        hterm, h1b3]
    · have hx1' : (1 : ℝ) < x := lt_of_not_ge hx1
      have hy1 : (1 : ℝ) < y := lt_of_lt_of_le hx1' hxy
      have hy2 : (18 / 125) * (1 + y) ≤ y ^ 2 := by nlinarith [hy1, hy.le]
      have hca : (1 + x) ^ 3 ≤ 8 * x ^ 3 := by nlinarith [hx1', hx.le, sq_nonneg (x - 1)]
      have hterm : (0 : ℝ) ≤ x ^ 5 * (1 + x) ^ 2 := by positivity
      have p1b : (0 : ℝ) ≤ (1 + y) ^ 3 := by positivity
      have p3 : (0 : ℝ) ≤ y ^ 3 * (1 + y) ^ 2 := by positivity
      nlinarith [mul_nonneg (sub_nonneg.2 hca) p1b, mul_nonneg (sub_nonneg.2 hxle) p1b,
        mul_nonneg (sub_nonneg.2 hy2) p3, hterm]
  rcases le_total a b with hle | hle
  · exact H a b ha hb hle hab
  · have hswap := H b a hb ha hle (by linarith)
    nlinarith [hswap]

/-- `(x^{1/6})^n = x^{n/6}` for `x ≥ 0`: the bridge from natural powers of the sixth root to
`rpow`. -/
theorem pow_rpow_sixth {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    (x ^ ((1 : ℝ) / 6)) ^ n = x ^ ((n : ℝ) / 6) := by
  rw [← Real.rpow_natCast (x ^ ((1 : ℝ) / 6)) n, ← Real.rpow_mul hx]
  congr 1
  ring

/-- `exp (2 · ahlforsLogPieceSq s) = (1 + s^{1/6}) / s^{5/6}`: the single-puncture density squared,
in closed form. -/
theorem exp_two_ahlforsLogPieceSq {s : ℝ} (hs : 0 < s) :
    Real.exp (2 * ahlforsLogPieceSq s) = (1 + s ^ ((1 : ℝ) / 6)) / s ^ ((5 : ℝ) / 6) := by
  have hp : (0 : ℝ) < 1 + s ^ ((1 : ℝ) / 6) := by positivity
  unfold ahlforsLogPieceSq
  rw [show 2 * ((1 / 2) * Real.log (1 + s ^ ((1 : ℝ) / 6)) - (5 / 12) * Real.log s)
        = Real.log (1 + s ^ ((1 : ℝ) / 6)) - (5 / 6) * Real.log s by ring,
     Real.exp_sub, Real.exp_log hp, mul_comm (5 / 6 : ℝ) (Real.log s),
     ← Real.rpow_def_of_pos hs]

open InnerProductSpace in
/-- **Curvature inequality for the ultrahyperbolic metric.** On `ℂ \ {0,1}`,
`(1/1000) · σ² ≤ Δ log σ`, where `σ = ultraDensity`. Equivalently, the rescaled metric
`√(1/1000)·σ |dz|` has Gaussian curvature `≤ -1`. This is the key nonpositive-curvature bound
that lets Ahlfors' lemma (`ahlfors_schwarz`) produce the Schwarz–Pick contraction
`𝔻 → ℂ \ {0,1}`. The proof substitutes `a = ‖w‖^{1/3}`, `b = ‖w-1‖^{1/3}`, converts both sides
to rational functions of `a, b`, and applies `curvature_poly` under the triangle constraint
`a³ + b³ = ‖w‖ + ‖w-1‖ ≥ 1`. -/
theorem curvature_ultraLogDensity {w : ℂ} (h0 : w ≠ 0) (h1 : w ≠ 1) :
    (1 / 1000) * ultraDensity w ^ 2 ≤ Δ ultraLogDensity w := by
  set a : ℝ := (‖w‖ ^ 2) ^ ((1 : ℝ) / 6) with hadef
  set b : ℝ := (‖w - 1‖ ^ 2) ^ ((1 : ℝ) / 6) with hbdef
  have hw0 : (0 : ℝ) < ‖w‖ := norm_pos_iff.2 h0
  have hw1 : (0 : ℝ) < ‖w - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 h1)
  have ha : 0 < a := Real.rpow_pos_of_pos (by positivity) _
  have hb : 0 < b := Real.rpow_pos_of_pos (by positivity) _
  have ha3 : a ^ 3 = ‖w‖ := by
    rw [hadef, pow_rpow_sixth (by positivity) 3, show ((3 : ℕ) : ℝ) / 6 = (1 : ℝ) / 2 by norm_num,
      ← Real.rpow_natCast ‖w‖ 2, ← Real.rpow_mul (norm_nonneg _)]; norm_num
  have hb3 : b ^ 3 = ‖w - 1‖ := by
    rw [hbdef, pow_rpow_sixth (by positivity) 3, show ((3 : ℕ) : ℝ) / 6 = (1 : ℝ) / 2 by norm_num,
      ← Real.rpow_natCast ‖w - 1‖ 2, ← Real.rpow_mul (norm_nonneg _)]; norm_num
  have ha6 : ‖w‖ ^ 2 = a ^ 6 := by
    rw [hadef, pow_rpow_sixth (by positivity) 6, show ((6 : ℕ) : ℝ) / 6 = (1 : ℝ) by norm_num,
      Real.rpow_one]
  have hb6 : ‖w - 1‖ ^ 2 = b ^ 6 := by
    rw [hbdef, pow_rpow_sixth (by positivity) 6, show ((6 : ℕ) : ℝ) / 6 = (1 : ℝ) by norm_num,
      Real.rpow_one]
  have ha5 : (‖w‖ ^ 2) ^ ((5 : ℝ) / 6) = a ^ 5 := by
    rw [hadef, pow_rpow_sixth (by positivity) 5, show ((5 : ℕ) : ℝ) / 6 = (5 : ℝ) / 6 by norm_num]
  have hb5 : (‖w - 1‖ ^ 2) ^ ((5 : ℝ) / 6) = b ^ 5 := by
    rw [hbdef, pow_rpow_sixth (by positivity) 5, show ((5 : ℕ) : ℝ) / 6 = (5 : ℝ) / 6 by norm_num]
  have hcon : 1 ≤ a ^ 3 + b ^ 3 := by
    rw [ha3, hb3]
    have h := norm_sub_le w (w - 1)
    rw [sub_sub_cancel] at h
    simpa using h
  have hLap : Δ ultraLogDensity w
      = 1 / (18 * a ^ 5 * (1 + a) ^ 2) + 1 / (18 * b ^ 5 * (1 + b) ^ 2) := by
    rw [laplacian_ultraLogDensity h0 h1, ← hadef, ← hbdef, ha6, hb6]
    have hane : a ≠ 0 := ne_of_gt ha
    have hbne : b ≠ 0 := ne_of_gt hb
    have h1a : (1 : ℝ) + a ≠ 0 := by positivity
    have h1b : (1 : ℝ) + b ≠ 0 := by positivity
    field_simp
  have hDen : ultraDensity w ^ 2 = ((1 + a) / a ^ 5) * ((1 + b) / b ^ 5) := by
    have hs0 : (0 : ℝ) < ‖w‖ ^ 2 := by positivity
    have hs1 : (0 : ℝ) < ‖w - 1‖ ^ 2 := by positivity
    rw [ultraDensity, pow_two, ← Real.exp_add, ultraLogDensity,
      show (ahlforsLogPieceSq (‖w‖ ^ 2) + ahlforsLogPieceSq (‖w - 1‖ ^ 2))
          + (ahlforsLogPieceSq (‖w‖ ^ 2) + ahlforsLogPieceSq (‖w - 1‖ ^ 2))
          = 2 * ahlforsLogPieceSq (‖w‖ ^ 2) + 2 * ahlforsLogPieceSq (‖w - 1‖ ^ 2) by ring,
      Real.exp_add, exp_two_ahlforsLogPieceSq hs0, exp_two_ahlforsLogPieceSq hs1,
      ← hadef, ← hbdef, ha5, hb5]
  rw [hLap, hDen]
  have poly := curvature_poly ha hb hcon
  rw [div_add_div _ _ (by positivity) (by positivity),
    show (1 / 1000) * ((1 + a) / a ^ 5 * ((1 + b) / b ^ 5))
        = ((1 + a) * (1 + b)) / (1000 * a ^ 5 * b ^ 5) by field_simp,
    div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left poly (show (0 : ℝ) ≤ 18000 * a ^ 5 * b ^ 5 by positivity),
    mul_pos ha hb, ha, hb]

/-- The **rescaled** ultrahyperbolic log-density: adding the constant `½·log(1/1000)` rescales
the metric `ultraDensity` by the factor `√(1/1000)`, exactly enough to turn the curvature bound
`curvature_ultraLogDensity` into curvature `≤ -1`, i.e. the hypothesis `exp(2u) ≤ Δu` consumed by
`ahlfors_schwarz`. -/
noncomputable def ultraLogDensityScaled (w : ℂ) : ℝ :=
  (1 / 2) * Real.log (1 / 1000) + ultraLogDensity w

theorem contDiffAt_ultraLogDensityScaled {w : ℂ} (h0 : w ≠ 0) (h1 : w ≠ 1) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n ultraLogDensityScaled w :=
  contDiffAt_const.add (contDiffAt_ultraLogDensity h0 h1)

open InnerProductSpace in
/-- **Curvature `≤ -1` for the rescaled metric.** The rescaled log-density satisfies
`exp(2·u) ≤ Δu` on `ℂ \ {0,1}`, which is exactly the negative-curvature hypothesis required by
`ahlfors_schwarz`. This packages `curvature_ultraLogDensity` in the pullback-ready form. -/
theorem exp_two_ultraLogDensityScaled_le_laplacian {w : ℂ} (h0 : w ≠ 0) (h1 : w ≠ 1) :
    Real.exp (2 * ultraLogDensityScaled w) ≤ Δ ultraLogDensityScaled w := by
  have hlap : Δ ultraLogDensityScaled w = Δ ultraLogDensity w := by
    have he : ultraLogDensityScaled
        = (fun _ : ℂ => (1 / 2) * Real.log (1 / 1000)) + ultraLogDensity := rfl
    rw [he, ContDiffAt.laplacian_add contDiffAt_const (contDiffAt_ultraLogDensity h0 h1),
      laplacian_const, zero_add]
  have hexp : Real.exp (2 * ultraLogDensityScaled w) = (1 / 1000) * ultraDensity w ^ 2 := by
    have h2 : ultraDensity w ^ 2 = Real.exp (2 * ultraLogDensity w) := by
      rw [ultraDensity, ← Real.exp_nat_mul]; norm_num
    rw [ultraLogDensityScaled, mul_add, h2,
      show (2 : ℝ) * ((1 / 2) * Real.log (1 / 1000)) = Real.log (1 / 1000) by ring,
      Real.exp_add, Real.exp_log (by norm_num)]
  rw [hlap, hexp]
  exact curvature_ultraLogDensity h0 h1

/-- **Near-puncture growth lower bound.** Since the smooth factor `½ log(1 + s^{1/6})` is
nonnegative, each single-puncture piece dominates its logarithmic singularity, giving the global
bound `ultraLogDensity w ≥ -(5/6)(log‖w‖ + log‖w-1‖)`.  Near a puncture this exhibits the
`‖w-·‖^{-5/6}` blow-up of the density.

**Note (completeness).** The exponent `5/6 < 1` means the radial distance element
`ultraDensity·d‖w-1‖ ∼ ‖w-1‖^{-5/6} d‖w-1‖` integrates to a *finite* value at the puncture: the
Ahlfors supporting metric is **not complete**.  This is the precise obstruction to the naive
Mañé–Sad–Sullivan confinement (which requires the target distance to a puncture to be infinite);
the continuity endgame needs a *complete* metric of curvature `≤ -1` (a `log log` cusp correction),
or an alternative to the confinement argument. -/
theorem ultraLogDensity_ge {w : ℂ} (h0 : w ≠ 0) (h1 : w ≠ 1) :
    ultraLogDensity w ≥ -(5/6) * Real.log ‖w‖ - (5/6) * Real.log ‖w - 1‖ := by
  have e0 : Real.log (‖w‖ ^ 2) = 2 * Real.log ‖w‖ := by rw [Real.log_pow]; norm_num
  have e1 : Real.log (‖w - 1‖ ^ 2) = 2 * Real.log ‖w - 1‖ := by rw [Real.log_pow]; norm_num
  have hpiece : ∀ s : ℝ, 0 ≤ s → ahlforsLogPieceSq s ≥ -(5/12) * Real.log s := by
    intro s hs
    have hlog : (0:ℝ) ≤ Real.log (1 + s ^ ((1:ℝ)/6)) :=
      Real.log_nonneg (by linarith [Real.rpow_nonneg hs ((1:ℝ)/6)])
    unfold ahlforsLogPieceSq; linarith
  have b0 := hpiece (‖w‖ ^ 2) (sq_nonneg ‖w‖)
  have b1 := hpiece (‖w - 1‖ ^ 2) (sq_nonneg ‖w - 1‖)
  rw [e0] at b0; rw [e1] at b1
  unfold ultraLogDensity; linarith

end

end MLC.Quadratic
