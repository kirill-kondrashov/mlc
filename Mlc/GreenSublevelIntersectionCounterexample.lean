import Mlc.ParaPuzzleConnectivity
import Molecule.Mol

/-!
# A counterexample to the categorical Green-sublevel intersection datum

This module formalises the negation of
`MLC.GreenSublevelIntersectionCategoricalData`, following
the counterexample reference.

The counterexample is `c = i`, `n = 16`. Writing
`A = {p | G_i(p - i) < (1/2)^16}` and `S = A ∩ M`, the points `0` and `i` lie
in `S`, the point `2i` lies in `A \ M` (so the non-factorisation hypothesis
holds), and no point of `S` has imaginary part `45/64`. Hence `S` is
disconnected while the categorical datum would force it to be connected.

The horizontal line `Im p = 45/64` is excluded by a finite certificate of
outward-rounded integer interval arithmetic: for every real `x ∈ [-2, 2]`
either the critical orbit of the parameter `x + (45/64)i` leaves the disc of
radius `2` within `16` steps (so the parameter is not in `M`), or the orbit of
`x + (45/64)i - i` under `z ↦ z² + i` leaves the disc of radius `4` within
`15` steps (so its Green value exceeds `2⁻¹⁶`).

The certificate itself is checked by the kernel with `decide`; everything else
is an ordinary proof. No `sorry`, `axiom` or `native_decide` is used here.
-/

open Complex Set MLC.Quadratic

namespace MLC.GreenCounterexample

/-! ## Integer interval arithmetic

An interval `(lo, hi)` represents the set of reals `[lo / scale, hi / scale]`,
and a box represents a rectangle in `ℂ`. All rounding is outward, so every
operation returns an enclosure of the corresponding exact operation. -/

abbrev Interval := Int × Int
abbrev Box := Interval × Interval
abbrev Cell := Int × Int × Bool × Nat

/-- The working denominator `2 ^ 48`. -/
def scale : Int := 281474976710656

def add (a b : Interval) : Interval := (a.1 + b.1, a.2 + b.2)

def sub (a b : Interval) : Interval := (a.1 - b.2, a.2 - b.1)

/-- Division by `scale`, rounded up. -/
def ceilDiv (a : Int) : Int := -((-a) / scale)

def mul (a b : Interval) : Interval :=
  let v₁ := a.1 * b.1
  let v₂ := a.1 * b.2
  let v₃ := a.2 * b.1
  let v₄ := a.2 * b.2
  (min (min v₁ v₂) (min v₃ v₄) / scale,
   ceilDiv (max (max v₁ v₂) (max v₃ v₄)))

def sq (a : Interval) : Interval :=
  let lo := if a.1 ≤ 0 ∧ 0 ≤ a.2 then 0
            else min (a.1 * a.1) (a.2 * a.2)
  let hi := max (a.1 * a.1) (a.2 * a.2)
  (lo / scale, ceilDiv hi)

/-- One step of `z ↦ z ^ 2 + c` on boxes. -/
def step (z c : Box) : Box :=
  let xy := mul z.1 z.2
  (add (sub (sq z.1) (sq z.2)) c.1,
   add (2 * xy.1, 2 * xy.2) c.2)

def iterateBox (c : Box) : Nat → Box → Box
  | 0, z => z
  | n + 1, z => iterateBox c n (step z c)

/-- A lower bound (at denominator `scale`) for the squared modulus of any point
    of the box. -/
def normLower (z : Box) : Int := (sq z.1).1 + (sq z.2).1

/-! ## Soundness of the interval semantics -/

/-- `x : ℝ` is enclosed by the integer interval `a` at denominator `scale`. -/
def MemI (a : Interval) (x : ℝ) : Prop :=
  (a.1 : ℝ) ≤ (scale : ℝ) * x ∧ (scale : ℝ) * x ≤ (a.2 : ℝ)

/-- `w : ℂ` is enclosed by the interval box `z`. -/
def MemB (z : Box) (w : ℂ) : Prop := MemI z.1 w.re ∧ MemI z.2 w.im

lemma scale_pos : (0 : ℝ) < (scale : ℝ) := by
  norm_num [scale]

lemma scale_ne_zero : (scale : ℤ) ≠ 0 := by
  norm_num [scale]

lemma ediv_mul_le (m : ℤ) : (m / scale) * scale ≤ m := by
  have h1 : scale * (m / scale) + m % scale = m := Int.mul_ediv_add_emod m scale
  have h2 : 0 ≤ m % scale := Int.emod_nonneg m scale_ne_zero
  have h3 : (m / scale) * scale = scale * (m / scale) := mul_comm _ _
  omega

lemma le_ceilDiv_mul (m : ℤ) : m ≤ (ceilDiv m) * scale := by
  have h := ediv_mul_le (-m)
  have hneg : ceilDiv m * scale = -(((-m) / scale) * scale) := by
    simp [ceilDiv, neg_mul]
  omega

lemma cast_ediv_le {m : ℤ} {t : ℝ} (h : (m : ℝ) ≤ (scale : ℝ) * t) :
    ((m / scale : ℤ) : ℝ) ≤ t := by
  have h1 : ((m / scale : ℤ) : ℝ) * (scale : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast ediv_mul_le m
  have h2 : ((m / scale : ℤ) : ℝ) * (scale : ℝ) ≤ t * (scale : ℝ) := by
    nlinarith [scale_pos]
  exact le_of_mul_le_mul_right h2 scale_pos

lemma le_cast_ceilDiv {m : ℤ} {t : ℝ} (h : (scale : ℝ) * t ≤ (m : ℝ)) :
    t ≤ ((ceilDiv m : ℤ) : ℝ) := by
  have h1 : (m : ℝ) ≤ ((ceilDiv m : ℤ) : ℝ) * (scale : ℝ) := by
    exact_mod_cast le_ceilDiv_mul m
  have h2 : t * (scale : ℝ) ≤ ((ceilDiv m : ℤ) : ℝ) * (scale : ℝ) := by
    nlinarith [scale_pos]
  exact le_of_mul_le_mul_right h2 scale_pos

lemma mem_add {a b : Interval} {x y : ℝ} (ha : MemI a x) (hb : MemI b y) :
    MemI (add a b) (x + y) := by
  obtain ⟨h1, h2⟩ := ha
  obtain ⟨h3, h4⟩ := hb
  have hexp : (scale : ℝ) * (x + y) = (scale : ℝ) * x + (scale : ℝ) * y := by ring
  refine ⟨?_, ?_⟩ <;> simp only [add, Int.cast_add] <;> rw [hexp] <;> linarith

lemma mem_sub {a b : Interval} {x y : ℝ} (ha : MemI a x) (hb : MemI b y) :
    MemI (sub a b) (x - y) := by
  obtain ⟨h1, h2⟩ := ha
  obtain ⟨h3, h4⟩ := hb
  have hexp : (scale : ℝ) * (x - y) = (scale : ℝ) * x - (scale : ℝ) * y := by ring
  refine ⟨?_, ?_⟩ <;> simp only [sub, Int.cast_sub] <;> rw [hexp] <;> linarith

lemma mem_double {a : Interval} {x : ℝ} (h : MemI a x) :
    MemI (2 * a.1, 2 * a.2) (2 * x) := by
  obtain ⟨h1, h2⟩ := h
  have hexp : (scale : ℝ) * (2 * x) = 2 * ((scale : ℝ) * x) := by ring
  refine ⟨?_, ?_⟩ <;> push_cast <;> rw [hexp] <;> linarith

/-- A product is monotone, hence enclosed by its endpoint values, in each
    variable separately. -/
lemma between_mul {l u t : ℝ} (h1 : l ≤ t) (h2 : t ≤ u) (y : ℝ) :
    min (l * y) (u * y) ≤ t * y ∧ t * y ≤ max (l * y) (u * y) := by
  rcases le_total 0 y with hy | hy
  · constructor
    · exact le_trans (min_le_left _ _) (by nlinarith)
    · exact le_trans (by nlinarith) (le_max_right _ _)
  · constructor
    · exact le_trans (min_le_right _ _) (by nlinarith)
    · exact le_trans (by nlinarith) (le_max_left _ _)

/-- The product of two points of real intervals lies between the smallest and
    the largest of the four corner products. -/
lemma corner_bounds {l u r s X Y : ℝ} (h1 : l ≤ X) (h2 : X ≤ u) (h3 : r ≤ Y)
    (h4 : Y ≤ s) :
    min (min (l * r) (l * s)) (min (u * r) (u * s)) ≤ X * Y ∧
      X * Y ≤ max (max (l * r) (l * s)) (max (u * r) (u * s)) := by
  obtain ⟨hA, hB⟩ := between_mul h1 h2 Y
  obtain ⟨hC, hD⟩ := between_mul h3 h4 l
  obtain ⟨hE, hF⟩ := between_mul h3 h4 u
  rw [mul_comm r l, mul_comm s l, mul_comm Y l] at hC hD
  rw [mul_comm r u, mul_comm s u, mul_comm Y u] at hE hF
  constructor
  · refine le_trans (le_min ?_ ?_) hA
    · exact le_trans (min_le_left _ _) hC
    · exact le_trans (min_le_right _ _) hE
  · refine le_trans hB (max_le ?_ ?_)
    · exact le_trans hD (le_max_left _ _)
    · exact le_trans hF (le_max_right _ _)

lemma mem_mul {a b : Interval} {x y : ℝ} (ha : MemI a x) (hb : MemI b y) :
    MemI (mul a b) (x * y) := by
  obtain ⟨h1, h2⟩ := ha
  obtain ⟨h3, h4⟩ := hb
  obtain ⟨hlow, hhigh⟩ := corner_bounds h1 h2 h3 h4
  have hprod : ((scale : ℝ) * x) * ((scale : ℝ) * y)
      = (scale : ℝ) * ((scale : ℝ) * (x * y)) := by ring
  rw [hprod] at hlow hhigh
  constructor
  · refine cast_ediv_le ?_
    push_cast
    exact hlow
  · exact le_cast_ceilDiv (by push_cast; exact hhigh)

lemma mem_sq {a : Interval} {x : ℝ} (ha : MemI a x) : MemI (sq a) (x * x) := by
  obtain ⟨h1, h2⟩ := ha
  have hprod : ((scale : ℝ) * x) * ((scale : ℝ) * x)
      = (scale : ℝ) * ((scale : ℝ) * (x * x)) := by ring
  constructor
  · by_cases hc : a.1 ≤ 0 ∧ 0 ≤ a.2
    · have hz : (sq a).1 = 0 := by simp [sq, hc]
      rw [hz]
      have hnn : (0 : ℝ) ≤ (scale : ℝ) * (x * x) := by
        have := scale_pos
        nlinarith [mul_self_nonneg x]
      simpa using hnn
    · have hz : (sq a).1 = min (a.1 * a.1) (a.2 * a.2) / scale := by simp [sq, hc]
      rw [hz]
      refine cast_ediv_le ?_
      push_cast
      rw [← hprod]
      rcases not_and_or.mp hc with hc1 | hc2
      · have hpos : (0 : ℝ) < (a.1 : ℝ) := by exact_mod_cast lt_of_not_ge hc1
        have hle : ((a.1 : ℝ) * (a.1 : ℝ)) ≤ ((scale : ℝ) * x) * ((scale : ℝ) * x) := by
          nlinarith
        exact le_trans (min_le_left _ _) hle
      · have hneg : ((a.2 : ℝ)) < 0 := by exact_mod_cast lt_of_not_ge hc2
        have hle : ((a.2 : ℝ) * (a.2 : ℝ)) ≤ ((scale : ℝ) * x) * ((scale : ℝ) * x) := by
          nlinarith
        exact le_trans (min_le_right _ _) hle
  · have hz : (sq a).2 = ceilDiv (max (a.1 * a.1) (a.2 * a.2)) := by simp [sq]
    rw [hz]
    refine le_cast_ceilDiv ?_
    push_cast
    rw [← hprod]
    rcases le_total 0 ((scale : ℝ) * x) with hx | hx
    · have hle : ((scale : ℝ) * x) * ((scale : ℝ) * x) ≤ (a.2 : ℝ) * (a.2 : ℝ) := by
        nlinarith
      exact le_trans hle (le_max_right _ _)
    · have hle : ((scale : ℝ) * x) * ((scale : ℝ) * x) ≤ (a.1 : ℝ) * (a.1 : ℝ) := by
        nlinarith
      exact le_trans hle (le_max_left _ _)

lemma mem_step {Z C : Box} {z c : ℂ} (hz : MemB Z z) (hc : MemB C c) :
    MemB (step Z C) (z ^ 2 + c) := by
  obtain ⟨hzr, hzi⟩ := hz
  obtain ⟨hcr, hci⟩ := hc
  constructor
  · have h := mem_add (mem_sub (mem_sq hzr) (mem_sq hzi)) hcr
    have hre : (z ^ 2 + c).re = z.re * z.re - z.im * z.im + c.re := by
      simp [pow_two, Complex.add_re, Complex.mul_re]
    show MemI (step Z C).1 ((z ^ 2 + c).re)
    rw [hre]
    exact h
  · have h := mem_add (mem_double (mem_mul hzr hzi)) hci
    have him : (z ^ 2 + c).im = 2 * (z.re * z.im) + c.im := by
      simp [pow_two, Complex.add_im, Complex.mul_im]
      ring
    show MemI (step Z C).2 ((z ^ 2 + c).im)
    rw [him]
    exact h

lemma orbit_succ_eq (c z : ℂ) (n : ℕ) : orbit c z (n + 1) = orbit c (z ^ 2 + c) n := by
  simp [orbit, fc, Function.iterate_succ_apply]

/-- Box iteration encloses the orbit of any enclosed starting point under any
    enclosed parameter. The parameter is fixed throughout the induction. -/
lemma mem_iterateBox {C : Box} {c : ℂ} (hc : MemB C c) :
    ∀ (n : ℕ) {Z : Box} {z : ℂ}, MemB Z z → MemB (iterateBox C n Z) (orbit c z n) := by
  intro n
  induction n with
  | zero => intro Z z hz; simpa [iterateBox] using hz
  | succ n ih =>
    intro Z z hz
    have hstep : MemB (step Z C) (z ^ 2 + c) := mem_step hz hc
    rw [orbit_succ_eq]
    simpa [iterateBox] using ih hstep

lemma normLower_le {Z : Box} {w : ℂ} (h : MemB Z w) :
    ((normLower Z : ℤ) : ℝ) ≤ (scale : ℝ) * ‖w‖ ^ 2 := by
  obtain ⟨hr, hi⟩ := h
  have h1 := (mem_sq hr).1
  have h2 := (mem_sq hi).1
  have hnorm : ‖w‖ ^ 2 = w.re * w.re + w.im * w.im := by
    rw [Complex.sq_norm, Complex.normSq_apply]
  rw [hnorm]
  have hsplit : ((normLower Z : ℤ) : ℝ) = (((sq Z.1).1 : ℤ) : ℝ) + (((sq Z.2).1 : ℤ) : ℝ) := by
    simp [normLower]
  rw [hsplit]
  have hexp : (scale : ℝ) * (w.re * w.re + w.im * w.im)
      = (scale : ℝ) * (w.re * w.re) + (scale : ℝ) * (w.im * w.im) := by ring
  rw [hexp]
  linarith

lemma norm_gt_of_normLower {Z : Box} {w : ℂ} (h : MemB Z w) {t : ℝ} (ht : 0 ≤ t)
    (hn : (scale : ℝ) * t ^ 2 < ((normLower Z : ℤ) : ℝ)) : t < ‖w‖ := by
  have hle := normLower_le h
  have hlt : (scale : ℝ) * t ^ 2 < (scale : ℝ) * ‖w‖ ^ 2 := lt_of_lt_of_le hn hle
  have hsq : t ^ 2 < ‖w‖ ^ 2 := lt_of_mul_lt_mul_left hlt (le_of_lt scale_pos)
  nlinarith [norm_nonneg w]

lemma two_lt_norm {Z : Box} {w : ℂ} (h : MemB Z w) (hn : 4 * scale < normLower Z) :
    2 < ‖w‖ := by
  refine norm_gt_of_normLower h (by norm_num) ?_
  have hcast : ((4 * scale : ℤ) : ℝ) < ((normLower Z : ℤ) : ℝ) := by exact_mod_cast hn
  push_cast at hcast
  nlinarith [scale_pos]

lemma four_lt_norm {Z : Box} {w : ℂ} (h : MemB Z w) (hn : 16 * scale < normLower Z) :
    4 < ‖w‖ := by
  refine norm_gt_of_normLower h (by norm_num) ?_
  have hcast : ((16 * scale : ℤ) : ℝ) < ((normLower Z : ℤ) : ℝ) := by exact_mod_cast hn
  push_cast at hcast
  nlinarith [scale_pos]

/-! ## The finite certificate

Each row `(l, r, parameter, k)` claims an escape statement, valid for every
real point of `[l / 16384, r / 16384]`:

* `parameter = true`: the critical orbit of `x + (45/64) i` has modulus larger
  than `2` after `k ≤ 16` steps;
* `parameter = false`: the orbit of `x + (45/64) i - i` under `z ↦ z ^ 2 + i`
  has modulus larger than `4` after `k ≤ 15` steps. -/

def checkCell (t : Cell) : Bool :=
  let (a, b, parameter, k) := t
  let x : Interval := (a * (scale / 16384), b * (scale / 16384))
  let y : Int := 45 * (scale / 64)
  let p : Box := (x, (y, y))
  let result := if parameter
    then iterateBox p k ((0, 0), (0, 0))
    else iterateBox ((0, 0), (scale, scale)) k (x, (y - scale, y - scale))
  decide (a < b ∧ 1 ≤ k ∧
    (if parameter then k ≤ 16 else k ≤ 15) ∧
    normLower result > (if parameter then 4 else 16) * scale)

/-- Adjacency check: the rows tile `[-32768, 32768]` (at denominator `16384`). -/
def coverFrom : Int → List Cell → Bool
  | a, [] => decide (a = 32768)
  | a, (l, r, _, _) :: tail => decide (a = l ∧ l < r) && coverFrom r tail

set_option maxHeartbeats 1000000 in
/-- The 298 verified rows: 150 parameter rows and 148 dynamical rows, with
    adjacent endpoints tiling `[-2, 2]` at denominator `16384`. -/
def cells : List Cell := [
  (-32768, -24576, false, 2),
  (-24576, -16384, false, 3),
  (-16384, -12288, false, 3),
  (-12288, -10240, false, 3),
  (-10240, -8192, false, 4),
  (-8192, -7168, false, 4),
  (-7168, -6144, false, 4),
  (-6144, -5120, false, 5),
  (-5120, -4608, false, 5),
  (-4608, -4096, false, 5),
  (-4096, -3840, false, 6),
  (-3840, -3584, false, 6),
  (-3584, -3328, false, 6),
  (-3328, -3200, false, 6),
  (-3200, -3072, false, 6),
  (-3072, -2944, false, 7),
  (-2944, -2816, false, 7),
  (-2816, -2688, false, 7),
  (-2688, -2560, false, 7),
  (-2560, -2496, false, 7),
  (-2496, -2432, false, 7),
  (-2432, -2368, false, 7),
  (-2368, -2304, false, 8),
  (-2304, -2240, false, 8),
  (-2240, -2176, false, 8),
  (-2176, -2112, false, 8),
  (-2112, -2048, false, 8),
  (-2048, -1984, false, 8),
  (-1984, -1920, false, 8),
  (-1920, -1856, false, 8),
  (-1856, -1792, false, 9),
  (-1792, -1728, false, 9),
  (-1728, -1664, false, 9),
  (-1664, -1600, false, 9),
  (-1600, -1536, false, 9),
  (-1536, -1472, false, 9),
  (-1472, -1408, false, 9),
  (-1408, -1376, false, 9),
  (-1376, -1344, false, 9),
  (-1344, -1312, false, 9),
  (-1312, -1280, false, 9),
  (-1280, -1216, false, 10),
  (-1216, -1152, false, 10),
  (-1152, -1120, false, 10),
  (-1120, -1088, false, 10),
  (-1088, -1056, false, 10),
  (-1056, -1024, false, 10),
  (-1024, -992, false, 10),
  (-992, -960, false, 10),
  (-960, -928, false, 11),
  (-928, -896, false, 11),
  (-896, -864, false, 11),
  (-864, -832, false, 11),
  (-832, -800, false, 11),
  (-800, -768, false, 11),
  (-768, -736, false, 11),
  (-736, -704, false, 11),
  (-704, -688, false, 11),
  (-688, -672, false, 11),
  (-672, -656, false, 11),
  (-656, -640, false, 11),
  (-640, -624, false, 12),
  (-624, -608, false, 12),
  (-608, -592, false, 12),
  (-592, -576, false, 12),
  (-576, -560, false, 12),
  (-560, -544, false, 12),
  (-544, -528, false, 12),
  (-528, -512, false, 12),
  (-512, -496, false, 12),
  (-496, -480, false, 12),
  (-480, -464, false, 12),
  (-464, -456, false, 12),
  (-456, -448, false, 12),
  (-448, -440, false, 12),
  (-440, -432, false, 12),
  (-432, -424, false, 12),
  (-424, -416, false, 12),
  (-416, -408, false, 13),
  (-408, -400, false, 13),
  (-400, -392, false, 13),
  (-392, -384, false, 13),
  (-384, -376, false, 13),
  (-376, -368, false, 13),
  (-368, -360, false, 13),
  (-360, -352, false, 13),
  (-352, -344, false, 13),
  (-344, -336, false, 13),
  (-336, -328, false, 13),
  (-328, -320, false, 13),
  (-320, -312, false, 13),
  (-312, -304, false, 13),
  (-304, -296, false, 13),
  (-296, -288, false, 14),
  (-288, -280, false, 14),
  (-280, -272, false, 14),
  (-272, -264, false, 14),
  (-264, -256, false, 14),
  (-256, -248, false, 14),
  (-248, -240, false, 14),
  (-240, -236, false, 14),
  (-236, -232, false, 14),
  (-232, -228, false, 14),
  (-228, -224, false, 14),
  (-224, -220, false, 14),
  (-220, -216, false, 14),
  (-216, -212, false, 14),
  (-212, -208, false, 14),
  (-208, -204, false, 14),
  (-204, -200, false, 15),
  (-200, -196, false, 15),
  (-196, -192, false, 15),
  (-192, -188, false, 15),
  (-188, -184, false, 15),
  (-184, -180, false, 15),
  (-180, -176, false, 15),
  (-176, -172, false, 15),
  (-172, -170, false, 15),
  (-170, -168, false, 15),
  (-168, -166, false, 15),
  (-166, -164, false, 15),
  (-164, -162, false, 15),
  (-162, -160, false, 15),
  (-160, -158, false, 15),
  (-158, -156, false, 15),
  (-156, -154, false, 15),
  (-154, -152, false, 15),
  (-152, -150, false, 15),
  (-150, -148, false, 15),
  (-148, -146, false, 15),
  (-146, -145, false, 15),
  (-145, -144, false, 15),
  (-144, -143, false, 15),
  (-143, -142, false, 15),
  (-142, -141, false, 15),
  (-141, -140, false, 15),
  (-140, -139, false, 15),
  (-139, -138, false, 15),
  (-138, -137, false, 15),
  (-137, -136, false, 15),
  (-136, -135, true, 16),
  (-135, -134, true, 16),
  (-134, -133, true, 16),
  (-133, -132, true, 16),
  (-132, -131, true, 16),
  (-131, -130, true, 16),
  (-130, -129, true, 16),
  (-129, -128, true, 16),
  (-128, -127, true, 15),
  (-127, -126, true, 15),
  (-126, -125, true, 15),
  (-125, -124, true, 15),
  (-124, -123, true, 15),
  (-123, -122, true, 15),
  (-122, -121, true, 15),
  (-121, -120, true, 15),
  (-120, -119, true, 15),
  (-119, -118, true, 15),
  (-118, -117, true, 15),
  (-117, -116, true, 15),
  (-116, -115, true, 15),
  (-115, -114, true, 15),
  (-114, -112, true, 15),
  (-112, -110, true, 15),
  (-110, -108, true, 15),
  (-108, -106, true, 15),
  (-106, -104, true, 15),
  (-104, -102, true, 15),
  (-102, -100, true, 15),
  (-100, -98, true, 15),
  (-98, -96, true, 15),
  (-96, -94, true, 15),
  (-94, -92, true, 15),
  (-92, -90, true, 14),
  (-90, -88, true, 14),
  (-88, -86, true, 14),
  (-86, -84, true, 14),
  (-84, -82, true, 14),
  (-82, -80, true, 14),
  (-80, -78, true, 14),
  (-78, -76, true, 14),
  (-76, -74, true, 14),
  (-74, -72, true, 14),
  (-72, -68, true, 14),
  (-68, -64, true, 14),
  (-64, -60, true, 14),
  (-60, -56, true, 14),
  (-56, -52, true, 14),
  (-52, -48, true, 14),
  (-48, -44, true, 14),
  (-44, -40, true, 14),
  (-40, -36, true, 13),
  (-36, -32, true, 13),
  (-32, -28, true, 13),
  (-28, -24, true, 13),
  (-24, -20, true, 13),
  (-20, -16, true, 13),
  (-16, -12, true, 13),
  (-12, -8, true, 13),
  (-8, -4, true, 13),
  (-4, 0, true, 13),
  (0, 8, true, 13),
  (8, 16, true, 13),
  (16, 24, true, 13),
  (24, 32, true, 13),
  (32, 40, true, 13),
  (40, 48, true, 13),
  (48, 56, true, 13),
  (56, 64, true, 13),
  (64, 72, true, 13),
  (72, 80, true, 12),
  (80, 88, true, 12),
  (88, 96, true, 12),
  (96, 104, true, 12),
  (104, 112, true, 12),
  (112, 128, true, 12),
  (128, 144, true, 12),
  (144, 160, true, 12),
  (160, 176, true, 12),
  (176, 192, true, 12),
  (192, 208, true, 12),
  (208, 224, true, 12),
  (224, 240, true, 11),
  (240, 256, true, 11),
  (256, 272, true, 11),
  (272, 288, true, 11),
  (288, 304, true, 11),
  (304, 320, true, 11),
  (320, 336, true, 11),
  (336, 352, true, 11),
  (352, 384, true, 11),
  (384, 416, true, 11),
  (416, 448, true, 11),
  (448, 480, true, 11),
  (480, 512, true, 11),
  (512, 576, true, 11),
  (576, 640, true, 11),
  (640, 704, true, 11),
  (704, 736, true, 10),
  (736, 768, true, 10),
  (768, 832, true, 10),
  (832, 896, true, 10),
  (896, 960, true, 10),
  (960, 1024, true, 9),
  (1024, 1088, true, 9),
  (1088, 1152, true, 9),
  (1152, 1216, true, 9),
  (1216, 1280, true, 9),
  (1280, 1344, true, 9),
  (1344, 1408, true, 9),
  (1408, 1472, true, 9),
  (1472, 1536, true, 9),
  (1536, 1600, true, 9),
  (1600, 1664, true, 9),
  (1664, 1728, true, 9),
  (1728, 1792, true, 9),
  (1792, 1856, true, 9),
  (1856, 1920, true, 9),
  (1920, 1984, true, 9),
  (1984, 2016, true, 9),
  (2016, 2048, true, 9),
  (2048, 2112, false, 11),
  (2112, 2176, false, 10),
  (2176, 2240, false, 10),
  (2240, 2272, true, 8),
  (2272, 2304, true, 8),
  (2304, 2336, true, 8),
  (2336, 2368, true, 8),
  (2368, 2432, true, 8),
  (2432, 2496, true, 8),
  (2496, 2560, true, 8),
  (2560, 2624, true, 8),
  (2624, 2688, true, 7),
  (2688, 2752, true, 7),
  (2752, 2816, true, 7),
  (2816, 2944, true, 7),
  (2944, 3072, true, 7),
  (3072, 3200, true, 7),
  (3200, 3328, true, 7),
  (3328, 3456, true, 7),
  (3456, 3584, true, 7),
  (3584, 3712, true, 6),
  (3712, 3840, true, 6),
  (3840, 4096, true, 7),
  (4096, 4352, true, 7),
  (4352, 4608, false, 7),
  (4608, 4864, true, 7),
  (4864, 5120, true, 7),
  (5120, 5632, false, 7),
  (5632, 6144, false, 6),
  (6144, 6656, false, 6),
  (6656, 7168, false, 6),
  (7168, 7680, true, 6),
  (7680, 8192, true, 4),
  (8192, 10240, true, 4),
  (10240, 12288, true, 3),
  (12288, 16384, true, 3),
  (16384, 32768, true, 2)
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The kernel-checked finite certificate. -/
theorem certificate_checked :
    coverFrom (-32768) cells = true ∧ cells.all checkCell = true := by
  decide

/-! ## Interpretation of the certificate -/

lemma scale_div_16384 : (scale / 16384 : ℤ) = 17179869184 := by
  norm_num [scale]

lemma scale_div_64 : (scale / 64 : ℤ) = 4398046511104 := by
  norm_num [scale]

lemma memI_re {a b : ℤ} {x : ℝ} (h1 : (a : ℝ) ≤ 16384 * x) (h2 : 16384 * x ≤ (b : ℝ)) :
    MemI (a * (scale / 16384), b * (scale / 16384)) x := by
  rw [scale_div_16384]
  constructor <;> simp only [scale] <;> push_cast <;> nlinarith

lemma memI_im {x : ℝ} (h : x = 45 / 64) :
    MemI (45 * (scale / 64), 45 * (scale / 64)) x := by
  rw [scale_div_64, h]
  constructor <;> simp only [scale] <;> push_cast <;> norm_num

lemma memI_im_sub {x : ℝ} (h : x = 45 / 64 - 1) :
    MemI (45 * (scale / 64) - scale, 45 * (scale / 64) - scale) x := by
  rw [scale_div_64, h]
  constructor <;> simp only [scale] <;> push_cast <;> norm_num

/-- A verified row gives a finite escape statement for every real point of its
    interval, on the line `Im p = 45 / 64`. -/
lemma checkCell_sound {a b : ℤ} {par : Bool} {k : ℕ} (h : checkCell (a, b, par, k) = true)
    {p : ℂ} (h1 : (a : ℝ) ≤ 16384 * p.re) (h2 : 16384 * p.re ≤ (b : ℝ))
    (him : p.im = 45 / 64) :
    (∃ m : ℕ, m ≤ 16 ∧ 2 < ‖orbit p 0 m‖) ∨
      (∃ m : ℕ, m ≤ 15 ∧ 4 < ‖orbit Complex.I (p - Complex.I) m‖) := by
  have hx : MemI (a * (scale / 16384), b * (scale / 16384)) p.re := memI_re h1 h2
  cases par with
  | true =>
    simp only [checkCell, decide_eq_true_eq] at h
    obtain ⟨-, -, hk, hnorm⟩ := h
    refine Or.inl ⟨k, hk, ?_⟩
    have hp : MemB ((a * (scale / 16384), b * (scale / 16384)),
        (45 * (scale / 64), 45 * (scale / 64))) p := ⟨hx, memI_im him⟩
    have h0 : MemB (((0 : ℤ), (0 : ℤ)), ((0 : ℤ), (0 : ℤ))) (0 : ℂ) := by
      constructor <;> constructor <;> simp
    exact two_lt_norm (mem_iterateBox hp k h0) hnorm
  | false =>
    simp only [checkCell, decide_eq_true_eq] at h
    obtain ⟨-, -, hk, hnorm⟩ := h
    refine Or.inr ⟨k, hk, ?_⟩
    have hI : MemB (((0 : ℤ), (0 : ℤ)), (scale, scale)) Complex.I := by
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp [scale]
    have hstart : MemB ((a * (scale / 16384), b * (scale / 16384)),
        (45 * (scale / 64) - scale, 45 * (scale / 64) - scale)) (p - Complex.I) := by
      refine ⟨?_, ?_⟩
      · simpa using hx
      · exact memI_im_sub (by simp [him])
    exact four_lt_norm (mem_iterateBox hI k hstart) hnorm

/-- Coverage invariant: a point of `[A, 32768]` either equals `A` or lies in
    one of the listed rows. -/
lemma coverFrom_sound : ∀ (rows : List Cell) (A : ℤ), coverFrom A rows = true →
    ∀ t : ℝ, (A : ℝ) ≤ t → t ≤ 32768 →
      t = (A : ℝ) ∨ ∃ row ∈ rows, ((row.1 : ℤ) : ℝ) ≤ t ∧ t ≤ ((row.2.1 : ℤ) : ℝ) := by
  intro rows
  induction rows with
  | nil =>
    intro A h t h1 h2
    simp only [coverFrom, decide_eq_true_eq] at h
    subst h
    left
    push_cast at h1 h2 ⊢
    linarith
  | cons row tail ih =>
    obtain ⟨l, r, par, k⟩ := row
    intro A h t h1 h2
    simp only [coverFrom, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hA, hlr⟩, htail⟩ := h
    subst hA
    right
    rcases le_total t (r : ℝ) with hc | hc
    · exact ⟨(A, r, par, k), List.mem_cons_self .., h1, hc⟩
    · rcases ih r htail t hc h2 with heq | ⟨row', hrow', hb⟩
      · exact ⟨(A, r, par, k), List.mem_cons_self .., h1, le_of_eq heq⟩
      · exact ⟨row', List.mem_cons_of_mem _ hrow', hb⟩

lemma cover_cells {t : ℝ} (h1 : -32768 ≤ t) (h2 : t ≤ 32768) :
    ∃ row ∈ cells, ((row.1 : ℤ) : ℝ) ≤ t ∧ t ≤ ((row.2.1 : ℤ) : ℝ) := by
  rcases coverFrom_sound cells (-32768) certificate_checked.1 t (by push_cast; linarith) h2 with
    heq | hrow
  · refine ⟨(-32768, -24576, false, 2), ?_, ?_, ?_⟩
    · rw [cells]
      exact List.mem_cons_self ..
    · push_cast at heq ⊢
      linarith
    · push_cast at heq ⊢
      linarith
  · exact hrow

/-! ## The finite escape alternative on the separating line -/

/-- Lemma 4.1 of the reference: on the line `Im p = 45 / 64` with
    `|Re p| ≤ 2`, either the critical orbit of `p` escapes the disc of radius
    `2` within `16` steps, or the orbit of `p - i` under `z ↦ z ^ 2 + i`
    escapes the disc of radius `4` within `15` steps. -/
theorem escape_alternatives {p : ℂ} (hre : |p.re| ≤ 2) (him : p.im = 45 / 64) :
    (∃ m : ℕ, m ≤ 16 ∧ 2 < ‖orbit p 0 m‖) ∨
      (∃ m : ℕ, m ≤ 15 ∧ 4 < ‖orbit Complex.I (p - Complex.I) m‖) := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp hre
  obtain ⟨row, hrow, hl, hr⟩ :=
    cover_cells (t := 16384 * p.re) (by linarith) (by linarith)
  obtain ⟨a, b, par, k⟩ := row
  exact checkCell_sound (List.all_eq_true.mp certificate_checked.2 _ hrow) hl hr him

/-! ## Explicit orbits -/

/-- The critical cycle of the parameter `i` lives in an explicit four-point
    set, which is invariant under `z ↦ z ^ 2 + i`. -/
lemma orbit_I_stays (n : ℕ) : ∀ {z : ℂ},
    (z = 0 ∨ z = Complex.I ∨ z = -1 + Complex.I ∨ z = -Complex.I) →
    (orbit Complex.I z n = 0 ∨ orbit Complex.I z n = Complex.I ∨
      orbit Complex.I z n = -1 + Complex.I ∨ orbit Complex.I z n = -Complex.I) := by
  induction n with
  | zero => intro z hz; simpa [orbit] using hz
  | succ n ih =>
    intro z hz
    rw [orbit_succ_eq]
    refine ih ?_
    rcases hz with h | h | h | h <;> subst h
    · right; left; ring
    · right; right; left; linear_combination Complex.I_sq
    · right; right; right; linear_combination Complex.I_sq
    · right; right; left; linear_combination Complex.I_sq

lemma norm_le_two_of_cycle {z : ℂ}
    (hz : z = 0 ∨ z = Complex.I ∨ z = -1 + Complex.I ∨ z = -Complex.I) : ‖z‖ ≤ 2 := by
  rcases hz with h | h | h | h <;> subst h
  · simp
  · simp
  · have h := Complex.norm_le_abs_re_add_abs_im (-1 + Complex.I)
    norm_num at h
    linarith
  · simp

lemma boundedOrbit_I {z : ℂ}
    (hz : z = 0 ∨ z = Complex.I ∨ z = -1 + Complex.I ∨ z = -Complex.I) :
    boundedOrbit Complex.I z :=
  ⟨2, fun n => norm_le_two_of_cycle (orbit_I_stays n hz)⟩

lemma I_mem_mandelbrot : Complex.I ∈ MandelbrotSet := boundedOrbit_I (Or.inl rfl)

lemma zero_mem_K_I : (0 : ℂ) ∈ K Complex.I := boundedOrbit_I (Or.inl rfl)

lemma I_mem_K_I : Complex.I ∈ K Complex.I := boundedOrbit_I (Or.inr (Or.inl rfl))

lemma neg_I_mem_K_I : -Complex.I ∈ K Complex.I :=
  boundedOrbit_I (Or.inr (Or.inr (Or.inr rfl)))

lemma orbit_zero_zero (n : ℕ) : orbit (0 : ℂ) 0 n = 0 := by
  induction n with
  | zero => simp [orbit]
  | succ n ih => rw [orbit_succ, ih]; simp [fc]

lemma zero_mem_mandelbrot : (0 : ℂ) ∈ MandelbrotSet :=
  ⟨0, fun n => by rw [orbit_zero_zero]; simp⟩

lemma two_I_not_mem_mandelbrot : (2 * Complex.I) ∉ MandelbrotSet := by
  intro hmem
  rw [Molecule.mandelbrot_eq_inter] at hmem
  have h2 := Set.mem_iInter.mp hmem 2
  simp only [Set.mem_setOf_eq] at h2
  have horb : orbit (2 * Complex.I) 0 2 = -4 + 2 * Complex.I := by
    rw [orbit_succ_eq, orbit_succ_eq, orbit_zero]
    linear_combination (4 : ℂ) * Complex.I_sq
  rw [horb] at h2
  have hre := Complex.abs_re_le_norm (-4 + 2 * Complex.I)
  norm_num at hre
  linarith

lemma mandelbrot_orbit_le_two {p : ℂ} (hp : p ∈ MandelbrotSet) (n : ℕ) :
    ‖orbit p 0 n‖ ≤ 2 := by
  rw [Molecule.mandelbrot_eq_inter] at hp
  simpa using Set.mem_iInter.mp hp n

lemma mandelbrot_re_le_two {p : ℂ} (hp : p ∈ MandelbrotSet) : |p.re| ≤ 2 := by
  have hball := Molecule.mandelbrot_subset_ball hp
  rw [Metric.mem_closedBall, dist_zero_right] at hball
  exact le_trans (Complex.abs_re_le_norm p) hball

lemma green_zero_of_mem_K {z : ℂ} (hz : z ∈ K Complex.I) :
    green_function Complex.I z = 0 :=
  (green_function_eq_zero_iff_mem_K Complex.I z).mpr hz

/-! ## Analytic and topological helpers -/

/-- A set containing `0` and `i` but no point of the line `Im = 45 / 64` is
    disconnected. -/
theorem disconnected_of_horizontal_gap {S : Set ℂ}
    (h0 : (0 : ℂ) ∈ S) (hi : Complex.I ∈ S)
    (hgap : ∀ z ∈ S, z.im ≠ (45 / 64 : ℝ)) :
    ¬ IsConnected S := by
  intro hS
  have hm : (45 / 64 : ℝ) ∈ Set.Icc ((0 : ℂ).im) Complex.I.im := by
    norm_num
  obtain ⟨z, hz, heq⟩ := hS.isPreconnected.intermediate_value
    h0 hi Complex.continuous_im.continuousOn hm
  exact hgap z hz heq

/-- Corollary 3.3 of the reference: an escape past modulus `4` within `15`
    steps forces the Green value to exceed `2 ^ (-16)`. -/
theorem green_large_after_iterate {z : ℂ} {k : ℕ} (hk : k ≤ 15)
    (hesc : 4 < ‖orbit Complex.I z k‖) :
    (1 / 2 : ℝ) ^ 16 < green_function Complex.I z := by
  let w := orbit Complex.I z k
  have hbound : escape_bound Complex.I = 2 := by
    rw [escape_bound_eq_max]
    norm_num
  have hw : escape_bound Complex.I < ‖w‖ := by
    rw [hbound]
    dsimp [w]
    linarith
  have hlow := green_function_bdd_below_log Complex.I w hw
  rw [hbound] at hlow
  norm_num at hlow
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hlog4 : (1 : ℝ) < Real.log 4 := by
    have heq : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    linarith
  have hlogw : Real.log 4 < Real.log ‖w‖ :=
    Real.log_lt_log (by norm_num) hesc
  have hgreenw : (1 / 2 : ℝ) < green_function Complex.I w := by
    linarith
  have hiterate := green_function_iterate Complex.I z k
  have hpow : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ 15 :=
    pow_le_pow_right₀ (by norm_num) hk
  by_contra! hnot
  have hupper : (2 : ℝ) ^ k * green_function Complex.I z ≤ (1 / 2 : ℝ) := by
    calc
      (2 : ℝ) ^ k * green_function Complex.I z ≤
          (2 : ℝ) ^ k * (1 / 2 : ℝ) ^ 16 := by gcongr
      _ ≤ (2 : ℝ) ^ 15 * (1 / 2 : ℝ) ^ 16 := by gcongr
      _ = (1 / 2 : ℝ) := by norm_num
  dsimp [w] at hgreenw
  rw [hiterate] at hgreenw
  exact (not_lt_of_ge hupper) hgreenw

/-! ## The separating line misses the intersection -/

/-- Lemma 5.1 of the reference. -/
theorem green_gt_of_im_eq {p : ℂ} (hp : p ∈ MandelbrotSet) (him : p.im = 45 / 64) :
    (1 / 2 : ℝ) ^ 16 < green_function Complex.I (p - Complex.I) := by
  rcases escape_alternatives (mandelbrot_re_le_two hp) him with ⟨m, -, hgt⟩ | ⟨m, hm, hgt⟩
  · exact absurd (mandelbrot_orbit_le_two hp m) (by linarith)
  · exact green_large_after_iterate hm hgt

/-! ## The counterexample -/

/-- The set-theoretic parameter-connectivity datum is false: the witness is
    `c = i`, `n = 16`. -/
theorem not_greenSublevelIntersectionSetData :
    ¬ GreenSublevelIntersectionSetData := by
  intro hdata
  have hpos : (0 : ℝ) < (1 / 2 : ℝ) ^ 16 := by positivity
  have hA0 : green_function Complex.I ((0 : ℂ) - Complex.I) < (1 / 2 : ℝ) ^ 16 := by
    rw [show (0 : ℂ) - Complex.I = -Complex.I by ring, green_zero_of_mem_K neg_I_mem_K_I]
    exact hpos
  have hAI : green_function Complex.I (Complex.I - Complex.I) < (1 / 2 : ℝ) ^ 16 := by
    rw [show Complex.I - Complex.I = (0 : ℂ) by ring, green_zero_of_mem_K zero_mem_K_I]
    exact hpos
  have hA2I : green_function Complex.I (2 * Complex.I - Complex.I) < (1 / 2 : ℝ) ^ 16 := by
    rw [show 2 * Complex.I - Complex.I = Complex.I by ring, green_zero_of_mem_K I_mem_K_I]
    exact hpos
  have hstraddle :
      ¬ ({c' | green_function Complex.I (c' - Complex.I) < (1 / 2 : ℝ) ^ 16} ⊆ MandelbrotSet) :=
    fun hsub => two_I_not_mem_mandelbrot (hsub hA2I)
  have hconn := hdata Complex.I I_mem_mandelbrot 16 hstraddle
  refine disconnected_of_horizontal_gap
    (S := {c' | green_function Complex.I (c' - Complex.I) < (1 / 2 : ℝ) ^ 16} ∩ MandelbrotSet)
    ⟨hA0, zero_mem_mandelbrot⟩ ⟨hAI, I_mem_mandelbrot⟩ ?_ hconn
  rintro z ⟨hzA, hzM⟩ hzim
  exact absurd hzA (not_lt.mpr (le_of_lt (green_gt_of_im_eq hzM hzim)))

end MLC.GreenCounterexample

namespace MLC

/-- **The categorical Green-sublevel intersection datum is false.** Applying it
    to `c = i`, `n = 16` would force `{p | G_i(p - i) < 2⁻¹⁶} ∩ M` to be
    connected, while it contains `0` and `i` and misses the line
    `Im p = 45 / 64`. -/
theorem not_greenSublevelIntersectionCategoricalData :
    ¬ GreenSublevelIntersectionCategoricalData := fun hdata =>
  GreenCounterexample.not_greenSublevelIntersectionSetData
    (greenSublevelIntersectionCategoricalData_iff.mp hdata)

#print axioms GreenCounterexample.certificate_checked
#print axioms GreenCounterexample.escape_alternatives
#print axioms GreenCounterexample.not_greenSublevelIntersectionSetData
#print axioms not_greenSublevelIntersectionCategoricalData

end MLC
