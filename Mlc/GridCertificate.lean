import Mlc.MandelbrotCompact
import Mlc.GridDefs
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Fixed-point enclosures and the geometry of the grid

A ball `(a + b i, R) / 2^48` encloses the iterate `z_k(c)` of the critical orbit
for every parameter `c` in a disk (`Encl`); the escape test of a ball is sound
(`escaped_sound`). The file also contains the facts about dyadic squares (their
point sets, areas and subdivisions), the boundedness of an orbit that returns
into an invariant set, the conjugation symmetry of the set `Unresolved` of
parameters of `M` that are not interior points, and the cover of its upper half
by the root squares. The certificates themselves are in `Mlc.GridTMCertificate`.
-/

namespace MLC.Certified

open Complex MLC.Quadratic MeasureTheory ComplexConjugate

lemma SN_pos : (0 : ℝ) < SN := by unfold SN; norm_num

/-- The Gaussian fixed-point number `(a + b i) / 2^48`. -/
noncomputable def fx (a b : ℤ) : ℂ := ⟨(a : ℝ) / SN, (b : ℝ) / SN⟩

lemma normUB_sq (a b : ℤ) : a * a + b * b ≤ (normUB a b : ℤ) * (normUB a b : ℤ) := by
  have habs : ((a.natAbs * a.natAbs + b.natAbs * b.natAbs : ℕ) : ℤ) = a * a + b * b := by
    push_cast
    rw [abs_mul_abs_self, abs_mul_abs_self]
  unfold normUB normAux normPick
  split_ifs with h
  · rw [← habs]
    exact_mod_cast h
  · have : a.natAbs * a.natAbs + b.natAbs * b.natAbs ≤
        (a.natAbs + b.natAbs) * (a.natAbs + b.natAbs) := by
      nlinarith [Nat.zero_le (a.natAbs * b.natAbs)]
    rw [← habs]
    exact_mod_cast this

/-- The enclosure `m` bounds the `k`-th critical iterate for all parameters
within `r` of `c₀`. -/
def Encl (c₀ : ℂ) (r : ℝ) (k : ℕ) (m : Ball) : Prop :=
  ∀ c : ℂ, ‖c - c₀‖ ≤ r → ‖orbit c 0 k - fx m.a m.b‖ ≤ (m.R : ℝ) / SN

lemma norm_le_of_sq {z : ℂ} {B : ℝ} (hB : 0 ≤ B)
    (h : z.re ^ 2 + z.im ^ 2 ≤ B ^ 2) : ‖z‖ ≤ B := by
  have h2 : ‖z‖ ^ 2 ≤ B ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    nlinarith
  by_contra hlt
  push_neg at hlt
  nlinarith [norm_nonneg z]

lemma fx_norm_le {a b : ℤ} {N : ℕ} (h : a * a + b * b ≤ (N : ℤ) * (N : ℤ)) :
    ‖fx a b‖ ≤ (N : ℝ) / SN := by
  apply norm_le_of_sq (div_nonneg (Nat.cast_nonneg _) SN_pos.le)
  have hR : (a : ℝ) * a + (b : ℝ) * b ≤ (N : ℝ) * N := by exact_mod_cast h
  have hS := SN_pos
  simp only [fx]
  rw [div_pow, div_pow, div_pow, ← add_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  nlinarith

lemma round_step (a b ca cb : ℤ) :
    ‖fx ((a * a - b * b) / (SN : ℤ) + ca) ((2 * a * b) / (SN : ℤ) + cb)
        - ((fx a b) ^ 2 + fx ca cb)‖ ≤ 2 / SN := by
  have hS := SN_pos
  have hSz : (0 : ℤ) < SN := by unfold SN; norm_num
  have h1 := Int.mul_ediv_add_emod (a * a - b * b) (SN : ℤ)
  have h2 := Int.mul_ediv_add_emod (2 * a * b) (SN : ℤ)
  have e1 := Int.emod_nonneg (a * a - b * b) hSz.ne'
  have e1' := Int.emod_lt_of_pos (a * a - b * b) hSz
  have e2 := Int.emod_nonneg (2 * a * b) hSz.ne'
  have e2' := Int.emod_lt_of_pos (2 * a * b) hSz
  generalize (a * a - b * b) / (SN : ℤ) = q1 at *
  generalize (a * a - b * b) % (SN : ℤ) = r1 at *
  generalize (2 * a * b) / (SN : ℤ) = q2 at *
  generalize (2 * a * b) % (SN : ℤ) = r2 at *
  have h1r : (SN : ℝ) * (q1 : ℝ) + (r1 : ℝ) = (a : ℝ) * a - (b : ℝ) * b := by
    exact_mod_cast h1
  have h2r : (SN : ℝ) * (q2 : ℝ) + (r2 : ℝ) = 2 * (a : ℝ) * b := by
    exact_mod_cast h2
  have e1r : (0 : ℝ) ≤ r1 := by exact_mod_cast e1
  have e1r' : (r1 : ℝ) < SN := by exact_mod_cast e1'
  have e2r : (0 : ℝ) ≤ r2 := by exact_mod_cast e2
  have e2r' : (r2 : ℝ) < SN := by exact_mod_cast e2'
  have hre : (fx (q1 + ca) (q2 + cb) - ((fx a b) ^ 2 + fx ca cb)).re
      = -((r1 : ℝ) / (SN : ℝ) ^ 2) := by
    simp only [fx, pow_two, Complex.sub_re, Complex.add_re, Complex.mul_re]
    push_cast
    field_simp
    linear_combination h1r
  have him : (fx (q1 + ca) (q2 + cb) - ((fx a b) ^ 2 + fx ca cb)).im
      = -((r2 : ℝ) / (SN : ℝ) ^ 2) := by
    simp only [fx, pow_two, Complex.sub_im, Complex.add_im, Complex.mul_im]
    push_cast
    field_simp
    linear_combination h2r
  have hb : ∀ r : ℝ, 0 ≤ r → r < SN → |-(r / (SN : ℝ) ^ 2)| ≤ 1 / SN := by
    intro r hr hr'
    rw [abs_neg, abs_of_nonneg (by positivity), div_le_div_iff₀ (by positivity) hS]
    nlinarith
  calc _ ≤ |(fx (q1 + ca) (q2 + cb) - ((fx a b) ^ 2 + fx ca cb)).re| +
        |(fx (q1 + ca) (q2 + cb) - ((fx a b) ^ 2 + fx ca cb)).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ ≤ 1 / SN + 1 / SN := by
        rw [hre, him]
        exact add_le_add (hb _ e1r e1r') (hb _ e2r e2r')
    _ = 2 / SN := by ring

lemma fx_zero : fx 0 0 = 0 := by
  apply Complex.ext <;> simp [fx]

lemma escaped_sound {c₀ : ℂ} {r : ℝ} {k : ℕ} {m : Ball} (hE : Encl c₀ r k m)
    (h : escaped m = true) {c : ℂ} (hc : ‖c - c₀‖ ≤ r) : 2 < ‖orbit c 0 k‖ := by
  have hS := SN_pos
  have hlt : (2 * SN + m.R) ^ 2 < m.a.natAbs ^ 2 + m.b.natAbs ^ 2 := by
    simpa [escaped] using h
  have hlt' : ((2 * SN + m.R : ℕ) : ℝ) ^ 2 < (m.a : ℝ) ^ 2 + (m.b : ℝ) ^ 2 := by
    have h1 : (((2 * SN + m.R) ^ 2 : ℕ) : ℤ) <
        ((m.a.natAbs ^ 2 + m.b.natAbs ^ 2 : ℕ) : ℤ) := by exact_mod_cast hlt
    push_cast at h1
    rw [sq_abs, sq_abs] at h1
    exact_mod_cast h1
  have hnorm : 2 + (m.R : ℝ) / SN < ‖fx m.a m.b‖ := by
    by_contra hcon
    push_neg at hcon
    have h2 : ‖fx m.a m.b‖ ^ 2 ≤ (2 + (m.R : ℝ) / SN) ^ 2 := by
      have := norm_nonneg (fx m.a m.b)
      nlinarith
    rw [Complex.sq_norm, Complex.normSq_apply] at h2
    simp only [fx] at h2
    have e : (2 + (m.R : ℝ) / SN) = (2 * SN + m.R) / SN := by field_simp
    rw [e, div_pow] at h2
    have h3 : ((m.a : ℝ) / SN) * ((m.a : ℝ) / SN) + ((m.b : ℝ) / SN) * ((m.b : ℝ) / SN) =
        ((m.a : ℝ) ^ 2 + (m.b : ℝ) ^ 2) / (SN : ℝ) ^ 2 := by field_simp
    rw [h3, div_le_div_iff_of_pos_right (by positivity)] at h2
    push_cast at hlt'
    linarith
  have hz := hE c hc
  have h3 : ‖fx m.a m.b‖ - ‖orbit c 0 k‖ ≤ (m.R : ℝ) / SN := by
    calc _ ≤ ‖fx m.a m.b - orbit c 0 k‖ := norm_sub_norm_le _ _
      _ = ‖orbit c 0 k - fx m.a m.b‖ := norm_sub_rev _ _
      _ ≤ _ := hz
  linarith

lemma fx_sub (a b a' b' : ℤ) : fx a b - fx a' b' = fx (a - a') (b - b') := by
  apply Complex.ext <;> simp [fx, sub_div]

/-- The point set of a dyadic square. -/
def Sq.set (q : Sq) : Set ℂ :=
  {c | (q.x : ℝ) / 2 ^ q.k ≤ c.re ∧ c.re ≤ ((q.x : ℝ) + 1) / 2 ^ q.k ∧
    (q.y : ℝ) / 2 ^ q.k ≤ c.im ∧ c.im ≤ ((q.y : ℝ) + 1) / 2 ^ q.k}

lemma two_pow_scale {k : ℕ} (hk : k ≤ 47) :
    ((2 : ℝ) ^ (47 - k)) * 2 ^ (k + 1) = SN := by
  rw [← pow_add]
  have : 47 - k + (k + 1) = 48 := by omega
  rw [this]
  unfold SN
  norm_num

lemma Sq.set_subset_disk (q : Sq) (hk : q.k ≤ 47) {c : ℂ} (hc : c ∈ q.set) :
    ‖c - fx q.ca q.cb‖ ≤ (q.rc : ℝ) / SN := by
  have hS := SN_pos
  have hscale := two_pow_scale hk
  have hp : (0 : ℝ) < 2 ^ (q.k + 1) := by positivity
  have hh : ((2 : ℝ) ^ (47 - q.k)) / SN = 1 / 2 ^ (q.k + 1) := by
    rw [div_eq_div_iff hS.ne' hp.ne']
    linarith
  have hrc : (2 : ℝ) ^ (47 - q.k) * 363 / 256 ≤ (q.rc : ℝ) := by
    have h3 : 2 ^ (47 - q.k) * 363 ≤ 256 * q.rc := by unfold Sq.rc; omega
    have h4 : ((2 ^ (47 - q.k) * 363 : ℕ) : ℝ) ≤ ((256 * q.rc : ℕ) : ℝ) := by
      exact_mod_cast h3
    push_cast at h4
    linarith
  set s : ℝ := 1 / 2 ^ (q.k + 1) with hsdef
  have hs0 : 0 < s := by positivity
  have hcre : (fx q.ca q.cb).re = (2 * (q.x : ℝ) + 1) * s := by
    simp only [fx, Sq.ca]
    push_cast
    rw [mul_div_assoc, hh]
  have hcim : (fx q.ca q.cb).im = (2 * (q.y : ℝ) + 1) * s := by
    simp only [fx, Sq.cb]
    push_cast
    rw [mul_div_assoc, hh]
  have ex : ∀ t : ℝ, t / 2 ^ q.k = 2 * t * s := by
    intro t
    rw [hsdef, pow_succ]
    field_simp
  obtain ⟨h1, h2, h3, h4⟩ := hc
  rw [ex] at h1 h2 h3 h4
  have hre : |c.re - (fx q.ca q.cb).re| ≤ s := by
    rw [hcre, abs_le]
    constructor <;> nlinarith
  have him : |c.im - (fx q.ca q.cb).im| ≤ s := by
    rw [hcim, abs_le]
    constructor <;> nlinarith
  have hr : s * (363 / 256) ≤ (q.rc : ℝ) / SN := by
    rw [le_div_iff₀ hS]
    have : (2 : ℝ) ^ (47 - q.k) = s * SN := by
      rw [← hh]
      field_simp
    nlinarith
  have hsq : 2 * s ^ 2 ≤ ((q.rc : ℝ) / SN) ^ 2 := by
    have h0 : 0 ≤ s * (363 / 256) := by positivity
    nlinarith
  apply norm_le_of_sq (by positivity)
  simp only [Complex.sub_re, Complex.sub_im]
  have e1 : (c.re - (fx q.ca q.cb).re) ^ 2 ≤ s ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hre 2
  have e2 : (c.im - (fx q.ca q.cb).im) ^ 2 ≤ s ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) him 2
  linarith

lemma Sq.mem_iff (q : Sq) (c : ℂ) : c ∈ q.set ↔
    (q.x : ℝ) ≤ c.re * 2 ^ q.k ∧ c.re * 2 ^ q.k ≤ q.x + 1 ∧
    (q.y : ℝ) ≤ c.im * 2 ^ q.k ∧ c.im * 2 ^ q.k ≤ q.y + 1 := by
  have hp : (0 : ℝ) < 2 ^ q.k := by positivity
  simp only [Sq.set, Set.mem_setOf_eq, div_le_iff₀ hp, le_div_iff₀ hp]

lemma Sq.volume_set (q : Sq) : volume q.set = ENNReal.ofReal (1 / 4 ^ q.k) := by
  have hp : (0 : ℝ) < 2 ^ q.k := by positivity
  have hset : q.set = Complex.measurableEquivRealProd ⁻¹'
      (Set.Icc ((q.x : ℝ) / 2 ^ q.k) (((q.x : ℝ) + 1) / 2 ^ q.k) ×ˢ
        Set.Icc ((q.y : ℝ) / 2 ^ q.k) (((q.y : ℝ) + 1) / 2 ^ q.k)) := by
    ext c
    simp only [Sq.set, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_prod, Set.mem_Icc,
      Complex.measurableEquivRealProd_apply, and_assoc]
  rw [hset, Complex.volume_preserving_equiv_real_prod.measure_preimage
    ((measurableSet_Icc.prod measurableSet_Icc).nullMeasurableSet),
    Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, Real.volume_Icc,
    ← ENNReal.ofReal_mul (by
      have : (0 : ℝ) ≤ 1 / 2 ^ q.k := by positivity
      convert this using 1
      field_simp
      ring)]
  congr 1
  have h4 : (4 : ℝ) ^ q.k = 2 ^ q.k * 2 ^ q.k := by
    rw [← mul_pow]; norm_num
  rw [h4]
  field_simp
  ring

lemma Sq.subset_children (q : Sq) :
    q.set ⊆ q.c00.set ∪ q.c10.set ∪ q.c01.set ∪ q.c11.set := by
  intro c hc
  rw [Sq.mem_iff] at hc
  obtain ⟨h1, h2, h3, h4⟩ := hc
  have hp : (2 : ℝ) ^ (q.k + 1) = 2 * 2 ^ q.k := by rw [pow_succ]; ring
  simp only [Set.mem_union, Sq.c00, Sq.c10, Sq.c01, Sq.c11, Sq.mem_iff, hp]
  push_cast
  rcases le_total (c.re * 2 ^ q.k) (q.x + 1 / 2) with hu | hu <;>
  rcases le_total (c.im * 2 ^ q.k) (q.y + 1 / 2) with hv | hv
  · left; left; left; refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith
  · left; right; refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith
  · left; left; right; refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith
  · right; refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith

/-- The interior of a dyadic square. -/
def Sq.openSet (q : Sq) : Set ℂ :=
  {c | (q.x : ℝ) / 2 ^ q.k < c.re ∧ c.re < ((q.x : ℝ) + 1) / 2 ^ q.k ∧
    (q.y : ℝ) / 2 ^ q.k < c.im ∧ c.im < ((q.y : ℝ) + 1) / 2 ^ q.k}

lemma Sq.openSet_subset (q : Sq) : q.openSet ⊆ q.set := by
  intro c ⟨h1, h2, h3, h4⟩
  exact ⟨h1.le, h2.le, h3.le, h4.le⟩

lemma Sq.isOpen_openSet (q : Sq) : IsOpen q.openSet := by
  have h1 : IsOpen {c : ℂ | (q.x : ℝ) / 2 ^ q.k < c.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have h2 : IsOpen {c : ℂ | c.re < ((q.x : ℝ) + 1) / 2 ^ q.k} :=
    isOpen_lt Complex.continuous_re continuous_const
  have h3 : IsOpen {c : ℂ | (q.y : ℝ) / 2 ^ q.k < c.im} :=
    isOpen_lt continuous_const Complex.continuous_im
  have h4 : IsOpen {c : ℂ | c.im < ((q.y : ℝ) + 1) / 2 ^ q.k} :=
    isOpen_lt Complex.continuous_im continuous_const
  have : q.openSet = {c : ℂ | (q.x : ℝ) / 2 ^ q.k < c.re} ∩
      ({c : ℂ | c.re < ((q.x : ℝ) + 1) / 2 ^ q.k} ∩
        ({c : ℂ | (q.y : ℝ) / 2 ^ q.k < c.im} ∩
          {c : ℂ | c.im < ((q.y : ℝ) + 1) / 2 ^ q.k})) := by
    ext c; simp [Sq.openSet]
  rw [this]
  exact h1.inter (h2.inter (h3.inter h4))

lemma Sq.volume_openSet (q : Sq) : volume q.openSet = ENNReal.ofReal (1 / 4 ^ q.k) := by
  have hp : (0 : ℝ) < 2 ^ q.k := by positivity
  have hset : q.openSet = Complex.measurableEquivRealProd ⁻¹'
      (Set.Ioo ((q.x : ℝ) / 2 ^ q.k) (((q.x : ℝ) + 1) / 2 ^ q.k) ×ˢ
        Set.Ioo ((q.y : ℝ) / 2 ^ q.k) (((q.y : ℝ) + 1) / 2 ^ q.k)) := by
    ext c
    simp only [Sq.openSet, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_prod, Set.mem_Ioo,
      Complex.measurableEquivRealProd_apply, and_assoc]
  rw [hset, Complex.volume_preserving_equiv_real_prod.measure_preimage
    ((measurableSet_Ioo.prod measurableSet_Ioo).nullMeasurableSet),
    Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioo, Real.volume_Ioo,
    ← ENNReal.ofReal_mul (by
      have : (0 : ℝ) ≤ 1 / 2 ^ q.k := by positivity
      convert this using 1
      field_simp
      ring)]
  congr 1
  have h4 : (4 : ℝ) ^ q.k = 2 ^ q.k * 2 ^ q.k := by
    rw [← mul_pow]; norm_num
  rw [h4]
  field_simp
  ring

lemma Sq.volume_boundary (q : Sq) : volume (q.set \ q.openSet) = 0 := by
  rw [measure_diff q.openSet_subset q.isOpen_openSet.measurableSet.nullMeasurableSet
    (by rw [Sq.volume_openSet]; exact ENNReal.ofReal_ne_top),
    Sq.volume_set, Sq.volume_openSet, tsub_self]

lemma iterate_bounded_of_trap {f : ℂ → ℂ} {D : Set ℂ} {p : ℕ} {B : ℝ} (hp : 1 ≤ p)
    (hD : ∀ z ∈ D, f^[p] z ∈ D) (hB : ∀ z ∈ D, ∀ k, k ≤ p → ‖f^[k] z‖ ≤ B)
    {z : ℂ} (hz : z ∈ D) : ∀ k, ‖f^[k] z‖ ≤ B := by
  intro k
  have hmem : ∀ t : ℕ, (f^[p])^[t] z ∈ D := by
    intro t
    induction t with
    | zero => simpa using hz
    | succ t ih => rw [Function.iterate_succ_apply']; exact hD _ ih
  have hk : k = k % p + p * (k / p) := (Nat.mod_add_div k p).symm
  have hpos : 0 < p := hp
  have : f^[k] z = f^[k % p] ((f^[p])^[k / p] z) := by
    conv_lhs => rw [hk]
    rw [Function.iterate_add_apply, Function.iterate_mul]
  rw [this]
  exact hB _ (hmem _) _ (Nat.mod_lt k hpos).le

lemma exists_tile_index (n : ℕ) (hn : 1 ≤ n) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ n) :
    ∃ i : ℕ, i < n ∧ (i : ℝ) ≤ t ∧ t ≤ i + 1 := by
  by_cases h : ⌊t⌋₊ < n
  · exact ⟨⌊t⌋₊, h, Nat.floor_le h0, (Nat.lt_floor_add_one t).le⟩
  · push_neg at h
    refine ⟨n - 1, by omega, ?_, ?_⟩
    · have : (n : ℝ) ≤ ⌊t⌋₊ := by exact_mod_cast h
      have := Nat.floor_le h0
      have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
        rw [Nat.cast_sub hn]; simp
      rw [hcast]; linarith
    · have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
        rw [Nat.cast_sub hn]; simp
      rw [hcast]; linarith

/-- Parameters of `M` that are not interior points. -/
def Unresolved : Set ℂ := MandelbrotSet \ interior MandelbrotSet

lemma orbit_conj (c : ℂ) (n : ℕ) : orbit (conj c) 0 n = conj (orbit c 0 n) := by
  induction n with
  | zero => simp
  | succ n ih => rw [orbit_succ, orbit_succ, ih]; simp [fc]

lemma mem_mandelbrot_conj {c : ℂ} (h : c ∈ MandelbrotSet) : conj c ∈ MandelbrotSet := by
  obtain ⟨B, hB⟩ := h
  refine ⟨B, fun n => ?_⟩
  rw [orbit_conj, Complex.norm_conj]
  exact hB n

lemma conj_preimage_mandelbrot : conj ⁻¹' MandelbrotSet = MandelbrotSet := by
  ext c
  exact ⟨fun h => by simpa using mem_mandelbrot_conj h, fun h => mem_mandelbrot_conj h⟩

lemma conj_preimage_interior : conj ⁻¹' interior MandelbrotSet = interior MandelbrotSet := by
  have h := (Complex.conjCLE.toHomeomorph).preimage_interior MandelbrotSet
  have e : (⇑Complex.conjCLE.toHomeomorph) ⁻¹' MandelbrotSet = MandelbrotSet := conj_preimage_mandelbrot
  rw [e] at h
  exact h

lemma conj_preimage_unresolved : conj ⁻¹' Unresolved = Unresolved := by
  simp only [Unresolved, Set.preimage_diff, conj_preimage_mandelbrot, conj_preimage_interior]

lemma volume_conj_preimage (S : Set ℂ) (hS : MeasurableSet S) : volume (conj ⁻¹' S) = volume S :=
  (Complex.conjLIE.measurePreserving).measure_preimage hS.nullMeasurableSet

lemma Sq.measurableSet (q : Sq) : MeasurableSet q.set := by
  have : q.set = {c : ℂ | (q.x : ℝ) / 2 ^ q.k ≤ c.re} ∩
      ({c : ℂ | c.re ≤ ((q.x : ℝ) + 1) / 2 ^ q.k} ∩
        ({c : ℂ | (q.y : ℝ) / 2 ^ q.k ≤ c.im} ∩ {c : ℂ | c.im ≤ ((q.y : ℝ) + 1) / 2 ^ q.k})) := by
    ext c; simp [Sq.set]
  rw [this]
  refine (isClosed_le continuous_const Complex.continuous_re).measurableSet.inter
    ((isClosed_le Complex.continuous_re continuous_const).measurableSet.inter
      ((isClosed_le continuous_const Complex.continuous_im).measurableSet.inter
        (isClosed_le Complex.continuous_im continuous_const).measurableSet))

lemma measurableSet_unresolved : MeasurableSet Unresolved :=
  isClosed_mandelbrot.measurableSet.diff isOpen_interior.measurableSet

lemma unresolved_up_subset :
    Unresolved ∩ {c : ℂ | 0 ≤ c.im} ⊆ ⋃ q ∈ rootsUp, q.set := by
  intro c ⟨hU, him0⟩
  have hb := mandelbrot_subset_closedBall hU.1
  rw [Metric.mem_closedBall, dist_zero_right] at hb
  have hre := (Complex.abs_re_le_norm c).trans hb
  have him := (Complex.abs_im_le_norm c).trans hb
  rw [abs_le] at hre him
  have him0' : 0 ≤ c.im := him0
  obtain ⟨i, hi, hi1, hi2⟩ := exists_tile_index 32 (by norm_num) (t := (c.re + 2) * 8)
    (by nlinarith [hre.1]) (by push_cast; nlinarith [hre.2])
  obtain ⟨j, hj, hj1, hj2⟩ := exists_tile_index 16 (by norm_num) (t := c.im * 8)
    (by nlinarith) (by push_cast; nlinarith [him.2])
  simp only [Set.mem_iUnion, exists_prop]
  refine ⟨⟨(i : ℤ) - 16, (j : ℤ), 3⟩, ?_, ?_⟩
  · simp only [rootsUp, List.mem_flatMap, List.mem_map, List.mem_range]
    exact ⟨(i : ℤ) - 16, ⟨i, hi, rfl⟩, (j : ℤ), ⟨j, hj, rfl⟩, rfl⟩
  · rw [Sq.mem_iff]
    push_cast
    refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith

end MLC.Certified
