import Mlc.MandelbrotCompact
import Mlc.GridDefs
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Fixed-point ball arithmetic for critical orbits

A ball `(a + b i, R) / 2^48` encloses the iterate `z_k(c)` of the critical
orbit for every parameter `c` in a disk. The update rule is checked by
kernel reduction on integers and justified here for complex numbers.
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

lemma ball_step {z m c c₀ : ℂ} {ρ r N : ℝ} (hz : ‖z - m‖ ≤ ρ)
    (hc : ‖c - c₀‖ ≤ r) (hm : ‖m‖ ≤ N) :
    ‖(z ^ 2 + c) - (m ^ 2 + c₀)‖ ≤ ρ * (ρ + 2 * N) + r := by
  have h1 : (z ^ 2 + c) - (m ^ 2 + c₀) = (z - m) * ((z - m) + 2 * m) + (c - c₀) := by
    ring
  rw [h1]
  have h2 : ‖(z - m) + 2 * m‖ ≤ ρ + 2 * N := by
    calc ‖(z - m) + 2 * m‖ ≤ ‖z - m‖ + ‖2 * m‖ := norm_add_le _ _
      _ ≤ ρ + 2 * N := by
        rw [norm_mul]
        have : ‖(2 : ℂ)‖ = 2 := by simp
        rw [this]
        linarith
  have h3 : ‖(z - m) * ((z - m) + 2 * m)‖ ≤ ρ * (ρ + 2 * N) := by
    rw [norm_mul]
    exact mul_le_mul hz h2 (norm_nonneg _) ((norm_nonneg _).trans hz)
  calc _ ≤ ‖(z - m) * ((z - m) + 2 * m)‖ + ‖c - c₀‖ := norm_add_le _ _
    _ ≤ ρ * (ρ + 2 * N) + r := by linarith

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

lemma encl_zero (c₀ : ℂ) (r : ℝ) : Encl c₀ r 0 ⟨0, 0, 0⟩ := by
  intro c _
  simp [fx_zero]

lemma step_enclosure {ca cb : ℤ} {rc : ℕ} {m : Ball} {r : ℕ} {c z : ℂ}
    (hc : ‖c - fx ca cb‖ ≤ (rc : ℝ) / SN) (hz : ‖z - fx m.a m.b‖ ≤ (r : ℝ) / SN) :
    ‖(z ^ 2 + c) - fx (stepBall ca cb rc m).a (stepBall ca cb rc m).b‖ ≤
      (stepR rc m r : ℝ) / SN := by
  have hS := SN_pos
  have hN := fx_norm_le (normUB_sq m.a m.b)
  have hball := ball_step hz hc hN
  have hround := round_step m.a m.b ca cb
  have hdiv : r * (r + 2 * normUB m.a m.b) ≤
      SN * ((r * (r + 2 * normUB m.a m.b) + (SN - 1)) / SN) := by
    have hpos : 0 < SN := by unfold SN; norm_num
    have := Nat.div_add_mod (r * (r + 2 * normUB m.a m.b) + (SN - 1)) SN
    have hmod := Nat.mod_lt (r * (r + 2 * normUB m.a m.b) + (SN - 1)) hpos
    omega
  have hdivR : ((r : ℝ) * (r + 2 * (normUB m.a m.b : ℝ))) ≤
      SN * (((r * (r + 2 * normUB m.a m.b) + (SN - 1)) / SN : ℕ) : ℝ) := by
    exact_mod_cast hdiv
  have hfirst : (r : ℝ) / SN * ((r : ℝ) / SN + 2 * ((normUB m.a m.b : ℝ) / SN)) ≤
      (((r * (r + 2 * normUB m.a m.b) + (SN - 1)) / SN : ℕ) : ℝ) / SN := by
    rw [show (r : ℝ) / SN * ((r : ℝ) / SN + 2 * ((normUB m.a m.b : ℝ) / SN)) =
        ((r : ℝ) * (r + 2 * (normUB m.a m.b : ℝ))) / SN / SN by field_simp]
    rw [div_div, div_le_div_iff₀ (by positivity) hS]
    nlinarith [hdivR]
  calc ‖(z ^ 2 + c) - fx (stepBall ca cb rc m).a (stepBall ca cb rc m).b‖
      ≤ ‖(z ^ 2 + c) - ((fx m.a m.b) ^ 2 + fx ca cb)‖ +
        ‖((fx m.a m.b) ^ 2 + fx ca cb) - fx (stepBall ca cb rc m).a (stepBall ca cb rc m).b‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ((r : ℝ) / SN * ((r : ℝ) / SN + 2 * ((normUB m.a m.b : ℝ) / SN)) +
          (rc : ℝ) / SN) + 2 / SN := by
        refine add_le_add hball ?_
        rw [norm_sub_rev]
        exact hround
    _ ≤ (((r * (r + 2 * normUB m.a m.b) + (SN - 1)) / SN : ℕ) : ℝ) / SN +
          (rc : ℝ) / SN + 2 / SN := by linarith
    _ = (stepR rc m r : ℝ) / SN := by
        simp only [stepR]
        push_cast
        ring

lemma encl_step {ca cb : ℤ} {rc : ℕ} {k : ℕ} {m : Ball}
    (h : Encl (fx ca cb) ((rc : ℝ) / SN) k m) :
    Encl (fx ca cb) ((rc : ℝ) / SN) (k + 1) (stepBall ca cb rc m) := by
  intro c hc
  have horbit : orbit c 0 (k + 1) = (orbit c 0 k) ^ 2 + c := by
    rw [orbit_succ]; rfl
  rw [horbit]
  exact step_enclosure hc (h c hc)

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

lemma trapScan_sound {ca cb : ℤ} {rc : ℕ} {m0 : Ball} {Rhat : ℕ} :
    ∀ (n i : ℕ) (m : Ball) (rhat : ℕ) (B : ℝ), 0 ≤ B →
      (∀ c : ℂ, ‖c - fx ca cb‖ ≤ (rc : ℝ) / SN → ∀ z : ℂ,
        ‖z - fx m0.a m0.b‖ ≤ (Rhat : ℝ) / SN →
        ‖(fc c)^[i] z - fx m.a m.b‖ ≤ (rhat : ℝ) / SN ∧
          ∀ k, k ≤ i → ‖(fc c)^[k] z‖ ≤ B) →
      trapScan ca cb rc m0 Rhat n m rhat = true →
      ∃ p : ℕ, ∃ B' : ℝ, 1 ≤ p ∧ ∀ c : ℂ, ‖c - fx ca cb‖ ≤ (rc : ℝ) / SN →
        ∀ z : ℂ, ‖z - fx m0.a m0.b‖ ≤ (Rhat : ℝ) / SN →
          ‖(fc c)^[p] z - fx m0.a m0.b‖ ≤ (Rhat : ℝ) / SN ∧
            ∀ k, k ≤ p → ‖(fc c)^[k] z‖ ≤ B' := by
  intro n
  induction n with
  | zero => intro i m rhat B _ _ h; simp [trapScan] at h
  | succ n ih =>
      intro i m rhat B hB hinv h
      have hS := SN_pos
      set m' := stepBall ca cb rc m with hm'
      set rhat' := stepR rc m rhat with hrhat'
      set B' : ℝ := B + (((normUB m'.a m'.b : ℕ) : ℝ) + (rhat' : ℝ)) / SN with hB'
      have hB'0 : 0 ≤ B' := by positivity
      have hinv' : ∀ c : ℂ, ‖c - fx ca cb‖ ≤ (rc : ℝ) / SN → ∀ z : ℂ,
          ‖z - fx m0.a m0.b‖ ≤ (Rhat : ℝ) / SN →
          ‖(fc c)^[i + 1] z - fx m'.a m'.b‖ ≤ (rhat' : ℝ) / SN ∧
            ∀ k, k ≤ i + 1 → ‖(fc c)^[k] z‖ ≤ B' := by
        intro c hc z hz
        obtain ⟨h1, h2⟩ := hinv c hc z hz
        have hit : (fc c)^[i + 1] z = ((fc c)^[i] z) ^ 2 + c := by
          rw [Function.iterate_succ_apply']; rfl
        have hnew : ‖(fc c)^[i + 1] z - fx m'.a m'.b‖ ≤ (rhat' : ℝ) / SN := by
          rw [hit]; exact step_enclosure hc h1
        refine ⟨hnew, ?_⟩
        intro k hk
        rcases Nat.lt_or_ge k (i + 1) with hlt | hge
        · have := h2 k (by omega)
          have hpos : 0 ≤ (((normUB m'.a m'.b : ℕ) : ℝ) + (rhat' : ℝ)) / SN := by positivity
          linarith
        · have hk' : k = i + 1 := by omega
          subst hk'
          have hfx := fx_norm_le (normUB_sq m'.a m'.b)
          have : ‖(fc c)^[i + 1] z‖ ≤ ‖fx m'.a m'.b‖ + (rhat' : ℝ) / SN := by
            calc ‖(fc c)^[i + 1] z‖ = ‖((fc c)^[i + 1] z - fx m'.a m'.b) + fx m'.a m'.b‖ := by
                  congr 1; ring
              _ ≤ ‖(fc c)^[i + 1] z - fx m'.a m'.b‖ + ‖fx m'.a m'.b‖ := norm_add_le _ _
              _ ≤ _ := by linarith
          have e : (((normUB m'.a m'.b : ℕ) : ℝ) + (rhat' : ℝ)) / SN =
              ((normUB m'.a m'.b : ℕ) : ℝ) / SN + (rhat' : ℝ) / SN := by ring
          have hB0 : 0 ≤ B := hB
          linarith
      have hdef : trapScan ca cb rc m0 Rhat (n + 1) m rhat =
          if normUB (m'.a - m0.a) (m'.b - m0.b) + rhat' ≤ Rhat then true
          else if 8 * SN < rhat' then false
          else trapScan ca cb rc m0 Rhat n m' rhat' := rfl
      rw [hdef] at h
      by_cases h1 : normUB (m'.a - m0.a) (m'.b - m0.b) + rhat' ≤ Rhat
      · refine ⟨i + 1, B', by omega, ?_⟩
        intro c hc z hz
        obtain ⟨hn, hb⟩ := hinv' c hc z hz
        refine ⟨?_, hb⟩
        have hd := fx_norm_le (normUB_sq (m'.a - m0.a) (m'.b - m0.b))
        rw [← fx_sub] at hd
        have h1r : ((normUB (m'.a - m0.a) (m'.b - m0.b) : ℕ) : ℝ) + (rhat' : ℝ) ≤ (Rhat : ℝ) := by
          exact_mod_cast h1
        calc ‖(fc c)^[i + 1] z - fx m0.a m0.b‖
            = ‖((fc c)^[i + 1] z - fx m'.a m'.b) + (fx m'.a m'.b - fx m0.a m0.b)‖ := by
              congr 1; ring
          _ ≤ ‖(fc c)^[i + 1] z - fx m'.a m'.b‖ + ‖fx m'.a m'.b - fx m0.a m0.b‖ :=
              norm_add_le _ _
          _ ≤ (rhat' : ℝ) / SN + ((normUB (m'.a - m0.a) (m'.b - m0.b) : ℕ) : ℝ) / SN :=
              add_le_add hn hd
          _ ≤ (Rhat : ℝ) / SN := by
              rw [← add_div]
              exact div_le_div_of_nonneg_right (by linarith) hS.le
      · rw [if_neg h1] at h
        by_cases h2 : 8 * SN < rhat'
        · rw [if_pos h2] at h
          exact absurd h (by simp)
        · rw [if_neg h2] at h
          exact ih (i + 1) m' rhat' B' hB'0 hinv' h

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

lemma mem_mandelbrot_of_trap {ca cb : ℤ} {rc pmax J : ℕ} {m : Ball}
    (hE : Encl (fx ca cb) ((rc : ℝ) / SN) J m) (h : trapTest ca cb rc pmax m = true)
    {c : ℂ} (hc : ‖c - fx ca cb‖ ≤ (rc : ℝ) / SN) : c ∈ MandelbrotSet := by
  have hS := SN_pos
  have hRhat : (m.R : ℝ) ≤ ((3 * m.R / 2 : ℕ) : ℝ) := by
    have : m.R ≤ 3 * m.R / 2 := by omega
    exact_mod_cast this
  have hB₀ : 0 ≤ (((normUB m.a m.b : ℕ) : ℝ) + ((3 * m.R / 2 : ℕ) : ℝ)) / SN := by positivity
  obtain ⟨p, B', hp, hmain⟩ := trapScan_sound (ca := ca) (cb := cb) (rc := rc) (m0 := m)
    (Rhat := 3 * m.R / 2) pmax 0 m (3 * m.R / 2)
    ((((normUB m.a m.b : ℕ) : ℝ) + ((3 * m.R / 2 : ℕ) : ℝ)) / SN) hB₀ (by
      intro c' _ z hz
      refine ⟨by simpa using hz, ?_⟩
      intro k hk
      have hk0 : k = 0 := by omega
      subst hk0
      have hfx := fx_norm_le (normUB_sq m.a m.b)
      calc ‖(fc c')^[0] z‖ = ‖z‖ := rfl
        _ = ‖(z - fx m.a m.b) + fx m.a m.b‖ := by congr 1; ring
        _ ≤ ‖z - fx m.a m.b‖ + ‖fx m.a m.b‖ := norm_add_le _ _
        _ ≤ _ := by
          have e : (((normUB m.a m.b : ℕ) : ℝ) + ((3 * m.R / 2 : ℕ) : ℝ)) / SN =
              ((normUB m.a m.b : ℕ) : ℝ) / SN + ((3 * m.R / 2 : ℕ) : ℝ) / SN := by ring
          rw [e]
          linarith) h
  have hz0 : ‖orbit c 0 J - fx m.a m.b‖ ≤ ((3 * m.R / 2 : ℕ) : ℝ) / SN := by
    have := hE c hc
    exact this.trans (div_le_div_of_nonneg_right hRhat hS.le)
  have hbd := iterate_bounded_of_trap (f := fc c)
    (D := {z : ℂ | ‖z - fx m.a m.b‖ ≤ ((3 * m.R / 2 : ℕ) : ℝ) / SN}) hp
    (fun z hz => (hmain c hc z hz).1) (fun z hz k hk => (hmain c hc z hz).2 k hk) hz0
  refine ⟨max B' (∑ k ∈ Finset.range J, ‖orbit c 0 k‖), ?_⟩
  intro k
  by_cases hk : k < J
  · refine le_trans ?_ (le_max_right _ _)
    exact Finset.single_le_sum (f := fun k => ‖orbit c 0 k‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_range.mpr hk)
  · refine le_trans ?_ (le_max_left _ _)
    obtain ⟨k', rfl⟩ := Nat.exists_eq_add_of_le (not_lt.mp hk)
    have : orbit c 0 (J + k') = (fc c)^[k'] (orbit c 0 J) := by
      show (fc c)^[J + k'] 0 = (fc c)^[k'] ((fc c)^[J] 0)
      rw [add_comm, Function.iterate_add_apply]
    rw [this]
    exact hbd k'

lemma classifyLoop_sound {ca cb : ℤ} {rc pmax : ℕ} : ∀ (n k : ℕ) (m : Ball),
    Encl (fx ca cb) ((rc : ℝ) / SN) k m →
      (classifyLoop ca cb rc pmax n m = 1 →
        ∀ c : ℂ, ‖c - fx ca cb‖ ≤ (rc : ℝ) / SN → c ∉ MandelbrotSet) ∧
      (classifyLoop ca cb rc pmax n m = 2 →
        ∀ c : ℂ, ‖c - fx ca cb‖ ≤ (rc : ℝ) / SN → c ∈ MandelbrotSet) := by
  intro n
  induction n with
  | zero =>
      intro k m hE
      constructor
      · intro h c hc hM
        by_cases h1 : escaped m = true
        · have := escaped_sound hE h1 hc
          rw [MLC.Quadratic.mandelbrot_eq_inter] at hM
          have := Set.mem_iInter.mp hM k
          simp only [Set.mem_setOf_eq] at this
          linarith [escaped_sound hE h1 hc]
        · by_cases h2 : 8 * SN < m.R
          · simp [classifyLoop, h1, h2] at h
          · by_cases h3 : trapTest ca cb rc pmax m = true
            · simp [classifyLoop, h1, h2, h3] at h
            · simp [classifyLoop, h1, h2, h3] at h
      · intro h c hc
        by_cases h1 : escaped m = true
        · simp [classifyLoop, h1] at h
        · by_cases h2 : 8 * SN < m.R
          · simp [classifyLoop, h1, h2] at h
          · by_cases h3 : trapTest ca cb rc pmax m = true
            · exact mem_mandelbrot_of_trap hE h3 hc
            · simp [classifyLoop, h1, h2, h3] at h
  | succ n ih =>
      intro k m hE
      constructor
      · intro h c hc hM
        by_cases h1 : escaped m = true
        · rw [MLC.Quadratic.mandelbrot_eq_inter] at hM
          have := Set.mem_iInter.mp hM k
          simp only [Set.mem_setOf_eq] at this
          linarith [escaped_sound hE h1 hc]
        · by_cases h2 : 8 * SN < m.R
          · simp [classifyLoop, h1, h2] at h
          · have h' : classifyLoop ca cb rc pmax n (stepBall ca cb rc m) = 1 := by
              simpa [classifyLoop, h1, h2] using h
            exact (ih (k + 1) _ (encl_step hE)).1 h' c hc hM
      · intro h c hc
        by_cases h1 : escaped m = true
        · simp [classifyLoop, h1] at h
        · by_cases h2 : 8 * SN < m.R
          · simp [classifyLoop, h1, h2] at h
          · have h' : classifyLoop ca cb rc pmax n (stepBall ca cb rc m) = 2 := by
              simpa [classifyLoop, h1, h2] using h
            exact (ih (k + 1) _ (encl_step hE)).2 h' c hc

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

lemma Sq.cls_sound {q : Sq} {pmax J : ℕ} :
    (q.cls pmax J = 1 → q.set ∩ MandelbrotSet = ∅) ∧
    (q.cls pmax J = 2 → q.set ⊆ MandelbrotSet) := by
  by_cases hk : q.k ≤ 47
  · have hcls : q.cls pmax J = classifyLoop q.ca q.cb q.rc pmax J ⟨0, 0, 0⟩ := by
      simp [Sq.cls, hk]
    have hsound := classifyLoop_sound (ca := q.ca) (cb := q.cb) (rc := q.rc) (pmax := pmax)
      J 0 ⟨0, 0, 0⟩ (encl_zero _ _)
    constructor
    · intro h
      rw [hcls] at h
      ext c
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
      intro hc
      exact hsound.1 h c (Sq.set_subset_disk q hk hc)
    · intro h c hc
      rw [hcls] at h
      exact hsound.2 h c (Sq.set_subset_disk q hk hc)
  · have : q.cls pmax J = 0 := by simp [Sq.cls, hk]
    constructor <;> intro h <;> simp [this] at h

lemma Sq.unresolved_null {q : Sq} {pmax J : ℕ} (h : q.resolved pmax J = true) :
    volume (q.set ∩ Unresolved) = 0 := by
  simp only [Sq.resolved, decide_eq_true_eq] at h
  rcases h with h | h
  · have hout := (Sq.cls_sound (q := q) (pmax := pmax) (J := J)).1 h
    have hsub : q.set ∩ Unresolved = ∅ := by
      ext c
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
      intro hc hU
      have : c ∈ q.set ∩ MandelbrotSet := ⟨hc, hU.1⟩
      rw [hout] at this
      exact this
    rw [hsub]; simp
  · have hM := (Sq.cls_sound (q := q) (pmax := pmax) (J := J)).2 h
    have hopen : q.openSet ⊆ interior MandelbrotSet :=
      interior_maximal (q.openSet_subset.trans hM) q.isOpen_openSet
    have hsub : q.set ∩ Unresolved ⊆ q.set \ q.openSet := by
      intro c ⟨hc, hU⟩
      exact ⟨hc, fun ho => hU.2 (hopen ho)⟩
    exact measure_mono_null hsub q.volume_boundary

theorem cells_sound (pmax J : ℕ) : ∀ (f : ℕ) (q : Sq),
    volume (q.set ∩ Unresolved) ≤
      ENNReal.ofReal ((cells pmax J f q : ℝ) / 4 ^ (q.k + f)) := by
  intro f
  induction f with
  | zero =>
      intro q
      by_cases h : q.resolved pmax J = true
      · simp [cells, h, Sq.unresolved_null h]
      · simp only [cells, h, if_false, Bool.false_eq_true]
        calc volume (q.set ∩ Unresolved) ≤ volume q.set :=
              measure_mono Set.inter_subset_left
          _ = ENNReal.ofReal (1 / 4 ^ q.k) := q.volume_set
          _ = _ := by simp
  | succ f ih =>
      intro q
      by_cases h : q.resolved pmax J = true
      · simp [cells, h, Sq.unresolved_null h]
      · simp only [cells, h, if_false, Bool.false_eq_true]
        have hsub : q.set ∩ Unresolved ⊆
            (q.c00.set ∩ Unresolved) ∪ (q.c10.set ∩ Unresolved) ∪
              (q.c01.set ∩ Unresolved) ∪ (q.c11.set ∩ Unresolved) := by
          intro c ⟨hc, hM⟩
          have := Sq.subset_children q hc
          simp only [Set.mem_union] at this ⊢
          rcases this with ((h1 | h1) | h1) | h1
          · exact Or.inl (Or.inl (Or.inl ⟨h1, hM⟩))
          · exact Or.inl (Or.inl (Or.inr ⟨h1, hM⟩))
          · exact Or.inl (Or.inr ⟨h1, hM⟩)
          · exact Or.inr ⟨h1, hM⟩
        calc volume (q.set ∩ Unresolved)
            ≤ volume ((q.c00.set ∩ Unresolved) ∪ (q.c10.set ∩ Unresolved) ∪
              (q.c01.set ∩ Unresolved) ∪ (q.c11.set ∩ Unresolved)) :=
              measure_mono hsub
          _ ≤ volume (q.c00.set ∩ Unresolved) + volume (q.c10.set ∩ Unresolved) +
              volume (q.c01.set ∩ Unresolved) + volume (q.c11.set ∩ Unresolved) := by
              refine (measure_union_le _ _).trans ?_
              refine add_le_add ((measure_union_le _ _).trans ?_) le_rfl
              exact add_le_add ((measure_union_le _ _).trans le_rfl) le_rfl
          _ ≤ ENNReal.ofReal ((cells pmax J f q.c00 : ℝ) / 4 ^ (q.c00.k + f)) +
              ENNReal.ofReal ((cells pmax J f q.c10 : ℝ) / 4 ^ (q.c10.k + f)) +
              ENNReal.ofReal ((cells pmax J f q.c01 : ℝ) / 4 ^ (q.c01.k + f)) +
              ENNReal.ofReal ((cells pmax J f q.c11 : ℝ) / 4 ^ (q.c11.k + f)) :=
              add_le_add (add_le_add (add_le_add (ih _) (ih _)) (ih _)) (ih _)
          _ = ENNReal.ofReal (((cells pmax J f q.c00 + cells pmax J f q.c10 +
                cells pmax J f q.c01 + cells pmax J f q.c11 : ℕ) : ℝ) /
                  4 ^ (q.k + (f + 1))) := by
              have hk : ∀ q' : Sq, q'.k = q.k + 1 → q'.k + f = q.k + (f + 1) := by
                intro q' h; omega
              rw [hk q.c00 rfl, hk q.c10 rfl, hk q.c01 rfl, hk q.c11 rfl,
                ← ENNReal.ofReal_add (by positivity) (by positivity),
                ← ENNReal.ofReal_add (by positivity) (by positivity),
                ← ENNReal.ofReal_add (by positivity) (by positivity)]
              congr 1
              push_cast
              ring

lemma volume_list_le (pmax J F L0 : ℕ) : ∀ L : List Sq, (∀ q ∈ L, q.k = L0) →
    volume (Unresolved ∩ ⋃ q ∈ L, q.set) ≤
      ENNReal.ofReal (((L.map (cells pmax J F)).sum : ℝ) / 4 ^ (L0 + F)) := by
  intro L
  induction L with
  | nil => intro _; simp
  | cons q L ih =>
      intro hk
      have hq : q.k = L0 := hk q (by simp)
      have hL : ∀ q' ∈ L, q'.k = L0 := fun q' h => hk q' (by simp [h])
      have hsub : Unresolved ∩ ⋃ q' ∈ q :: L, q'.set ⊆
          (q.set ∩ Unresolved) ∪ (Unresolved ∩ ⋃ q' ∈ L, q'.set) := by
        intro c ⟨hM, hc⟩
        simp only [Set.mem_iUnion, exists_prop, List.mem_cons] at hc
        obtain ⟨q', hq', hcq⟩ := hc
        rcases hq' with rfl | hq'
        · exact Or.inl ⟨hcq, hM⟩
        · exact Or.inr ⟨hM, by simp only [Set.mem_iUnion, exists_prop]; exact ⟨q', hq', hcq⟩⟩
      calc volume (Unresolved ∩ ⋃ q' ∈ q :: L, q'.set)
          ≤ volume ((q.set ∩ Unresolved) ∪ (Unresolved ∩ ⋃ q' ∈ L, q'.set)) :=
            measure_mono hsub
        _ ≤ volume (q.set ∩ Unresolved) + volume (Unresolved ∩ ⋃ q' ∈ L, q'.set) :=
            measure_union_le _ _
        _ ≤ ENNReal.ofReal ((cells pmax J F q : ℝ) / 4 ^ (q.k + F)) +
            ENNReal.ofReal (((L.map (cells pmax J F)).sum : ℝ) / 4 ^ (L0 + F)) :=
            add_le_add (cells_sound pmax J F q) (ih hL)
        _ = ENNReal.ofReal ((((q :: L).map (cells pmax J F)).sum : ℝ) / 4 ^ (L0 + F)) := by
            rw [hq, ← ENNReal.ofReal_add (by positivity) (by positivity)]
            congr 1
            simp only [List.map_cons, List.sum_cons]
            push_cast
            ring

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

/-- Symmetric form of the grid bound: only the upper half-plane is classified. -/
theorem unresolved_volume_le_sym (pmax J f : ℕ) :
    volume Unresolved ≤ 2 * ENNReal.ofReal ((rootCellsUp pmax J f : ℝ) / 4 ^ (3 + f)) := by
  set A : Set ℂ := Unresolved ∩ ⋃ q ∈ rootsUp, q.set with hA
  have hk : ∀ q ∈ rootsUp, q.k = 3 := by
    intro q hq
    simp only [rootsUp, List.mem_flatMap, List.mem_map] at hq
    obtain ⟨x, _, y, _, rfl⟩ := hq
    rfl
  have hAle : volume A ≤ ENNReal.ofReal ((rootCellsUp pmax J f : ℝ) / 4 ^ (3 + f)) :=
    volume_list_le pmax J f 3 rootsUp hk
  have hAm : MeasurableSet A := by
    refine measurableSet_unresolved.inter ?_
    refine MeasurableSet.biUnion (List.finite_toSet rootsUp).countable ?_
    intro q _
    exact q.measurableSet
  have hsub : Unresolved ⊆ A ∪ conj ⁻¹' A := by
    intro c hc
    by_cases him : 0 ≤ c.im
    · exact Or.inl ⟨hc, unresolved_up_subset ⟨hc, him⟩⟩
    · right
      have hc' : conj c ∈ Unresolved := by
        have : c ∈ conj ⁻¹' Unresolved := by rw [conj_preimage_unresolved]; exact hc
        exact this
      refine ⟨hc', unresolved_up_subset ⟨hc', ?_⟩⟩
      simp only [Set.mem_setOf_eq, Complex.conj_im]
      linarith [not_le.mp him]
  calc volume Unresolved ≤ volume (A ∪ conj ⁻¹' A) := measure_mono hsub
    _ ≤ volume A + volume (conj ⁻¹' A) := measure_union_le _ _
    _ = volume A + volume A := by rw [volume_conj_preimage A hAm]
    _ ≤ ENNReal.ofReal ((rootCellsUp pmax J f : ℝ) / 4 ^ (3 + f)) +
        ENNReal.ofReal ((rootCellsUp pmax J f : ℝ) / 4 ^ (3 + f)) := add_le_add hAle hAle
    _ = 2 * ENNReal.ofReal ((rootCellsUp pmax J f : ℝ) / 4 ^ (3 + f)) := by rw [two_mul]

end MLC.Certified
