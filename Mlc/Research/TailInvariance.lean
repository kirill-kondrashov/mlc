import Mlc.Research.Degeneration

/-!
# Tail invariance of the degeneration tower

The open lemmas of Problem 4.3 (`Mlc/Research/Problem43.lean`) are statements about the
renormalization tower `f = f₀, f₁, …` of a parameter: the Teichmüller contraction TC′
(`Teichmuller`), the cap G on the jumps at the levels of large relative period
(`LargePeriodJumpCap`) and the linear dichotomy D (`LinearDichotomy`). This module proves that
each of them, and the a priori bounds that they give, depends on a tail of the tower only.

**Tuning and untuning.** Tuning with an `n`-step prefix maps the Mandelbrot set onto a little
copy of itself. In the model of `Mlc/Research/Degeneration.lean`, with abstract real widths,
the tower of a tuned parameter `c' = τ(c)` is the prefix of `n` levels followed by the tower of
`c`: the relative periods, the kinds and the degenerations of the levels from `n` on are those
of `c`. Dropping the first `n` levels is the untuning, `T.shift n`. Its levels, periods, jumps
and amplifications are those of `T` at the levels `k + n` (`shift_rel`, `period_shift`,
`jumps_shift`, `amplifies_shift`).

**Tail invariance.** A finite prefix changes finitely many data, and a finite family of real
numbers has a maximum. Each statement of the programme holds for `T` exactly when it holds for
`T.shift n`, with constants that differ by quantities that the prefix determines:

* `aPrioriBounds_shift_iff`: the widths of the first `n` levels have a finite maximum;
* `teichmuller_shift_iff`: the prefix contributes the finitely many ratios `W_{k+1} / W_k`,
  `k < n`, to the growth factor `Δ_P`;
* `largePeriodJumpCap_shift_iff`: the ceiling `B₀` is enlarged by the widths of the first
  `n + 1` levels;
* `linearDichotomy_shift_iff`: a pair of levels `k < n < k + m` that straddles the prefix has
  the period `period k (n - k) · period n b` with `b = k + m - n` (`period_split`), a product
  of a prefix period, which takes finitely many values, and a period of the tail. The
  amplification of the tail from the level `n` gives the amplification from the level `k`
  with the constant `c` divided by a bound of the prefix periods and with the error enlarged
  by `W_n`; the pairs inside the prefix are covered by the error;
* `aPrioriBounds_of_shift_tails`: the Teichmüller contraction, the cap and the linear
  dichotomy of the tail `T.shift n` give a priori bounds for `T`;
* `lemmas_shift_iff`: the three lemmas hold for `T` exactly when they hold for `T.shift n`.

**Two self-similarities.** The equivalences are the exact, combinatorial self-similarity of
the Mandelbrot set under tuning: the constants of `T` are computed from those of `T.shift n`
and from the prefix, and they depend on the prefix. The metric self-similarity compares the
degenerations of `c` and `τ(c)` quantitatively, with constants that serve all the tuned copies
at once. It is the geometric content that the lemmas of Problems 4.3 and 4.4 ask for: the
theorems of this module carry the combinatorial part, and the lemmas carry the metric part.
-/

namespace MLC.Research

open Finset

noncomputable section

namespace WidthTower

variable (T : WidthTower)

/-- The tower with the first `n` levels removed: the untuning by an `n`-step prefix. Its
level `k` is the level `k + n` of `T`. -/
def shift (n : ℕ) : WidthTower where
  rel := fun k => T.rel (k + n)
  two_le := fun k => T.two_le (k + n)
  kind := fun k => T.kind (k + n)
  width := fun k => T.width (k + n)
  width_pos := fun k => T.width_pos (k + n)

/-- The relative period of the level `k` of `T.shift n` is that of the level `k + n` of `T`. -/
@[simp] theorem shift_rel (n k : ℕ) : (T.shift n).rel k = T.rel (k + n) := rfl

/-- The kind of the level `k` of `T.shift n` is that of the level `k + n` of `T`. -/
@[simp] theorem shift_kind (n k : ℕ) : (T.shift n).kind k = T.kind (k + n) := rfl

/-- The degeneration of the level `k` of `T.shift n` is that of the level `k + n` of `T`. -/
@[simp] theorem shift_width (n k : ℕ) : (T.shift n).width k = T.width (k + n) := rfl

/-- Towers with the same relative periods, kinds and widths are equal. -/
theorem ext_of {S₁ S₂ : WidthTower} (hr : S₁.rel = S₂.rel) (hk : S₁.kind = S₂.kind)
    (hw : S₁.width = S₂.width) : S₁ = S₂ := by
  cases S₁
  cases S₂
  simp only at hr hk hw
  subst hr hk hw
  rfl

/-- The untuning by `0` levels leaves the tower unchanged. -/
@[simp] theorem shift_zero : T.shift 0 = T := ext_of rfl rfl rfl

/-- Dropping `n` levels and then `m` levels drops `n + m` levels. -/
theorem shift_shift (n m : ℕ) : (T.shift n).shift m = T.shift (n + m) := by
  refine ext_of (funext fun k => ?_) (funext fun k => ?_) (funext fun k => ?_)
  · simp only [shift_rel]
    congr 1
    omega
  · simp only [shift_kind]
    congr 1
    omega
  · simp only [shift_width]
    congr 1
    omega

/-- The period of `T.shift n` from the level `k` over `m` levels is the period of `T` from the
level `k + n` over `m` levels. -/
@[simp] theorem period_shift (n k m : ℕ) : (T.shift n).period k m = T.period (k + n) m := by
  unfold period
  refine Finset.prod_congr rfl fun j _ => ?_
  simp only [shift_rel]
  congr 1
  omega

/-- A jump of `T.shift n` at the level `m` is a jump of `T` at the level `m + n`. -/
@[simp] theorem jumps_shift (C : ℝ) (n m : ℕ) :
    (T.shift n).Jumps C m ↔ T.Jumps C (m + n) := by
  unfold Jumps
  simp only [shift_width]
  rw [Nat.add_right_comm m 1 n]

/-- An amplification of `T.shift n` between the levels `k` and `k + m` is the amplification of
`T` between the levels `k + n` and `k + n + m`. -/
@[simp] theorem amplifies_shift (c : ℝ) (E : ℕ → ℝ) (n k m : ℕ) :
    (T.shift n).Amplifies c E k m ↔ T.Amplifies c E (k + n) m := by
  unfold Amplifies
  simp only [shift_width, period_shift]
  rw [Nat.add_right_comm k m n]

/-- The period over `a + b` levels is the period over the first `a` levels times the period
over the next `b` levels. -/
theorem period_add (k a b : ℕ) : T.period k (a + b) = T.period k a * T.period (k + a) b := by
  unfold period
  rw [Finset.prod_range_add]
  simp only [Nat.add_assoc]

/-- Every relative period is at least `1`. -/
theorem one_le_period (k n : ℕ) : 1 ≤ T.period k n :=
  Nat.one_le_two_pow.trans (T.two_pow_le_period k n)

/-- If `k ≤ n` and `k + m = b + n`, the period over the `m` levels from `k` is the period over
the `n - k` levels from `k` up to the level `n` times the period over the `b` levels from `n`. -/
theorem period_split {k n m b : ℕ} (hk : k ≤ n) (hb : k + m = b + n) :
    T.period k m = T.period k (n - k) * T.period n b := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hk
  obtain rfl : m = a + b := by omega
  rw [Nat.add_sub_cancel_left, period_add]

/-- A real sequence is bounded above on the first `n` indices by a nonnegative constant: a
finite family has a maximum. -/
theorem exists_nonneg_bound (f : ℕ → ℝ) (n : ℕ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ k, k < n → f k ≤ M :=
  ⟨∑ j ∈ range n, |f j|, Finset.sum_nonneg fun _ _ => abs_nonneg _, fun k hk =>
    (le_abs_self (f k)).trans
      (Finset.single_le_sum (f := fun j => |f j|) (fun _ _ => abs_nonneg _) (mem_range.mpr hk))⟩

/-! ### A priori bounds and the Teichmüller contraction -/

/-- **A priori bounds are tail-invariant.** A tower has a priori bounds if and only if the tower
with its first `n` levels removed has them: the widths of the prefix have a finite maximum. -/
theorem aPrioriBounds_shift_iff (n : ℕ) : (T.shift n).APrioriBounds ↔ T.APrioriBounds := by
  constructor
  · rintro ⟨B, hB⟩
    obtain ⟨W, -, hW⟩ := exists_nonneg_bound T.width n
    refine ⟨max B W, fun k => ?_⟩
    by_cases hk : n ≤ k
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + n := ⟨k - n, by omega⟩
      exact (hB j).trans (le_max_left _ _)
    · exact (hW k (not_le.mp hk)).trans (le_max_right _ _)
  · rintro ⟨B, hB⟩
    exact ⟨B, fun k => hB (k + n)⟩

/-- **The Teichmüller contraction is tail-invariant.** The contraction holds for a tower if and
only if it holds for the tower with its first `n` levels removed: the factor `Δ_P` of the tail
is enlarged by the finitely many ratios `W_{k+1} / W_k`, `k < n`, of the prefix. -/
theorem teichmuller_shift_iff (n : ℕ) : (T.shift n).Teichmuller ↔ T.Teichmuller := by
  constructor
  · intro h P
    obtain ⟨Δ, hΔ⟩ := h P
    obtain ⟨R, -, hR⟩ := exists_nonneg_bound (fun j => T.width (j + 1) / T.width j) n
    refine ⟨max Δ R, fun k hk => ?_⟩
    have hw := T.width_pos k
    by_cases hkn : n ≤ k
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + n := ⟨k - n, by omega⟩
      have h1 : T.width (j + 1 + n) ≤ Δ * T.width (j + n) := hΔ j hk
      rw [show j + n + 1 = j + 1 + n by omega]
      exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hw.le)
    · have h1 : T.width (k + 1) / T.width k ≤ R := hR k (not_le.mp hkn)
      rw [div_le_iff₀ hw] at h1
      exact h1.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hw.le)
  · intro h P
    obtain ⟨Δ, hΔ⟩ := h P
    refine ⟨Δ, fun k hk => ?_⟩
    have h1 : T.width (k + n + 1) ≤ Δ * T.width (k + n) := hΔ (k + n) hk
    rw [shift_width, shift_width, show k + 1 + n = k + n + 1 by omega]
    exact h1

/-! ### The cap on the jumps -/

/-- A cap on the jumps of `T` at the levels of relative period above `P₀` is a cap of the same
form on `T.shift n`, with the same constants. -/
theorem largePeriodJumpCap_shift {P₀ : ℕ} {C₀ B₀ : ℝ} (n : ℕ)
    (h : T.LargePeriodJumpCap P₀ C₀ B₀) : (T.shift n).LargePeriodJumpCap P₀ C₀ B₀ := by
  intro m hm hj
  have h1 : T.width (m + n + 1) ≤ B₀ := h (m + n) hm ((T.jumps_shift C₀ n m).mp hj)
  rw [shift_width, show m + 1 + n = m + n + 1 by omega]
  exact h1

/-- A cap on the jumps of `T.shift n` at the levels of relative period above `P₀` is a cap of
the same form on `T`, with the ceiling enlarged by the widths of the first `n + 1` levels. -/
theorem exists_largePeriodJumpCap_of_shift {P₀ : ℕ} {C₀ B₀ : ℝ} (n : ℕ)
    (h : (T.shift n).LargePeriodJumpCap P₀ C₀ B₀) :
    ∃ B₁ : ℝ, T.LargePeriodJumpCap P₀ C₀ B₁ := by
  obtain ⟨W, -, hW⟩ := exists_nonneg_bound T.width (n + 1)
  refine ⟨max B₀ W, fun m hm hj => ?_⟩
  by_cases hmn : n ≤ m
  · obtain ⟨j, rfl⟩ : ∃ j, m = j + n := ⟨m - n, by omega⟩
    have h1 : T.width (j + 1 + n) ≤ B₀ := h j hm ((T.jumps_shift C₀ n j).mpr hj)
    rw [show j + n + 1 = j + 1 + n by omega]
    exact h1.trans (le_max_left _ _)
  · exact (hW (m + 1) (by omega)).trans (le_max_right _ _)

/-- **The cap on the jumps is tail-invariant.** There is a cap on the jumps at the levels of
large relative period for `T` if and only if there is one for the tower with its first `n`
levels removed. -/
theorem largePeriodJumpCap_shift_iff (n : ℕ) :
    (∃ (P₀ : ℕ) (C₀ B₀ : ℝ), 0 < C₀ ∧ (T.shift n).LargePeriodJumpCap P₀ C₀ B₀) ↔
      ∃ (P₀ : ℕ) (C₀ B₀ : ℝ), 0 < C₀ ∧ T.LargePeriodJumpCap P₀ C₀ B₀ := by
  constructor
  · rintro ⟨P₀, C₀, B₀, hC, h⟩
    obtain ⟨B₁, hB₁⟩ := T.exists_largePeriodJumpCap_of_shift n h
    exact ⟨P₀, C₀, B₁, hC, hB₁⟩
  · rintro ⟨P₀, C₀, B₀, hC, h⟩
    exact ⟨P₀, C₀, B₀, hC, T.largePeriodJumpCap_shift n h⟩

/-! ### The linear dichotomy -/

/-- The amplification persists when the constant decreases and the linear error grows. -/
theorem amplifies_mono {c c' A A' : ℝ} (hc : c ≤ c') (hA : A' ≤ A) (k m : ℕ)
    (h : T.Amplifies c' (fun p => A' * p) k m) : T.Amplifies c (fun p => A * p) k m := by
  unfold Amplifies at h ⊢
  have hp : (0 : ℝ) ≤ (T.period k m : ℝ) := Nat.cast_nonneg _
  have hw := T.width_pos (k + m)
  have h1 := mul_le_mul_of_nonneg_right hc (mul_nonneg hp hw.le)
  have h2 := mul_le_mul_of_nonneg_right hA hp
  linarith

/-- The arithmetic of a pair of levels that straddles the prefix. Let `P ≥ 1` be the prefix
period, `q ≥ 1` the tail period, and `w`, `wn`, `wk` the widths of the levels `k + m`, `n`, `k`.
The tail amplification `c' q w - A' q ≤ wn` and `c P ≤ c'` give
`c (P q) w - (A' + wn + c W) (P q) ≤ wk`. -/
theorem glue_arith {c c' A' W P q w wn wk : ℝ} (hc : 0 ≤ c) (hA' : 0 ≤ A') (hW : 0 ≤ W)
    (hwn : 0 ≤ wn) (hwk : 0 ≤ wk) (hP : 1 ≤ P) (hq : 1 ≤ q) (hw : 0 ≤ w) (hcP : c * P ≤ c')
    (h : c' * q * w - A' * q ≤ wn) :
    c * (P * q) * w - (A' + wn + c * W) * (P * q) ≤ wk := by
  have hq0 : (0 : ℝ) ≤ q := by linarith
  have hP0 : (0 : ℝ) ≤ P := by linarith
  have h1 : c * P * (q * w) ≤ c' * (q * w) :=
    mul_le_mul_of_nonneg_right hcP (mul_nonneg hq0 hw)
  have h2 : (A' + wn) * q ≤ (A' + wn) * (P * q) :=
    mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hq0 hP) (by linarith)
  have h3 : 0 ≤ c * W * (P * q) := mul_nonneg (mul_nonneg hc hW) (mul_nonneg hP0 hq0)
  have h4 : wn ≤ wn * q := le_mul_of_one_le_right hwn hq
  linarith

/-- **The linear dichotomy passes to the tail.** If `T` satisfies the dichotomy with a linear
error, so does the tower with its first `n` levels removed, with the same constants: the pairs
of levels of the tail are pairs of levels of `T`. -/
theorem linearDichotomy_shift (n : ℕ) (h : T.LinearDichotomy) : (T.shift n).LinearDichotomy := by
  intro C hC
  obtain ⟨c, hc, A, hA, hE⟩ := h C hC
  refine ⟨c, hc, A, hA, fun k m => ?_⟩
  rcases hE (k + n) m with h1 | h1
  · exact Or.inl ((T.amplifies_shift c _ n k m).mpr h1)
  · refine Or.inr ((T.jumps_shift C n (k + m)).mpr ?_)
    rw [show k + m + n = k + n + m by omega]
    exact h1

/-- **The linear dichotomy of the tail gives the linear dichotomy.** If the tower with its first
`n` levels removed satisfies the dichotomy with a linear error, so does `T`, with other
constants. A pair of levels inside the tail is a pair of the tail. A pair `k < n < k + m` that
straddles the prefix has the period `P · q` of a prefix period `P = period k (n - k)` and a tail
period `q = period n b` (`period_split`); the tail gives a jump at the level `k + m` or the
amplification `c' q W_{k+m} - A' q ≤ W_n`, and `glue_arith` turns the latter into the
amplification from the level `k` with the constant `c = c' / (1 + S)` and the error
`A' + W_n + c W`, where `S` bounds the finitely many prefix periods and `W` the widths of the
first `n + 1` levels. A pair inside the prefix, `k + m ≤ n`, satisfies the amplification
because the term `c W` of the error exceeds `c W_{k+m}`. -/
theorem linearDichotomy_of_shift (n : ℕ) (h : (T.shift n).LinearDichotomy) :
    T.LinearDichotomy := by
  intro C hC
  obtain ⟨c', hc', A', hA', hD⟩ := h C hC
  obtain ⟨S, hS0, hS⟩ := exists_nonneg_bound (fun k => (T.period k (n - k) : ℝ)) n
  obtain ⟨W, hW0, hW⟩ := exists_nonneg_bound T.width (n + 1)
  have hwn := T.width_pos n
  obtain ⟨c, hc0, hcc', hcP⟩ : ∃ c : ℝ, 0 < c ∧ c ≤ c' ∧ ∀ P : ℝ, P ≤ S → c * P ≤ c' := by
    refine ⟨c' / (1 + S), div_pos hc' (by linarith), div_le_self hc'.le (by linarith),
      fun P hP => ?_⟩
    rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    exact mul_le_mul_of_nonneg_left (by linarith) hc'.le
  have hcW : 0 ≤ c * W := mul_nonneg hc0.le hW0
  refine ⟨c, hc0, A' + T.width n + c * W, by linarith, fun k m => ?_⟩
  by_cases hk : n ≤ k
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + n := ⟨k - n, by omega⟩
    rcases hD j m with h1 | h1
    · exact Or.inl (T.amplifies_mono hcc' (by linarith) _ _
        ((T.amplifies_shift c' _ n j m).mp h1))
    · refine Or.inr ?_
      have h2 := (T.jumps_shift C n (j + m)).mp h1
      rwa [show j + m + n = j + n + m by omega] at h2
  · have hkn : k < n := not_le.mp hk
    by_cases hkm : k + m ≤ n
    · refine Or.inl ?_
      unfold Amplifies
      have hp : (0 : ℝ) ≤ (T.period k m : ℝ) := Nat.cast_nonneg _
      have hw : T.width (k + m) ≤ W := hW (k + m) (by omega)
      have hwk := T.width_pos k
      have h1 := mul_le_mul_of_nonneg_left hw (mul_nonneg hc0.le hp)
      have h2 := mul_nonneg hA' hp
      have h3 := mul_nonneg hwn.le hp
      linarith
    · obtain ⟨b, hb⟩ : ∃ b, k + m = b + n := ⟨k + m - n, by omega⟩
      rcases hD 0 b with h1 | h1
      · refine Or.inl ?_
        have h2 := (T.amplifies_shift c' (fun p => A' * p) n 0 b).mp h1
        rw [zero_add] at h2
        simp only [Amplifies] at h2 ⊢
        rw [show n + b = k + m by omega] at h2
        have hq : (1 : ℝ) ≤ (T.period n b : ℝ) := by exact_mod_cast T.one_le_period n b
        have hP : (1 : ℝ) ≤ (T.period k (n - k) : ℝ) := by
          exact_mod_cast T.one_le_period k (n - k)
        have key := glue_arith hc0.le hA' hW0 hwn.le (T.width_pos k).le hP hq
          (T.width_pos (k + m)).le (hcP _ (hS k hkn)) h2
        rw [T.period_split hkn.le hb, Nat.cast_mul]
        exact key
      · refine Or.inr ?_
        have h2 := (T.jumps_shift C n (0 + b)).mp h1
        rwa [zero_add, ← hb] at h2

/-- **The linear dichotomy is tail-invariant.** A tower satisfies the dichotomy with a linear
error if and only if the tower with its first `n` levels removed does. -/
theorem linearDichotomy_shift_iff (n : ℕ) : (T.shift n).LinearDichotomy ↔ T.LinearDichotomy :=
  ⟨T.linearDichotomy_of_shift n, T.linearDichotomy_shift n⟩

/-! ### The programme -/

/-- **The combination theorem for the tail.** The Teichmüller contraction, a cap on the jumps at
the levels of large relative period and the dichotomy with a linear error, all for the tower
with its first `n` levels removed, give a priori bounds for the tower itself. -/
theorem aPrioriBounds_of_shift_tails {n P₀ : ℕ} {C₀ B₀ : ℝ} (hC : 0 < C₀)
    (hT : (T.shift n).Teichmuller) (hL : (T.shift n).LargePeriodJumpCap P₀ C₀ B₀)
    (hD : (T.shift n).LinearDichotomy) : T.APrioriBounds :=
  (T.aPrioriBounds_shift_iff n).mp ((T.shift n).aPrioriBounds_of_tails hC hT hL hD)

/-- **The three lemmas of Problem 4.3 are tail-invariant.** The Teichmüller contraction, the cap
on the jumps at the levels of large relative period and the dichotomy with a linear error hold
for a tower if and only if they hold for the tower with its first `n` levels removed. -/
theorem lemmas_shift_iff (n : ℕ) :
    ((T.shift n).Teichmuller ∧
        (∃ (P₀ : ℕ) (C₀ B₀ : ℝ), 0 < C₀ ∧ (T.shift n).LargePeriodJumpCap P₀ C₀ B₀) ∧
        (T.shift n).LinearDichotomy) ↔
      (T.Teichmuller ∧
        (∃ (P₀ : ℕ) (C₀ B₀ : ℝ), 0 < C₀ ∧ T.LargePeriodJumpCap P₀ C₀ B₀) ∧
        T.LinearDichotomy) :=
  and_congr (T.teichmuller_shift_iff n)
    (and_congr (T.largePeriodJumpCap_shift_iff n) (T.linearDichotomy_shift_iff n))

end WidthTower

end

end MLC.Research
