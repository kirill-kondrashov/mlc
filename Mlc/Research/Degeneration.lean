import Mlc.Research.Programme
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The degeneration recursion of the near-degenerate argument

This module formalizes the *logic* of Dudko's §4.1–§4.3, with the geometric inputs as
explicit hypotheses. Let `f = f₀, f₁, f₂, …` be the quadratic-like renormalization tower
of a parameter, `rel k` the period of `f_{k+1}` relative to `f_k`, and `W_k = W(f_k)` the
degeneration of the level (the reciprocal of its modulus, see (4.1)). The survey proves a
priori bounds, `sup_k W_k < ∞`, from two inputs:

* the amplification (4.3), `W(f_k) ⪰ p·W(f_{k+n}) − O_p(1)`, for primitive levels, and the
  dichotomy (4.6) for satellite levels: either this amplification holds, or the degeneration
  jumps, `W(f_{k+n+1}) ≥ C_δ W(f_{k+n})`, with `C_δ → ∞` as `δ → 0`;
* the Teichmüller contraction, which bounds the jump of the degeneration between consecutive
  levels by a factor `Δ` that depends exponentially on the relative period, so that the jump
  is impossible for `C_δ > Δ`.

Both inputs are named hypotheses here (`Dichotomy`, `Teichmuller`); the theorems below prove
that they imply the a priori bounds. For relative periods that are not bounded, the factor
`Δ` and the additive error `O_p(1)` are not uniform: this is exactly where the survey's
proof stops. Problem 4.3 asks for the uniform versions: a growth bound (`GrowthBound`) and
an additive error that grows at most linearly with the period (`LinearDichotomy`: each of
the `p` small Julia sets contributes a bounded error), which the pseudo-Siegel disks are meant
to supply. Linear growth is the threshold of the recursion, and both uniformities are
necessary: `aPrioriBounds_of_uniform` proves the bounds from them, `exists_unbounded_of_superlinear`
shows that an error `p · h(p)` with `h` unbounded does not suffice, even with a uniform growth
bound, and `exists_unbounded_of_teichmuller_linearDichotomy` shows that a growth bound that
depends on the relative period does not suffice, even with a linear error
(`uniformities_necessary`).

The widths are abstract real numbers. Nothing here defines a conformal modulus.
-/

namespace MLC.Research

open Finset

noncomputable section

/-- A level of a quadratic-like renormalization tower is primitive or satellite. -/
inductive LevelKind
  | primitive
  | satellite
  deriving DecidableEq

/-- The combinatorics and the degeneration of a quadratic-like renormalization tower
`f = f₀, f₁, …`: `rel k` is the period of `f_{k+1}` relative to `f_k`, and `width k` is the
degeneration `W(f_k)` of the level. -/
structure WidthTower where
  rel : ℕ → ℕ
  two_le : ∀ k, 2 ≤ rel k
  kind : ℕ → LevelKind
  width : ℕ → ℝ
  width_pos : ∀ k, 0 < width k

namespace WidthTower

variable (T : WidthTower)

/-- The period of `f_{k+n}` relative to `f_k`. -/
def period (k n : ℕ) : ℕ := ∏ j ∈ range n, T.rel (k + j)

theorem two_pow_le_period (k n : ℕ) : 2 ^ n ≤ T.period k n := by
  unfold period
  calc 2 ^ n = ∏ _j ∈ range n, 2 := by simp
    _ ≤ ∏ j ∈ range n, T.rel (k + j) :=
      Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun j _ => T.two_le (k + j))

theorem period_le_pow {P : ℕ} (hP : ∀ k, T.rel k ≤ P) (k n : ℕ) : T.period k n ≤ P ^ n := by
  unfold period
  calc ∏ j ∈ range n, T.rel (k + j) ≤ ∏ _j ∈ range n, P :=
        Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun j _ => hP (k + j))
    _ = P ^ n := by simp

/-- The tower has a priori bounds: the degeneration of all its levels is bounded, that is,
the moduli of all levels are bounded below. -/
def APrioriBounds : Prop := ∃ B : ℝ, ∀ k, T.width k ≤ B

/-- The amplification `W(f_k) ⪰ c·p·W(f_{k+n}) − E(p)` between the levels `k` and `k + n`,
where `p` is the period of `f_{k+n}` relative to `f_k`: the estimate (4.3). -/
def Amplifies (c : ℝ) (E : ℕ → ℝ) (k n : ℕ) : Prop :=
  c * (T.period k n : ℝ) * T.width (k + n) - E (T.period k n) ≤ T.width k

/-- The degeneration jumps by the factor `C` from the level `m` to the next one:
alternative (ii) of §4.3. -/
def Jumps (C : ℝ) (m : ℕ) : Prop := C * T.width m ≤ T.width (m + 1)

/-- The degeneration grows by at most the factor `Δ` from a level to the next one. -/
def GrowthBound (Δ : ℝ) : Prop := ∀ k, T.width (k + 1) ≤ Δ * T.width k

/-- Teichmüller contraction: for relative periods bounded by `P` the degeneration grows by at
most a factor `Δ_P` (the survey: `W(f_m) = O(Δ^{p_m})`). The factor depends on `P`. -/
def Teichmuller : Prop :=
  ∀ P : ℕ, ∃ Δ : ℝ, ∀ k, T.rel k ≤ P → T.width (k + 1) ≤ Δ * T.width k

/-- The dichotomy of §4.3 with an error that depends on the period: for every threshold `C`
there are constants such that, for every pair of levels, either the amplification holds, or
the degeneration jumps by `C`. -/
def Dichotomy : Prop :=
  ∀ C : ℝ, 0 < C → ∃ c : ℝ, 0 < c ∧ ∃ E : ℕ → ℝ,
    ∀ k n, T.Amplifies c E k n ∨ T.Jumps C (k + n)

/-- The dichotomy with an additive error that grows at most linearly with the period: each of
the `p` small Julia sets contributes a bounded error. -/
def LinearDichotomy : Prop :=
  ∀ C : ℝ, 0 < C → ∃ c : ℝ, 0 < c ∧ ∃ A : ℝ, 0 ≤ A ∧
    ∀ k n, T.Amplifies c (fun p => A * p) k n ∨ T.Jumps C (k + n)

/-- Amplification at a fixed distance between levels, with a constant `c` such that
`c · 2^{n₀} ≥ 2` and an error that does not depend on the period: the estimate (4.3) of
the primitive levels together with (4.5) of the anti-Molecule condition. -/
def StrongAmplification : Prop :=
  ∃ (c E : ℝ) (n₀ : ℕ), 2 ≤ c * 2 ^ n₀ ∧ ∀ k, T.Amplifies c (fun _ => E) k n₀

/-- A real sequence with `2 w(k + n₀) ≤ w(k) + E` is bounded. -/
theorem bounded_of_two_mul_le (w : ℕ → ℝ) (n₀ : ℕ) (E : ℝ)
    (h : ∀ k, 2 * w (k + n₀) ≤ w k + E) : ∃ B : ℝ, ∀ k, w k ≤ B := by
  rcases Nat.eq_zero_or_pos n₀ with h0 | h0
  · subst h0
    refine ⟨E, fun k => ?_⟩
    have := h k
    simp only [add_zero] at this
    linarith
  · refine ⟨max E (∑ j ∈ range n₀, |w j|), fun k => ?_⟩
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      by_cases hk : k < n₀
      · have h1 : |w k| ≤ ∑ j ∈ range n₀, |w j| :=
          Finset.single_le_sum (f := fun j => |w j|) (fun j _ => abs_nonneg _)
            (mem_range.mpr hk)
        exact (le_abs_self _).trans (h1.trans (le_max_right _ _))
      · obtain ⟨m, rfl⟩ : ∃ m, k = m + n₀ := ⟨k - n₀, by omega⟩
        have hm : m < m + n₀ := by omega
        have h2 := ih m hm
        have h3 := h m
        have h4 : E ≤ max E (∑ j ∈ range n₀, |w j|) := le_max_left _ _
        linarith

/-- **A priori bounds from linear amplification.** Amplification at a fixed distance `n₀`
between levels, with `c · 2^{n₀} ≥ 2` and an additive error at most linear in the period,
bounds the degeneration of all levels. -/
theorem aPrioriBounds_of_linear_amplification {c A : ℝ} {n₀ : ℕ} (hc : 2 ≤ c * 2 ^ n₀)
    (h : ∀ k, T.Amplifies c (fun p => A * p) k n₀) : T.APrioriBounds := by
  have hcpos : 0 < c := by
    by_contra hneg
    have : c * 2 ^ n₀ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hneg) (by positivity)
    linarith
  refine bounded_of_two_mul_le T.width n₀ (2 * A / c) fun k => ?_
  have hp : (2 : ℝ) ^ n₀ ≤ (T.period k n₀ : ℝ) := by exact_mod_cast T.two_pow_le_period k n₀
  have hp0 : 0 < (T.period k n₀ : ℝ) := lt_of_lt_of_le (by positivity) hp
  have hw : 0 < T.width (k + n₀) := T.width_pos _
  have hwk : 0 < T.width k := T.width_pos k
  have h1 : 2 ≤ c * (T.period k n₀ : ℝ) :=
    hc.trans (mul_le_mul_of_nonneg_left hp hcpos.le)
  have h2 := h k
  unfold Amplifies at h2
  -- `p (c w' - A) ≤ w k` and `c p ≥ 2` give `c w' ≤ A + c w k / 2`.
  have h3 : c * T.width (k + n₀) - A ≤ c / 2 * T.width k := by
    have h4 : (T.period k n₀ : ℝ) * (c * T.width (k + n₀) - A) ≤ T.width k := by linarith
    have h5 : (T.period k n₀ : ℝ) * (c * T.width (k + n₀) - A) ≤
        (T.period k n₀ : ℝ) * (c / 2 * T.width k) := by
      calc (T.period k n₀ : ℝ) * (c * T.width (k + n₀) - A) ≤ T.width k := h4
        _ ≤ (T.period k n₀ : ℝ) * (c / 2 * T.width k) := by nlinarith
    exact le_of_mul_le_mul_left h5 hp0
  have h6 : 2 * T.width (k + n₀) ≤ T.width k + 2 * A / c := by
    have hc' : c * (2 * A / c) = 2 * A := by field_simp
    by_contra hneg
    push_neg at hneg
    have h7 := mul_lt_mul_of_pos_left hneg hcpos
    nlinarith [hc', h3, h7]
  exact h6

/-- Amplification at a fixed distance `n₀` between levels, strong enough that
`c · 2^{n₀} ≥ 2`, bounds the degeneration of all levels. -/
theorem aPrioriBounds_of_amplification {c E : ℝ} {n₀ : ℕ} (hc : 2 ≤ c * 2 ^ n₀)
    (h : ∀ k, T.Amplifies c (fun _ => E) k n₀) : T.APrioriBounds := by
  have hcpos : 0 < c := by
    by_contra hneg
    have : c * 2 ^ n₀ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hneg) (by positivity)
    linarith
  refine bounded_of_two_mul_le T.width n₀ E fun k => ?_
  have hp : (2 : ℝ) ^ n₀ ≤ (T.period k n₀ : ℝ) := by exact_mod_cast T.two_pow_le_period k n₀
  have hw : 0 < T.width (k + n₀) := T.width_pos _
  have h1 : 2 ≤ c * (T.period k n₀ : ℝ) :=
    hc.trans (mul_le_mul_of_nonneg_left hp hcpos.le)
  have h2 := h k
  unfold Amplifies at h2
  nlinarith

/-- **A priori bounds from strong amplification** (primitive levels, §4.1 and §4.2). -/
theorem aPrioriBounds_of_strongAmplification (h : T.StrongAmplification) : T.APrioriBounds := by
  obtain ⟨c, E, n₀, hc, h⟩ := h
  exact T.aPrioriBounds_of_amplification hc h

/-- A jump by more than the growth factor is impossible. -/
theorem not_jumps_of_growth {Δ : ℝ} (hΔ : T.GrowthBound Δ) (m : ℕ) : ¬ T.Jumps (Δ + 1) m := by
  intro hj
  have h1 := hΔ m
  have h2 := T.width_pos m
  unfold Jumps at hj
  nlinarith

theorem growth_pos {Δ : ℝ} (hΔ : T.GrowthBound Δ) : 0 < Δ := by
  have h := hΔ 0
  have h1 := T.width_pos 0
  have h2 := T.width_pos 1
  by_contra hneg
  have : Δ * T.width 0 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hneg) h1.le
  linarith

theorem exists_two_le_mul_two_pow {c : ℝ} (hc : 0 < c) : ∃ n : ℕ, 0 < n ∧ 2 ≤ c * 2 ^ n := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (2 / c) (by norm_num : (1 : ℝ) < 2)
  refine ⟨n + 1, Nat.succ_pos n, ?_⟩
  have h1 : 2 < c * 2 ^ n := by
    rwa [div_lt_iff₀ hc, mul_comm] at hn
  calc (2 : ℝ) ≤ c * 2 ^ n := h1.le
    _ ≤ c * 2 ^ (n + 1) := by
      apply mul_le_mul_of_nonneg_left _ hc.le
      exact pow_le_pow_right₀ (by norm_num) (Nat.le_succ n)

/-- **A priori bounds from uniform control.** A uniform growth bound across all levels and the
dichotomy with an additive error at most linear in the period give a priori bounds for every
tower, whatever its relative periods are. -/
theorem aPrioriBounds_of_uniform {Δ : ℝ} (hG : T.GrowthBound Δ) (hD : T.LinearDichotomy) :
    T.APrioriBounds := by
  have hΔ := T.growth_pos hG
  obtain ⟨c, hc, A, -, hE⟩ := hD (Δ + 1) (by linarith)
  obtain ⟨n₀, -, hn₀⟩ := exists_two_le_mul_two_pow hc
  refine T.aPrioriBounds_of_linear_amplification hn₀ (A := A) fun k => ?_
  rcases hE k n₀ with h | h
  · exact h
  · exact absurd h (T.not_jumps_of_growth hG _)

/-- **A priori bounds for bounded type** (the argument behind Theorem 4.1): for relative
periods bounded by `P`, the Teichmüller contraction and the dichotomy with a period-dependent
error give a priori bounds. -/
theorem aPrioriBounds_of_bounded {P : ℕ} (hP : ∀ k, T.rel k ≤ P) (hT : T.Teichmuller)
    (hD : T.Dichotomy) : T.APrioriBounds := by
  obtain ⟨Δ, hΔ⟩ := hT P
  have hG : T.GrowthBound Δ := fun k => hΔ k (hP k)
  have hpos := T.growth_pos hG
  obtain ⟨c, hc, E, hE⟩ := hD (Δ + 1) (by linarith)
  obtain ⟨n₀, -, hn₀⟩ := exists_two_le_mul_two_pow hc
  -- The periods `p(k, n₀)` take finitely many values, so the error is bounded.
  set E' : ℝ := ∑ p ∈ range (P ^ n₀ + 1), |E p| with hE'
  refine T.aPrioriBounds_of_amplification hn₀ (E := E') fun k => ?_
  rcases hE k n₀ with h | h
  · unfold Amplifies at h ⊢
    have hle : T.period k n₀ ≤ P ^ n₀ := T.period_le_pow hP k n₀
    have h1 : |E (T.period k n₀)| ≤ E' :=
      Finset.single_le_sum (f := fun p => |E p|) (fun p _ => abs_nonneg _)
        (mem_range.mpr (Nat.lt_succ_of_le hle))
    have h2 : E (T.period k n₀) ≤ E' := (le_abs_self _).trans h1
    linarith
  · exact absurd h (T.not_jumps_of_growth hG _)

/-! ### Both uniformities are necessary

`aPrioriBounds_of_uniform` needs a uniform growth bound and a dichotomy with an error at most
linear in the period. Neither can be dropped.

* An error of order `p · h(p)` with `h` unbounded gives no a priori bounds, even with a uniform
  growth bound: the tower with relative periods `k + 2` and widths `h(k + 1)` satisfies the
  Teichmüller contraction, a uniform growth bound when `h` grows by a bounded factor, and the
  amplification with the error `p · h(p)`, and its degeneration is unbounded. With `h`
  constant the error `A · p` of `LinearDichotomy` suffices, so linear is the threshold of the
  recursion.
* A growth bound that depends on the relative period gives no a priori bounds, even with a
  linear error: in the tower with relative periods `k + 2` and widths `(k + 1)!` the
  degeneration jumps by the factor `k + 2` at every level, which the Teichmüller contraction
  allows, and the dichotomy holds because the jump alternative covers every level above a
  threshold that depends on `C`.

The inputs of Theorem 4.1 with period-dependent constants leave a gap exactly at unbounded
relative periods: Problem 4.3 needs new input, and the input has two parts. -/

/-- The tower with relative periods `k + 2` and widths `h(k + 1)`. -/
def counterTower (h : ℕ → ℝ) (hpos : ∀ x, 0 < h x) : WidthTower where
  rel := fun k => k + 2
  two_le := fun k => by omega
  kind := fun _ => LevelKind.satellite
  width := fun k => h (k + 1)
  width_pos := fun k => hpos (k + 1)

theorem counterTower_teichmuller {h : ℕ → ℝ} (hmono : Monotone h) (hpos : ∀ x, 0 < h x) :
    (counterTower h hpos).Teichmuller := by
  intro P
  refine ⟨h P / h 1, fun k hk => ?_⟩
  have hk' : k + 2 ≤ P := hk
  show h (k + 1 + 1) ≤ h P / h 1 * h (k + 1)
  calc h (k + 1 + 1) ≤ h P := hmono hk'
    _ = h P / h 1 * h 1 := by
      have h1 := (hpos 1).ne'
      field_simp
    _ ≤ h P / h 1 * h (k + 1) :=
      mul_le_mul_of_nonneg_left (hmono (by omega)) (div_nonneg (hpos P).le (hpos 1).le)

theorem counterTower_amplifies {h : ℕ → ℝ} (hmono : Monotone h) (hpos : ∀ x, 0 < h x)
    (k n : ℕ) : (counterTower h hpos).Amplifies 1 (fun p => (p : ℝ) * h p) k n := by
  rcases Nat.eq_zero_or_pos n with h0 | hn
  · subst h0
    have h1 := hpos 1
    simp only [Amplifies, period, Finset.range_zero, Finset.prod_empty, Nat.cast_one, one_mul,
      add_zero]
    linarith
  · have hle : k + n + 1 ≤ (counterTower h hpos).period k n := by
      have hmem : n - 1 ∈ Finset.range n := Finset.mem_range.mpr (by omega)
      have hdvd : (counterTower h hpos).rel (k + (n - 1)) ∣ (counterTower h hpos).period k n :=
        Finset.dvd_prod_of_mem (fun j => (counterTower h hpos).rel (k + j)) hmem
      have hppos : 0 < (counterTower h hpos).period k n :=
        Finset.prod_pos fun j _ => by show 0 < k + j + 2; omega
      have h2 : k + (n - 1) + 2 ≤ (counterTower h hpos).period k n :=
        Nat.le_of_dvd hppos hdvd
      omega
    show (1 : ℝ) * ((counterTower h hpos).period k n : ℝ) * h (k + n + 1)
        - ((counterTower h hpos).period k n : ℝ) * h ((counterTower h hpos).period k n)
        ≤ h (k + 1)
    generalize (counterTower h hpos).period k n = p at hle ⊢
    have h3 : h (k + n + 1) ≤ h p := hmono hle
    have hp : (0 : ℝ) ≤ p := Nat.cast_nonneg p
    nlinarith [mul_le_mul_of_nonneg_left h3 hp, hpos (k + 1)]

theorem counterTower_not_bounded {h : ℕ → ℝ} (hmono : Monotone h) (hpos : ∀ x, 0 < h x)
    (hunb : ∀ B : ℝ, ∃ x, B < h x) : ¬ (counterTower h hpos).APrioriBounds := by
  rintro ⟨B, hB⟩
  obtain ⟨x, hx⟩ := hunb B
  have h1 : h x ≤ h (x + 1) := hmono (Nat.le_succ x)
  have h2 : h (x + 1) ≤ B := hB x
  linarith

theorem counterTower_growth {h : ℕ → ℝ} (hpos : ∀ x, 0 < h x) {Δ : ℝ}
    (hΔ : ∀ x, h (x + 1) ≤ Δ * h x) : (counterTower h hpos).GrowthBound Δ :=
  fun k => hΔ (k + 1)

/-- **Linear error is the threshold.** For a monotone, positive and unbounded `h` there is a
tower of unbounded relative periods that satisfies the Teichmüller contraction, a uniform
growth bound whenever `h` grows by a bounded factor, and the amplification with the error
`p · h(p)` (so the dichotomy, with its first alternative at every pair of levels), and has
unbounded degeneration. -/
theorem exists_unbounded_of_superlinear {h : ℕ → ℝ} (hmono : Monotone h)
    (hpos : ∀ x, 0 < h x) (hunb : ∀ B : ℝ, ∃ x, B < h x) :
    ∃ T : WidthTower, T.Teichmuller ∧ (∀ Δ, (∀ x, h (x + 1) ≤ Δ * h x) → T.GrowthBound Δ) ∧
      (∀ k n, T.Amplifies 1 (fun p => (p : ℝ) * h p) k n) ∧ ¬ T.APrioriBounds :=
  ⟨counterTower h hpos, counterTower_teichmuller hmono hpos,
    fun _ hΔ => counterTower_growth hpos hΔ, counterTower_amplifies hmono hpos,
    counterTower_not_bounded hmono hpos hunb⟩

/-- **Uniform growth does not rescue a superlinear error.** There is a tower with a uniform
growth bound and the dichotomy, with an error quadratic in the period, and unbounded
degeneration. So the dichotomy of the survey, with an error that depends on the period, gives
no a priori bounds for unbounded relative periods even if the growth is uniform. -/
theorem exists_unbounded_of_growth_dichotomy :
    ∃ T : WidthTower, T.GrowthBound 2 ∧ T.Dichotomy ∧ ¬ T.APrioriBounds := by
  obtain ⟨T, -, hG, hA, hB⟩ := exists_unbounded_of_superlinear (h := fun x => (x : ℝ) + 1)
    (fun a b hab => by
      have := (Nat.cast_le (α := ℝ)).mpr hab
      simp only
      linarith)
    (fun x => by positivity) (fun B => ⟨⌈B⌉₊, by linarith [Nat.le_ceil B]⟩)
  refine ⟨T, hG 2 (fun x => ?_), fun C _ => ⟨1, one_pos, _, fun k n => Or.inl (hA k n)⟩, hB⟩
  simp only [Nat.cast_add, Nat.cast_one]
  linarith [(Nat.cast_nonneg x : (0 : ℝ) ≤ x)]

/-- The tower with relative periods `k + 2` and widths `(k + 1)!`: the degeneration jumps by
the factor `k + 2` at every level, the largest factor that the Teichmüller contraction
allows for the relative period `k + 2`. -/
def factTower : WidthTower where
  rel := fun k => k + 2
  two_le := fun k => by omega
  kind := fun _ => LevelKind.satellite
  width := fun k => ((k + 1).factorial : ℝ)
  width_pos := fun k => by exact_mod_cast Nat.factorial_pos (k + 1)

theorem factTower_teichmuller : factTower.Teichmuller := by
  intro P
  refine ⟨P, fun k hk => ?_⟩
  have hk' : k + 2 ≤ P := hk
  show (((k + 1 + 1).factorial : ℕ) : ℝ) ≤ (P : ℝ) * (((k + 1).factorial : ℕ) : ℝ)
  have e : (k + 1 + 1).factorial = (k + 2) * (k + 1).factorial := Nat.factorial_succ (k + 1)
  rw [e]
  push_cast
  have hk'' : ((k : ℝ) + 2) ≤ (P : ℝ) := by exact_mod_cast hk'
  exact mul_le_mul_of_nonneg_right hk'' (by positivity)

/-- The jump alternative holds at every level above a threshold `N` that depends on `C`, so
the amplification is needed at finitely many pairs of levels only, and a small `c` gives it. -/
theorem factTower_linearDichotomy : factTower.LinearDichotomy := by
  intro C _
  obtain ⟨N, hN⟩ := exists_nat_ge C
  set W : ℝ := ∑ m ∈ range N, factTower.width m with hW
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun m _ => (factTower.width_pos m).le
  refine ⟨1 / (W + 1), by positivity, 1, zero_le_one, fun k n => ?_⟩
  by_cases hkn : k + n < N
  · left
    have hw : factTower.width (k + n) ≤ W :=
      Finset.single_le_sum (f := fun m => factTower.width m)
        (fun m _ => (factTower.width_pos m).le) (Finset.mem_range.mpr hkn)
    have hc : 1 / (W + 1) * factTower.width (k + n) ≤ 1 := by
      rw [one_div, inv_mul_le_iff₀ (by positivity)]
      linarith
    have hp : (0 : ℝ) ≤ (factTower.period k n : ℝ) := Nat.cast_nonneg _
    have hwk := factTower.width_pos k
    unfold Amplifies
    nlinarith [mul_le_mul_of_nonneg_left hc hp]
  · right
    have hm : C ≤ ((k + n : ℕ) : ℝ) + 2 := by
      have : (N : ℝ) ≤ ((k + n : ℕ) : ℝ) := by exact_mod_cast not_lt.mp hkn
      linarith
    unfold Jumps
    show C * (((k + n + 1).factorial : ℕ) : ℝ) ≤ (((k + n + 1 + 1).factorial : ℕ) : ℝ)
    have e : (k + n + 1 + 1).factorial = (k + n + 2) * (k + n + 1).factorial :=
      Nat.factorial_succ (k + n + 1)
    rw [e]
    push_cast
    have hpos : (0 : ℝ) < (((k + n + 1).factorial : ℕ) : ℝ) := by
      exact_mod_cast Nat.factorial_pos _
    have hm' : C ≤ (k : ℝ) + n + 2 := by push_cast at hm; linarith
    exact mul_le_mul_of_nonneg_right hm' hpos.le

theorem factTower_not_bounded : ¬ factTower.APrioriBounds := by
  rintro ⟨B, hB⟩
  have h1 : (((⌈B⌉₊ + 1).factorial : ℕ) : ℝ) ≤ B := hB ⌈B⌉₊
  have h2 : (⌈B⌉₊ : ℝ) + 1 ≤ (((⌈B⌉₊ + 1).factorial : ℕ) : ℝ) := by
    exact_mod_cast Nat.self_le_factorial (⌈B⌉₊ + 1)
  have h3 := Nat.le_ceil B
  linarith

/-- **A uniform growth bound is needed even with a linear error.** There is a tower that
satisfies the Teichmüller contraction and the dichotomy with a linear error, with finitely
many pairs of levels where the amplification is used for each threshold, and has unbounded
degeneration: the jump alternative cannot be excluded without a growth bound that is uniform
in the relative period. -/
theorem exists_unbounded_of_teichmuller_linearDichotomy :
    ∃ T : WidthTower, T.Teichmuller ∧ T.LinearDichotomy ∧ ¬ T.APrioriBounds :=
  ⟨factTower, factTower_teichmuller, factTower_linearDichotomy, factTower_not_bounded⟩

/-- **Both uniformities of Problem 4.3 are necessary in the recursion.** A uniform growth bound
with a dichotomy whose error is not linear in the period gives no a priori bounds, and neither
does the Teichmüller contraction, with a growth bound that depends on the relative period,
with a linear error: `aPrioriBounds_of_uniform` needs both. -/
theorem uniformities_necessary :
    (∃ T : WidthTower, T.GrowthBound 2 ∧ T.Dichotomy ∧ ¬ T.APrioriBounds) ∧
      (∃ T : WidthTower, T.Teichmuller ∧ T.LinearDichotomy ∧ ¬ T.APrioriBounds) :=
  ⟨exists_unbounded_of_growth_dichotomy, exists_unbounded_of_teichmuller_linearDichotomy⟩

end WidthTower

/-- A degeneration bound `B` gives a return budget with constant loss: every level contributes
the collar `1/B`, so the accumulated modulus is `n/B`. -/
def ReturnBudget.ofBound (B : ℝ) (hB : 0 < B) : ReturnBudget where
  degree := fun _ => 1
  distortion := fun _ => 1
  collar := fun _ => 1 / B
  attenuation := fun _ => 1
  injection := fun _ => 1 / B
  modulus := fun n => (n : ℝ) / B
  degree_pos := fun _ => one_pos
  distortion_ge_one := fun _ => le_rfl
  collar_pos := fun _ => by positivity
  attenuation_nonneg := fun _ => zero_le_one
  initial_nonneg := by simp
  injection_ge := fun _ => by simp
  step := fun n => by
    simp only [one_mul]
    push_cast
    rw [add_div]

theorem ReturnBudget.ofBound_linearLossControl (B : ℝ) (hB : 0 < B) :
    (ReturnBudget.ofBound B hB).LinearLossControl := by
  refine ⟨1 / B, by positivity, 1, one_pos, fun _ => le_rfl, fun n => ?_⟩
  simp only [ReturnBudget.loss, ReturnBudget.ofBound, mul_one, one_mul]
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

end

end MLC.Research
