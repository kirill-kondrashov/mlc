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
proof stops, and Problem 4.3 asks for the uniform versions (`GrowthBound`, `UniformDichotomy`),
which the pseudo-Siegel disks are meant to supply.

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

/-- The dichotomy with an additive error that does not depend on the period. -/
def UniformDichotomy : Prop :=
  ∀ C : ℝ, 0 < C → ∃ c : ℝ, 0 < c ∧ ∃ E : ℝ,
    ∀ k n, T.Amplifies c (fun _ => E) k n ∨ T.Jumps C (k + n)

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
dichotomy with a period-independent error give a priori bounds for every tower, whatever
its relative periods are. -/
theorem aPrioriBounds_of_uniform {Δ : ℝ} (hG : T.GrowthBound Δ) (hD : T.UniformDichotomy) :
    T.APrioriBounds := by
  have hΔ := T.growth_pos hG
  obtain ⟨c, hc, E, hE⟩ := hD (Δ + 1) (by linarith)
  obtain ⟨n₀, -, hn₀⟩ := exists_two_le_mul_two_pow hc
  refine T.aPrioriBounds_of_amplification hn₀ (E := E) fun k => ?_
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
