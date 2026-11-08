import Mathlib.Analysis.PSeries
import Mathlib.Tactic

/-!
# Numerical part of M1

These are real inequalities, not a definition of conformal modulus.
The geometric realization of the data is the explicit research obligation.
-/

namespace MLC.Research

open Finset Filter Topology

noncomputable section

/-- The lower-bound bookkeeping for induced quadratic returns. -/
structure ReturnBudget where
  degree : ℕ → ℝ
  distortion : ℕ → ℝ
  collar : ℕ → ℝ
  attenuation : ℕ → ℝ
  injection : ℕ → ℝ
  modulus : ℕ → ℝ
  degree_pos : ∀ n, 0 < degree n
  distortion_ge_one : ∀ n, 1 ≤ distortion n
  collar_pos : ∀ n, 0 < collar n
  attenuation_nonneg : ∀ n, 0 ≤ attenuation n
  initial_nonneg : 0 ≤ modulus 0
  injection_ge : ∀ n, collar n / degree n ≤ injection n
  step : ∀ n, attenuation n * modulus n + injection n ≤ modulus (n + 1)

namespace ReturnBudget

variable (b : ReturnBudget)

def loss (n : ℕ) : ℝ := b.degree n * b.distortion n
def weight (n : ℕ) : ℝ := b.collar n / b.loss n
def cost (n : ℕ) : ℝ := b.modulus (n + 1) / b.distortion n
def partialCost (n : ℕ) : ℝ := ∑ j ∈ range n, b.cost j

theorem distortion_pos (n : ℕ) : 0 < b.distortion n :=
  lt_of_lt_of_le zero_lt_one (b.distortion_ge_one n)

theorem degree_ne_zero (n : ℕ) : b.degree n ≠ 0 := ne_of_gt (b.degree_pos n)

theorem distortion_ne_zero (n : ℕ) : b.distortion n ≠ 0 :=
  ne_of_gt (b.distortion_pos n)

theorem loss_pos (n : ℕ) : 0 < b.loss n :=
  mul_pos (b.degree_pos n) (b.distortion_pos n)

theorem weight_pos (n : ℕ) : 0 < b.weight n :=
  div_pos (b.collar_pos n) (b.loss_pos n)

theorem injection_pos (n : ℕ) : 0 < b.injection n :=
  lt_of_lt_of_le (div_pos (b.collar_pos n) (b.degree_pos n)) (b.injection_ge n)

theorem injection_nonneg (n : ℕ) : 0 ≤ b.injection n :=
  le_of_lt (b.injection_pos n)

theorem modulus_nonneg (n : ℕ) : 0 ≤ b.modulus n := by
  induction n with
  | zero => exact b.initial_nonneg
  | succ n ih =>
    exact le_trans (add_nonneg (mul_nonneg (b.attenuation_nonneg n) ih)
      (b.injection_nonneg n)) (b.step n)

theorem step_ge_injection (n : ℕ) : b.injection n ≤ b.modulus (n + 1) := by
  have h := mul_nonneg (b.attenuation_nonneg n) (b.modulus_nonneg n)
  exact le_trans (le_add_of_nonneg_left h) (b.step n)

theorem step_ge_collar_div_degree (n : ℕ) :
    b.collar n / b.degree n ≤ b.modulus (n + 1) :=
  (b.injection_ge n).trans (b.step_ge_injection n)

theorem cost_nonneg (n : ℕ) : 0 ≤ b.cost n :=
  div_nonneg (b.modulus_nonneg (n + 1)) (le_of_lt (b.distortion_pos n))

theorem weight_eq_iterated_div (n : ℕ) :
    b.weight n = (b.collar n / b.degree n) / b.distortion n := by
  simp only [weight, loss, div_div]

theorem cost_ge_weight (n : ℕ) : b.weight n ≤ b.cost n := by
  rw [b.weight_eq_iterated_div]
  exact div_le_div_of_nonneg_right (b.step_ge_collar_div_degree n)
    (le_of_lt (b.distortion_pos n))

theorem cost_pos (n : ℕ) : 0 < b.cost n :=
  (b.weight_pos n).trans_le (b.cost_ge_weight n)

theorem partialCost_zero : b.partialCost 0 = 0 := by simp [partialCost]

theorem partialCost_succ (n : ℕ) :
    b.partialCost (n + 1) = b.partialCost n + b.cost n := by
  simp [partialCost, sum_range_succ]

theorem partialCost_mono : Monotone b.partialCost := by
  apply monotone_nat_of_le_succ
  intro n
  rw [b.partialCost_succ]
  exact le_add_of_nonneg_right (b.cost_nonneg n)

theorem partialCost_ge_weights (n : ℕ) :
    (∑ j ∈ range n, b.weight j) ≤ b.partialCost n :=
  sum_le_sum fun j _ => b.cost_ge_weight j

/-- Allows unbounded total losses, provided they grow at most linearly in
the index of the induced return. No bound on all raw return times is imposed. -/
def LinearLossControl : Prop :=
  ∃ η > (0 : ℝ), ∃ C > (0 : ℝ),
    (∀ n, η ≤ b.collar n) ∧ (∀ n, b.loss n ≤ C * (n + 1))

def HarmonicControl : Prop :=
  ∃ ε > (0 : ℝ), ∀ n, ε / (n + 1) ≤ b.weight n

theorem weight_lower_of_linear_loss
    {η C : ℝ} (hη : 0 < η)
    (hcollar : ∀ n, η ≤ b.collar n)
    (hloss : ∀ n, b.loss n ≤ C * (n + 1)) (n : ℕ) :
    (η / C) / (n + 1) ≤ b.weight n := by
  calc
    (η / C) / (n + 1) = η / (C * (n + 1)) := by rw [div_div]
    _ ≤ η / b.loss n :=
      div_le_div_of_nonneg_left (le_of_lt hη) (b.loss_pos n) (hloss n)
    _ ≤ b.weight n :=
      div_le_div_of_nonneg_right (hcollar n) (le_of_lt (b.loss_pos n))

theorem harmonicControl_of_linearLossControl (h : b.LinearLossControl) :
    b.HarmonicControl := by
  obtain ⟨η, hη, C, hC, hc, hl⟩ := h
  exact ⟨η / C, div_pos hη hC, b.weight_lower_of_linear_loss hη hc hl⟩

theorem partialCost_ge_harmonic
    {ε : ℝ} (h : ∀ j, ε / (j + 1) ≤ b.weight j) (n : ℕ) :
    ε * (∑ j ∈ range n, (1 / (j + 1) : ℝ)) ≤ b.partialCost n := by
  calc
    ε * (∑ j ∈ range n, (1 / (j + 1) : ℝ)) =
        ∑ j ∈ range n, ε / (j + 1) := by simp [mul_sum, div_eq_mul_inv]
    _ ≤ ∑ j ∈ range n, b.weight j := sum_le_sum fun j _ => h j
    _ ≤ b.partialCost n := b.partialCost_ge_weights n

end ReturnBudget

/-- A cost has arbitrarily large finite partial sums. -/
def UnboundedBudget (cost : ℕ → ℝ) : Prop :=
  ∀ B : ℝ, ∃ n, B < ∑ j ∈ Finset.range n, cost j

theorem harmonic_partial_sums_unbounded (B : ℝ) :
    ∃ n, B < ∑ j ∈ Finset.range n, (1 / (j + 1) : ℝ) := by
  obtain ⟨n, hn⟩ := eventually_atTop.mp
    (Real.tendsto_sum_range_one_div_nat_succ_atTop.eventually
      (eventually_gt_atTop B))
  exact ⟨n, hn n le_rfl⟩

theorem ReturnBudget.unbounded_of_harmonicControl
    (b : ReturnBudget) (h : b.HarmonicControl) : UnboundedBudget b.cost := by
  obtain ⟨ε, hε, hweight⟩ := h
  intro B
  obtain ⟨n, hn⟩ := harmonic_partial_sums_unbounded (B / ε)
  refine ⟨n, ?_⟩
  have hmul : B < ε * (∑ j ∈ range n, (1 / (j + 1) : ℝ)) := by
    nlinarith [(div_lt_iff₀ hε).mp hn]
  exact hmul.trans_le (b.partialCost_ge_harmonic hweight n)

theorem ReturnBudget.unbounded_of_linearLossControl
    (b : ReturnBudget) (h : b.LinearLossControl) : UnboundedBudget b.cost :=
  b.unbounded_of_harmonicControl (b.harmonicControl_of_linearLossControl h)

end
end MLC.Research
