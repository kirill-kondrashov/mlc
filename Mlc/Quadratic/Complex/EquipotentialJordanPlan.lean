import Mlc.Quadratic.Complex.BottcherMotion
import Mlc.Quadratic.Complex.Equipotential
import Mlc.Quadratic.Complex.JordanBasics

namespace MLC.Quadratic

open Complex Topology Set

noncomputable section

/-!
Plan for proving equipotential Jordan curve data.

This file records the missing analytic inputs needed to derive
`equipotential_jordan_data` from Böttcher coordinates and Green function facts.
It is not imported by the main development yet.
-/

/-- Böttcher coordinates relate the Green function to the norm (placeholder hypothesis). -/
lemma green_function_eq_log_norm_bottcher (B : BottcherData) (c z : ℂ)
    (h : green_function c z = Real.log ‖B.phi c z‖) :
    green_function c z = Real.log ‖B.phi c z‖ := by
  exact h

/-- The equipotential is the preimage of a Euclidean circle (placeholder hypothesis). -/
lemma equipotential_eq_bottcher_circle (B : BottcherData) (c : ℂ) (n : ℕ)
    (h : Equipotential c n = {z | ‖B.phi c z‖ = (1 / 2 : ℝ) ^ n}) :
    Equipotential c n = {z | ‖B.phi c z‖ = (1 / 2 : ℝ) ^ n} := by
  exact h

/-- Continuity of the Böttcher coordinate in `z` (placeholder hypothesis). -/
lemma bottcher_continuous (B : BottcherData) (c : ℂ)
    (hcont : Continuous (B.phi c)) :
    Continuous (B.phi c) := by
  exact hcont

/-- Placeholder: Böttcher coordinates are injective on the unit parameter disk. -/
lemma bottcher_inj (B : BottcherData) {c : ℂ} (hc : c ∈ Metric.ball 0 1) :
    Set.InjOn (B.phi c) Set.univ := by
  simpa using (B.inj_on c hc)

/-- Equipotentials are Jordan curves via Böttcher coordinates (placeholder hypothesis). -/
lemma equipotential_jordan_curve_of_bottcher (_B : BottcherData) (c : ℂ) (n : ℕ)
    (h : ∃ γ : ℝ → ℂ, JordanCurve γ ∧ JordanCurveImage γ = Equipotential c n) :
    ∃ γ : ℝ → ℂ, JordanCurve γ ∧ JordanCurveImage γ = Equipotential c n := by
  exact h

/-- Equipotential Jordan data derived from Böttcher coordinates (placeholder hypothesis). -/
lemma equipotential_jordan_data_of_bottcher (_B : BottcherData) (c : ℂ) (n : ℕ)
    (h : ∃ γ : ℝ → ℂ,
      JordanCurve γ ∧
        JordanCurveImage γ = Equipotential c n ∧
        JordanInterior γ ⊆ GreenSublevel c n ∧
        connectedComponentIn (GreenSublevelClosed c n) 0 ⊆
          Set.compl (Equipotential c n)) :
    ∃ γ : ℝ → ℂ,
      JordanCurve γ ∧
        JordanCurveImage γ = Equipotential c n ∧
        JordanInterior γ ⊆ GreenSublevel c n ∧
        connectedComponentIn (GreenSublevelClosed c n) 0 ⊆
          Set.compl (Equipotential c n) := by
  exact h

end

end MLC.Quadratic
