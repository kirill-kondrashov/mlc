import Mlc.Quadratic.Complex.BottcherMotion
import Mlc.Quadratic.Complex.BottcherOnM

namespace MLC

open Quadratic Complex Topology Set Filter

/-!
Outline stubs for `bottcher_onM_hyp`.

These lemmas are intentionally weak (mostly `True`) placeholders that keep
the file building while recording the eventual proof milestones.
The stronger analytic statements belong in a future theory file.
-/

lemma bottcher_coordinate_exists
    (_c : ℂ) :
    ∃ _φ : ℂ → ℂ,
      True := by
  -- Placeholder witness; the analytic statement will replace this.
  exact ⟨fun _ => 0, trivial⟩

lemma holomorphic_motion_external
    (_c₀ : ℂ) :
    True := by
  -- TODO: strengthen to a concrete holomorphic motion statement.
  trivial

lemma parameter_bottcher_identifies_outside_M :
    True := by
  -- TODO: formalize parameter Böttcher map identifying `ℂ \ M` with `|w| > 1`.
  trivial

lemma parameter_disk_stability
    (_c₀ : ℂ) :
    ∃ (r : ℕ → ℂ → ℝ),
      (∀ n c, 0 < r n c) := by
  -- TODO: strengthen to the parameter disk inclusion into `M`.
  refine ⟨fun _ _ => 1, ?_⟩
  intro n c
  norm_num

theorem bottcher_onM_hyp_theory :
    True := by
  -- TODO: assemble `BottcherOnMHyp` from the analytic construction.
  trivial

end MLC
