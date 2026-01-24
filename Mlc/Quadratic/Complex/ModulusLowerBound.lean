import Yoccoz.Yoccoz
import Mlc.AxiomsMainConjecture

namespace MLC

namespace Quadratic

open Complex Topology Set Filter

noncomputable section

/-!
Reductions around puzzle-annulus moduli.

These lemmas are independent of the Molecule Conjecture bridge: they package the
standard implication

  (uniform positive lower bound on moduli) => (moduli not summable) =>
  (dynamical pieces shrink by Yoccoz) => (parameter pieces shrink).

They will be used once we connect satellite renormalization bounds to puzzle-annulus
modulus bounds.
-/

theorem not_summable_modulus_of_lower_bound (c : ℂ) {m : ℝ}
    (hm : 0 < m) (h : ∀ n : ℕ, m ≤ modulus (PuzzleAnnulus c n)) :
    ¬ Summable (fun n => modulus (PuzzleAnnulus c n)) := by
  intro hs
  have h0 : Tendsto (fun n => modulus (PuzzleAnnulus c n)) atTop (𝓝 (0 : ℝ)) :=
    hs.tendsto_atTop_zero
  have hlt : ∀ᶠ n in atTop, modulus (PuzzleAnnulus c n) < m / 2 :=
    (tendsto_order.1 h0).2 (m / 2) (by linarith)
  have hge : ∀ᶠ n in atTop, m ≤ modulus (PuzzleAnnulus c n) :=
    Filter.Eventually.of_forall h
  rcases (hge.and hlt).exists with ⟨n, hn_ge, hn_lt⟩
  linarith

theorem dynamical_shrink_of_modulus_lower_bound (c : ℂ) {m : ℝ}
    (hm : 0 < m) (h : ∀ n : ℕ, m ≤ modulus (PuzzleAnnulus c n)) :
    (⋂ n, DynamicalPuzzlePiece c n 0) = {0} := by
  apply MLC.yoccoz_theorem
  exact not_summable_modulus_of_lower_bound c hm h

theorem parameter_shrink_of_modulus_lower_bound (c : ℂ) (hc : c ∈ MandelbrotSet) {m : ℝ}
    (hm : 0 < m) (h : ∀ n : ℕ, m ≤ modulus (PuzzleAnnulus c n)) :
    (⋂ n, ParaPuzzlePieceAt c n) = {c} := by
  have h_dyn : (⋂ n, DynamicalPuzzlePiece c n 0) = {0} :=
    dynamical_shrink_of_modulus_lower_bound c hm h
  have h_fin : FinitelyRenormalizable c := by
    -- `FinitelyRenormalizable` is `¬ Summable ...`.
    exact not_summable_modulus_of_lower_bound c hm h
  exact parameter_shrink_of_yoccoz c hc h_fin h_dyn

end

end Quadratic

end MLC
