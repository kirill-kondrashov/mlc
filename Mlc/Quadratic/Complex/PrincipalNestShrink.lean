import Yoccoz.Quadratic.Complex.Groetzsch
import Yoccoz.Quadratic.Complex.PuzzleLemmas
import Mlc.Quadratic.Complex.PrincipalNestAnnulus

namespace MLC

namespace Quadratic

open Complex Topology Set Filter MeasureTheory

set_option linter.unnecessarySimpa false

noncomputable section

namespace PrincipalNest

lemma isOpen_dynamicalPuzzlePiece (c : ℂ) (n : ℕ) :
    IsOpen (DynamicalPuzzlePiece c n 0) := by
  have h_base : IsOpen {w | green_function c w < (1 / 2) ^ n} :=
    IsOpen.preimage (continuous_green_function c) isOpen_Iio
  simpa [DynamicalPuzzlePiece] using IsOpen.connectedComponentIn h_base

lemma nullMeasurable_dynamicalPuzzlePiece (c : ℂ) (n : ℕ) :
    MeasureTheory.NullMeasurableSet (DynamicalPuzzlePiece c n 0) MeasureTheory.volume := by
  exact (isOpen_dynamicalPuzzlePiece c n).measurableSet.nullMeasurableSet

lemma isConnected_dynamicalPuzzlePiece (c : ℂ) (hc : c ∈ MandelbrotSet) (n : ℕ) :
    IsConnected (DynamicalPuzzlePiece c n 0) := by
  have h_ne : (DynamicalPuzzlePiece c n 0).Nonempty :=
    ⟨0, mem_dynamical_puzzle_piece_self c hc n⟩
  refine ⟨h_ne, ?_⟩
  -- Connected components are preconnected.
  simpa [DynamicalPuzzlePiece] using (isPreconnected_connectedComponentIn : IsPreconnected (connectedComponentIn _ (0 : ℂ)))

/--
If the moduli of the principal nest annuli are not summable, the principal dynamical nest
shrinks to `{0}` (Grötzsch criterion).
-/
theorem dyn_iInter_eq_singleton_zero_of_not_summable_modulus
    (c : ℂ) (hc : c ∈ MandelbrotSet) (depths : ℕ → ℕ)
    (hmono : Monotone depths)
    (h_div : ¬ Summable (fun n => modulus (dynAnnulus c depths n))) :
    (⋂ n, dyn c depths n) = {0} := by
  -- Apply Groetzsch to the nested family `P n = DynamicalPuzzlePiece c (depths n) 0`.
  let P : ℕ → Set ℂ := fun n => DynamicalPuzzlePiece c (depths n) 0
  have h_nested : ∀ n, P (n + 1) ⊆ P n := by
    intro n
    -- `depths n ≤ depths (n+1)` and `DynamicalPuzzlePiece` is antitone in depth.
    have hle : depths n ≤ depths (n + 1) := hmono (Nat.le_succ n)
    exact (PrincipalNest.antitone_dynamicalPuzzlePiece c hle)
  have h_zero : ∀ n, 0 ∈ P n := by
    intro n
    exact mem_dynamical_puzzle_piece_self c hc (depths n)
  have h_conn : ∀ n, IsConnected (P n) := by
    intro n
    exact isConnected_dynamicalPuzzlePiece c hc (depths n)
  have h_meas : ∀ n, NullMeasurableSet (P n) volume := by
    intro n
    exact nullMeasurable_dynamicalPuzzlePiece c (depths n)
  have h_div' : ¬ Summable (fun n => modulus (P n \ P (n + 1))) := by
    simpa [P, dynAnnulus] using h_div
  -- Now Groetzsch yields the intersection is `{0}`.
  simpa [dyn, P] using groetzsch_criterion (P := P) h_nested h_zero h_conn h_meas h_div'

/--
If `depths` is cofinal, shrinking of the principal dynamical nest implies shrinking of the full
Yoccoz dynamical puzzle nest.
-/
theorem dyn_iInter_all_eq_singleton_zero_of_cofinal
    (c : ℂ) (depths : ℕ → ℕ)
    (hcof : Cofinal depths)
    (h : (⋂ n, dyn c depths n) = {0}) :
    (⋂ n, DynamicalPuzzlePiece c n 0) = {0} := by
  -- Rewrite the principal intersection as the full intersection.
  have : (⋂ n, dyn c depths n) = ⋂ n, DynamicalPuzzlePiece c n 0 :=
    iInter_dyn_eq c depths hcof
  simpa [this] using h

/-- Dynamical shrink implies parameter-piece shrink (pure translation). -/
axiom para_iInter_eq_singleton_of_dyn_iInter_eq_singleton
    (c : ℂ) (h_dyn : (⋂ n, DynamicalPuzzlePiece c n 0) = {0}) :
    (⋂ n, ParaPuzzlePieceAt c n) = {c}

/--
If the moduli of the principal nest annuli are not summable, then the full parameter puzzle
nests shrink to `{c}`.
-/
theorem para_iInter_eq_singleton_of_principal_modulus_not_summable
    (c : ℂ) (hc : c ∈ MandelbrotSet) (depths : ℕ → ℕ)
    (hmono : Monotone depths) (hcof : Cofinal depths)
    (h_div : ¬ Summable (fun n => modulus (dynAnnulus c depths n))) :
    (⋂ n, ParaPuzzlePieceAt c n) = {c} := by
  have h_principal : (⋂ n, dyn c depths n) = {0} :=
    dyn_iInter_eq_singleton_zero_of_not_summable_modulus c hc depths hmono h_div
  have h_dyn : (⋂ n, DynamicalPuzzlePiece c n 0) = {0} :=
    dyn_iInter_all_eq_singleton_zero_of_cofinal c depths hcof h_principal
  exact para_iInter_eq_singleton_of_dyn_iInter_eq_singleton c h_dyn

end PrincipalNest

end

end Quadratic

end MLC
