import Mlc.ParaPuzzleConnectivity
import Mlc.MotivicIntersectionNoGo

/-!
# Categorical frontier contract for the straddling parameter piece

The intended endomorphism monoid below is
`π₀ End_{Mot^loc_E}(M_n(P))` for a finite marked model `P` and relative
coefficient category `E`.  The repository does not yet formalize those
infinity-categorical objects, so this file records the exact ring-level
contract they must satisfy.  It is a proposition and a conditional theorem,
not a new axiom.
-/

namespace MLC.Motivic

open Set
open Quadratic

noncomputable section

/-- A nontrivial idempotent in a multiplicative monoid with zero. -/
def NontrivialIdempotent (R : Type*) [MonoidWithZero R] : Prop :=
  ∃ e : R, e * e = e ∧ e ≠ 0 ∧ e ≠ 1

/-- The categorical content needed to rule out a clopen split.

`EndM` is intended to model the endomorphism ring of the selected relative
localizing motive. `characteristic` is the conservative realization of
integer-valued clopen characteristic functions as motive endomorphisms.
-/
structure SeparationReflectingIndecomposable (X : Type*) [TopologicalSpace X] where
  EndM : Type
  [endM : MonoidWithZero EndM]
  characteristic : integerValuedRealization X →* EndM
  reflects_clopen :
    ∀ (U : Set X) (hU : IsClopen U),
      U.Nonempty → Uᶜ.Nonempty →
      characteristic (clopenCharacteristic U hU) ≠ 0 ∧
        characteristic (clopenCharacteristic U hU) ≠ 1
  indecomposable : ¬ NontrivialIdempotent EndM

theorem connectedSpace_of_separationReflectingIndecomposable
    {X : Type*} [TopologicalSpace X] [Nonempty X]
    (hM : SeparationReflectingIndecomposable X) :
    ConnectedSpace X := by
  letI := hM.endM
  rw [connectedSpace_iff_clopen]
  refine ⟨inferInstance, ?_⟩
  intro U hU
  by_cases hUempty : U = ∅
  · exact Or.inl hUempty
  have hUnonempty : U.Nonempty :=
    Set.nonempty_iff_ne_empty.mpr hUempty
  by_cases hUcompempty : Uᶜ = ∅
  · right
    calc
      U = (Uᶜ)ᶜ := by simp
      _ = (∅ : Set X)ᶜ := by rw [hUcompempty]
      _ = Set.univ := by simp
  have hUcompnonempty : Uᶜ.Nonempty :=
    Set.nonempty_iff_ne_empty.mpr hUcompempty
  exfalso
  apply hM.indecomposable
  have hnontrivial :=
    hM.reflects_clopen U hU hUnonempty hUcompnonempty
  refine ⟨hM.characteristic (clopenCharacteristic U hU), ?_, hnontrivial.1,
    hnontrivial.2⟩
  calc
    hM.characteristic (clopenCharacteristic U hU) *
        hM.characteristic (clopenCharacteristic U hU) =
        hM.characteristic
          (clopenCharacteristic U hU * clopenCharacteristic U hU) := by
            symm
            exact hM.characteristic.map_mul _ _
    _ = hM.characteristic (clopenCharacteristic U hU) := by
      rw [clopenCharacteristic_idempotent U hU]

/-- The exact frozen target for the straddling parameter frontier. -/
def greenSublevelTranslateInterMandelbrot (c : ℂ) (n : ℕ) : Set ℂ :=
  {c' | green_function c (c' - c) < (1 / 2 : ℝ) ^ n} ∩ MandelbrotSet

/-- Non-axiomatic Lean frontier contract for the Efimov route.

For each straddling target, it asks for an independently defined realization
set `Q` with the exact target comparison and a separation-reflecting
indecomposable motive endomorphism object.  The contract is intentionally
unproved; declaring it does not add it to the root axiom graph.
-/
def GreenSublevelStraddlingMotivicFrontier : Prop :=
  ∀ (c : ℂ) (hc : c ∈ MandelbrotSet) (n : ℕ)
    (hstraddle :
      ¬ ({c' | green_function c (c' - c) < (1 / 2 : ℝ) ^ n}
        ⊆ MandelbrotSet)),
    ∃ Q : Set ℂ,
      Q = greenSublevelTranslateInterMandelbrot c n ∧
      Q.Nonempty ∧
      Nonempty (SeparationReflectingIndecomposable Q)

theorem green_sublevel_translate_inter_mandelbrot_connected_of_motivic_frontier
    (hM : GreenSublevelStraddlingMotivicFrontier) (c : ℂ)
    (hc : c ∈ MandelbrotSet) (n : ℕ)
    (hstraddle :
      ¬ ({c' | green_function c (c' - c) < (1 / 2 : ℝ) ^ n}
        ⊆ MandelbrotSet)) :
    IsConnected (greenSublevelTranslateInterMandelbrot c n) := by
  rcases hM c hc n hstraddle with ⟨Q, hQ, hQnonempty, ⟨hMotive⟩⟩
  rw [← hQ]
  letI : Nonempty Q := Set.nonempty_coe_sort.mpr hQnonempty
  rw [isConnected_iff_connectedSpace]
  exact connectedSpace_of_separationReflectingIndecomposable hMotive

theorem green_sublevel_translate_inter_mandelbrot_connected_straddling_of_motivic_frontier
    (hM : GreenSublevelStraddlingMotivicFrontier) (c : ℂ)
    (hc : c ∈ MandelbrotSet) (n : ℕ)
    (hstraddle :
      ¬ ({c' | green_function c (c' - c) < (1 / 2 : ℝ) ^ n}
        ⊆ MandelbrotSet)) :
    IsConnected
      ({c' | green_function c (c' - c) < (1 / 2 : ℝ) ^ n}
        ∩ MandelbrotSet) := by
  simpa [greenSublevelTranslateInterMandelbrot] using
    green_sublevel_translate_inter_mandelbrot_connected_of_motivic_frontier
      hM c hc n hstraddle

end

end MLC.Motivic
