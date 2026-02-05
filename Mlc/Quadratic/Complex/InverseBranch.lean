import Mlc.Quadratic.Complex.PuzzleBoundaryMotion
import Mathlib.Topology.Basic

namespace MLC
namespace Quadratic

open Topology Set
open Classical

universe u v

variable {α : Type u} {β : Type v}

/-- A (local) inverse branch of a map `f` on a set `S`. -/
structure InverseBranch (f : α → β) (S : Set β) where
  (toFun : S → α)
  (right_inv : ∀ y : S, f (toFun y) = y)

/-- `f` admits a right inverse on `S`. -/
def HasRightInverseOn (f : α → β) (S : Set β) : Prop :=
  ∃ g : S → α, ∀ y : S, f (g y) = y

/-- `f` admits a left inverse on `T` with values in `S`. -/
def HasLeftInverseOn (f : α → β) (S : Set β) (T : Set α) : Prop :=
  ∃ g : β → α, (∀ x ∈ T, g (f x) = x) ∧ (∀ y ∈ S, g y ∈ T)

/-- A right inverse gives a right inverse on the range. -/
lemma hasRightInverseOn_range (f : α → β) : HasRightInverseOn f (Set.range f) := by
  refine ⟨fun y => Classical.choose y.2, ?_⟩
  intro y
  rcases y.2 with ⟨x, hx⟩
  have hx' : f (Classical.choose y.2) = y := by
    have := Classical.choose_spec y.2
    simpa [hx] using this
  exact hx'

/-- A right inverse on `S` gives surjectivity onto `S`. -/
lemma surj_of_hasRightInverseOn {f : α → β} {S : Set β}
    (h : HasRightInverseOn f S) : S ⊆ Set.range f := by
  intro y hy
  rcases h with ⟨g, hg⟩
  refine ⟨g ⟨y, hy⟩, ?_⟩
  simpa using (hg ⟨y, hy⟩)

/-- A left inverse on `T` gives injectivity on `T`. -/
lemma injOn_of_hasLeftInverseOn {f : α → β} {S : Set β} {T : Set α}
    (h : HasLeftInverseOn f S T) : Set.InjOn f T := by
  rcases h with ⟨g, h_left, _⟩
  intro x hx y hy hxy
  calc
    x = g (f x) := (h_left x hx).symm
    _ = g (f y) := by simpa [hxy]
    _ = y := h_left y hy

/-- Coercion to a right inverse on `S` from `InverseBranch`. -/
lemma inverseBranch_hasRightInverseOn {f : α → β} {S : Set β}
    (g : InverseBranch f S) : HasRightInverseOn f S := by
  refine ⟨g.toFun, ?_⟩
  intro y
  exact g.right_inv y

end Quadratic
end MLC
