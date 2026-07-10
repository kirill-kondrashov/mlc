import Molecule.BMol
import Mlc.BMolFilledJulia

/-!
# Genuine BMol refinement

This file adds a small local compact-containment refinement over the vendored
`Molecule.BMol` representation, without modifying vendored dependencies.
-/

open Set
open Complex
open Function

namespace Molecule

/-- A set `U` is compactly contained in `V` in the ambient plane. -/
def IsCompactlyContainedIn (U V : Set ℂ) : Prop :=
  IsCompact (closure U) ∧ closure U ⊆ V

/-- A local refinement of `BMol` adding genuine compact containment. -/
structure GenuineBMol where
  toBMol : BMol
  compact_containment : IsCompactlyContainedIn toBMol.U toBMol.V

instance : Coe GenuineBMol BMol := ⟨GenuineBMol.toBMol⟩

@[simp] lemma genuineBMol_toBMol (g : GenuineBMol) :
    g.toBMol = (g : BMol) := rfl

lemma isCompact_closure_U (g : GenuineBMol) :
    IsCompact (closure g.toBMol.U) :=
  g.compact_containment.1

lemma closure_U_subset_V (g : GenuineBMol) :
    closure g.toBMol.U ⊆ g.toBMol.V :=
  g.compact_containment.2

/-- Build a genuine BMol from a vendored `BMol` plus compactness of `closure U`. -/
def mkOfIsCompactClosure (g : BMol) (hcompact : IsCompact (closure g.U)) : GenuineBMol where
  toBMol := g
  compact_containment := ⟨hcompact, g.closure_subset⟩

end Molecule
