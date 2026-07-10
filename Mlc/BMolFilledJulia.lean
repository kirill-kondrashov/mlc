import Molecule.BMol
import Mathlib.Topology.Connected.Basic

/-!
# Intrinsic BMol filled Julia foundation

This file introduces the intrinsic non-escaping / filled Julia set for a
`Molecule.BMol`, together with the minimal parameter-family shell needed to talk
about connectedness loci.
-/

open Set
open Complex
open Function

namespace Molecule

/-- The intrinsic non-escaping / filled Julia set of a quadratic-like map. -/
def filledJuliaSet (g : BMol) : Set ℂ :=
  {z : ℂ | ∀ n : ℕ, (g.f^[n]) z ∈ g.U}

@[simp] lemma mem_filledJuliaSet_iff (g : BMol) (z : ℂ) :
    z ∈ filledJuliaSet g ↔ ∀ n : ℕ, (g.f^[n]) z ∈ g.U := Iff.rfl

/-- The intrinsic filled Julia set is the intersection of all iterate preimages of `U`. -/
lemma filledJuliaSet_eq_iInter_preimage (g : BMol) :
    filledJuliaSet g = ⋂ n : ℕ, (g.f^[n]) ⁻¹' g.U := by
  ext z
  simp [filledJuliaSet]

/-- A quadratic-like map has connected filled Julia set. -/
def FilledJuliaConnected (g : BMol) : Prop :=
  IsConnected (filledJuliaSet g)

/-- A minimal parameter family with values in `BMol`. -/
structure BMolParameterFamily (α : Type*) where
  parameterSet : Set α
  map : α → BMol

namespace BMolParameterFamily

/-- The parameters whose intrinsic BMol filled Julia sets are connected. -/
def connectednessLocus {α : Type*} (F : BMolParameterFamily α) : Set α :=
  {a : α | a ∈ F.parameterSet ∧ FilledJuliaConnected (F.map a)}

@[simp] lemma mem_connectednessLocus_iff {α : Type*} (F : BMolParameterFamily α) (a : α) :
    a ∈ F.connectednessLocus ↔ a ∈ F.parameterSet ∧ FilledJuliaConnected (F.map a) := Iff.rfl

end BMolParameterFamily

end Molecule
