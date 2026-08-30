import Mlc.MotivicConnectednessFrontier
import Mlc.Quadratic.Complex.FiniteParapuzzleBoundary
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Finite incidence endomorphisms for the motivic frontier

Efimov's relative motive is not formalized in this repository.  This file
formalizes the finite algebraic shadow needed for the first motivic gate:
functions on a connected incidence graph that are constant along incidence
edges have no nontrivial idempotents.

The missing geometric input is isolated as `IncidenceMotiveBridge`: a
conservative map from continuous integer-valued functions on the parameter
locus to this incidence endomorphism ring.  No connectedness property is
included in the bridge data.
-/

namespace MLC.Motivic

open Set

noncomputable section

variable {V : Type}

/-- Functions that are constant along the edges of an incidence graph. -/
def incidenceCenter (G : SimpleGraph V) : Subring (V → ℤ) where
  carrier := {f | ∀ ⦃u v⦄, G.Adj u v → f u = f v}
  zero_mem' := by
    intro u v huv
    rfl
  one_mem' := by
    intro u v huv
    rfl
  add_mem' := by
    intro f g hf hg u v huv
    change f u + g u = f v + g v
    rw [hf huv, hg huv]
  neg_mem' := by
    intro f hf u v huv
    change -f u = -f v
    rw [hf huv]
  mul_mem' := by
    intro f g hf hg u v huv
    change f u * g u = f v * g v
    rw [hf huv, hg huv]

/-- The incidence endomorphism ring attached to a graph. -/
abbrev IncidenceEndomorphismRing (G : SimpleGraph V) : Type :=
  ↥(incidenceCenter G)

lemma incidence_eq_of_reachable
    {G : SimpleGraph V} {f : IncidenceEndomorphismRing G}
    {u v : V} (hpath : G.Reachable u v) :
    (f : V → ℤ) u = (f : V → ℤ) v := by
  rcases hpath with ⟨p⟩
  induction p with
  | nil => rfl
  | cons h p ih =>
      exact (f.2 h).trans ih

/-- A connected incidence graph has an indecomposable center. -/
theorem incidenceCenter_noNontrivialIdempotent
    (G : SimpleGraph V) (hG : G.Connected) :
    ¬ NontrivialIdempotent (IncidenceEndomorphismRing G) := by
  letI := hG.nonempty
  intro h
  rcases h with ⟨e, he_idem, he_zero, he_one⟩
  classical
  let v₀ : V := Classical.choice (inferInstance : Nonempty V)
  by_cases hv₀ : (e : V → ℤ) v₀ = 0
  · apply he_zero
    apply Subtype.ext
    funext v
    change (e : V → ℤ) v = 0
    calc
      (e : V → ℤ) v = (e : V → ℤ) v₀ :=
        (incidence_eq_of_reachable (hG v₀ v)).symm
      _ = 0 := hv₀
  · have hv₀_idem : ((e : V → ℤ) v₀) ^ 2 = (e : V → ℤ) v₀ := by
      have h_eval :=
        congrArg (fun q : IncidenceEndomorphismRing G => (q : V → ℤ) v₀) he_idem
      simpa [pow_two] using h_eval
    have hv₀_one : (e : V → ℤ) v₀ = 1 :=
      (eq_zero_or_one_of_sq_eq_self hv₀_idem).resolve_left hv₀
    apply he_one
    apply Subtype.ext
    funext v
    change (e : V → ℤ) v = 1
    calc
      (e : V → ℤ) v = (e : V → ℤ) v₀ :=
        (incidence_eq_of_reachable (hG v₀ v)).symm
      _ = 1 := hv₀_one

/-- The missing conservative comparison from parameter functions to incidence
endomorphisms.  Its fields contain no connectedness conclusion. -/
structure IncidenceMotiveBridge (X : Type*) [TopologicalSpace X]
    (G : SimpleGraph V) where
  characteristic :
    integerValuedRealization X →*
      IncidenceEndomorphismRing G
  reflects_clopen :
    ∀ (U : Set X) (hU : IsClopen U),
      U.Nonempty → Uᶜ.Nonempty →
      characteristic (clopenCharacteristic U hU) ≠ 0 ∧
        characteristic (clopenCharacteristic U hU) ≠ 1

/-- Vertices of a finite boundary graph, with the finiteness carried by the
underlying `Finset`. -/
abbrev BoundaryVertex (B : MLC.Quadratic.FiniteEmbeddedBoundaryGraph) : Type :=
  ↥B.arcs

instance boundaryVertexFintype
    (B : MLC.Quadratic.FiniteEmbeddedBoundaryGraph) :
    Fintype (BoundaryVertex B) :=
  Finset.Subtype.fintype B.arcs

/-- Two distinct marked boundary arcs are incident when their carriers meet. -/
def boundaryIncidenceGraph
    (B : MLC.Quadratic.FiniteEmbeddedBoundaryGraph) :
    SimpleGraph (BoundaryVertex B) where
  Adj u v := u ≠ v ∧ (u.1.carrier ∩ v.1.carrier).Nonempty
  symm := by
    intro u v huv
    exact ⟨Ne.symm huv.1, by simpa [inter_comm] using huv.2⟩
  loopless := by
    intro u huv
    exact huv.1 rfl

/-- The finite boundary incidence graph inherits the indecomposable-center
result once its attachment graph is shown connected. -/
theorem boundaryIncidence_noNontrivialIdempotent
    (B : MLC.Quadratic.FiniteEmbeddedBoundaryGraph)
    (hconnected : (boundaryIncidenceGraph B).Connected) :
    ¬ NontrivialIdempotent
      (IncidenceEndomorphismRing (boundaryIncidenceGraph B)) :=
  incidenceCenter_noNontrivialIdempotent (boundaryIncidenceGraph B) hconnected

/-- A conservative incidence bridge plus a connected finite graph implies
connectedness of the parameter space. -/
theorem connectedSpace_of_incidenceMotiveBridge
    {X : Type*} [TopologicalSpace X] [Nonempty X]
    (G : SimpleGraph V) (hG : G.Connected)
    (hbridge : IncidenceMotiveBridge X G) :
    ConnectedSpace X := by
  let hsep : SeparationReflectingIndecomposable X :=
    { EndM := IncidenceEndomorphismRing G
      characteristic := hbridge.characteristic
      reflects_clopen := hbridge.reflects_clopen
      indecomposable := incidenceCenter_noNontrivialIdempotent G hG }
  exact connectedSpace_of_separationReflectingIndecomposable hsep

end

end MLC.Motivic
