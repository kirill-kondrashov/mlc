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

lemma boundaryArc_carrier_nonempty (γ : MLC.Quadratic.BoundaryArc) :
    γ.carrier.Nonempty := by
  refine ⟨γ ⟨0, by norm_num, by norm_num⟩, ?_⟩
  exact ⟨_, rfl⟩

def reachableCarrier
    (B : MLC.Quadratic.FiniteEmbeddedBoundaryGraph) (u : BoundaryVertex B) : Set ℂ :=
  ⋃ v : {v : BoundaryVertex B // (boundaryIncidenceGraph B).Reachable u v},
    (v.1.1).carrier

def unreachableCarrier
    (B : MLC.Quadratic.FiniteEmbeddedBoundaryGraph) (u : BoundaryVertex B) : Set ℂ :=
  ⋃ v : {v : BoundaryVertex B //
      ¬ (boundaryIncidenceGraph B).Reachable u v},
    (v.1.1).carrier

lemma reachableCarrier_subset (B : MLC.Quadratic.FiniteEmbeddedBoundaryGraph)
    (u : BoundaryVertex B) :
    reachableCarrier B u ⊆ B.carrier := by
  intro z hz
  rcases Set.mem_iUnion.1 hz with ⟨v, hz⟩
  exact (B.mem_carrier_iff).2 ⟨v.1.1, v.1.2, hz⟩

lemma unreachableCarrier_subset (B : MLC.Quadratic.FiniteEmbeddedBoundaryGraph)
    (u : BoundaryVertex B) :
    unreachableCarrier B u ⊆ B.carrier := by
  intro z hz
  rcases Set.mem_iUnion.1 hz with ⟨v, hz⟩
  exact (B.mem_carrier_iff).2 ⟨v.1.1, v.1.2, hz⟩

lemma reachableCarrier_union_unreachableCarrier
    (B : MLC.Quadratic.FiniteEmbeddedBoundaryGraph) (u : BoundaryVertex B) :
    reachableCarrier B u ∪ unreachableCarrier B u = B.carrier := by
  ext z
  constructor
  · rintro (hz | hz)
    · exact reachableCarrier_subset B u hz
    · exact unreachableCarrier_subset B u hz
  · intro hz
    rcases (B.mem_carrier_iff).1 hz with ⟨γ, hγ, hzγ⟩
    let v : BoundaryVertex B := ⟨γ, hγ⟩
    by_cases hv : (boundaryIncidenceGraph B).Reachable u v
    · left
      exact Set.mem_iUnion.2 ⟨⟨v, hv⟩, hzγ⟩
    · right
      exact Set.mem_iUnion.2 ⟨⟨v, hv⟩, hzγ⟩

lemma disjoint_reachableCarrier_unreachableCarrier
    (B : MLC.Quadratic.FiniteEmbeddedBoundaryGraph) (u : BoundaryVertex B) :
    Disjoint (reachableCarrier B u) (unreachableCarrier B u) := by
  refine Set.disjoint_left.2 ?_
  intro z hzR hzU
  rcases Set.mem_iUnion.1 hzR with ⟨w, hzw⟩
  rcases Set.mem_iUnion.1 hzU with ⟨x, hzx⟩
  by_cases hwx : w.1 = x.1
  · apply x.2
    exact hwx ▸ w.2
  · have hadj : (boundaryIncidenceGraph B).Adj w.1 x.1 :=
      ⟨hwx, ⟨z, hzw, hzx⟩⟩
    exact x.2 (w.2.trans hadj.reachable)

theorem boundaryIncidenceGraph_connected_of_carrier_connected
    (B : MLC.Quadratic.FiniteEmbeddedBoundaryGraph)
    (hcarrier : IsConnected B.carrier) :
    (boundaryIncidenceGraph B).Connected := by
  classical
  have hcarrier_ne : B.carrier.Nonempty := hcarrier.nonempty
  obtain ⟨z, hz⟩ := hcarrier_ne
  obtain ⟨γ, hγ, hzγ⟩ := (B.mem_carrier_iff).1 hz
  let u : BoundaryVertex B := ⟨γ, hγ⟩
  have hpre : (boundaryIncidenceGraph B).Preconnected := by
    intro v w
    by_contra hnot
    have hwu : ¬ (boundaryIncidenceGraph B).Reachable v w := hnot
    let R := reachableCarrier B v
    let U := unreachableCarrier B v
    have hRclosed : IsClosed R := by
      dsimp [R, reachableCarrier]
      exact isClosed_iUnion_of_finite (fun x =>
        MLC.Quadratic.BoundaryArc.isClosed_carrier x.1.1)
    have hUclosed : IsClosed U := by
      dsimp [U, unreachableCarrier]
      exact isClosed_iUnion_of_finite (fun x =>
        MLC.Quadratic.BoundaryArc.isClosed_carrier x.1.1)
    have hdisj : Disjoint R U := by
      exact disjoint_reachableCarrier_unreachableCarrier B v
    have hcover : B.carrier ⊆ Uᶜ ∪ Rᶜ := by
      intro x hx
      by_cases hxR : x ∈ R
      · exact Or.inl (show x ∈ Uᶜ from
          fun hxU => (Set.disjoint_left.1 hdisj) hxR hxU)
      · exact Or.inr (show x ∈ Rᶜ from hxR)
    have hsep := (isPreconnected_iff_subset_of_disjoint.mp hcarrier.isPreconnected
      Uᶜ Rᶜ hUclosed.isOpen_compl hRclosed.isOpen_compl hcover (by
        rw [Set.eq_empty_iff_forall_notMem]
        intro x hx
        rcases ((reachableCarrier_union_unreachableCarrier B v).symm ▸ hx.1) with
          hxR | hxU
        · exact hx.2.2 hxR
        · exact hx.2.1 hxU))
    rcases hsep with hU | hR
    · have hRne : R.Nonempty := by
        refine ⟨v.1.1 (⟨0, by norm_num, by norm_num⟩), ?_⟩
        exact Set.mem_iUnion.2 ⟨⟨v, .refl v⟩, ⟨_, rfl⟩⟩
      have hUne : U.Nonempty := by
        refine ⟨w.1.1 (⟨0, by norm_num, by norm_num⟩), ?_⟩
        exact Set.mem_iUnion.2 ⟨⟨w, hwu⟩, ⟨_, rfl⟩⟩
      exact hUne.elim (fun x hx => (hU (unreachableCarrier_subset B v hx)) hx)
    · have hUne : U.Nonempty := by
        refine ⟨w.1.1 (⟨0, by norm_num, by norm_num⟩), ?_⟩
        exact Set.mem_iUnion.2 ⟨⟨w, hwu⟩, ⟨_, rfl⟩⟩
      have hRne : R.Nonempty := by
        refine ⟨v.1.1 (⟨0, by norm_num, by norm_num⟩), ?_⟩
        exact Set.mem_iUnion.2 ⟨⟨v, .refl v⟩, ⟨_, rfl⟩⟩
      exact hRne.elim (fun x hx => (hR (reachableCarrier_subset B v hx)) hx)
  exact { preconnected := hpre, nonempty := ⟨u⟩ }

theorem boundaryCarrier_connected_of_incidenceGraph_connected
    (B : MLC.Quadratic.FiniteEmbeddedBoundaryGraph)
    (hconnected : (boundaryIncidenceGraph B).Connected) :
    IsConnected B.carrier := by
  letI := hconnected.nonempty
  have hunion :
      (⋃ v : BoundaryVertex B, v.1.carrier) = B.carrier := by
    ext z
    constructor
    · intro hz
      rcases Set.mem_iUnion.1 hz with ⟨v, hz⟩
      exact (B.mem_carrier_iff).2 ⟨v.1, v.2, hz⟩
    · intro hz
      rcases (B.mem_carrier_iff).1 hz with ⟨γ, hγ, hzγ⟩
      exact Set.mem_iUnion.2 ⟨⟨γ, hγ⟩, hzγ⟩
  have hconn :
      IsConnected (⋃ v : BoundaryVertex B, v.1.carrier) :=
    IsConnected.iUnion_of_reflTransGen
      (fun v => by
        rw [v.1.carrier_eq_image]
        exact isConnected_univ.image v.1.toFun v.1.continuous_toFun.continuousOn)
      (fun v w => by
        exact Relation.ReflTransGen.mono
          (r := (boundaryIncidenceGraph B).Adj)
          (p := fun x y => (x.1.carrier ∩ y.1.carrier).Nonempty)
          (fun x y hxy => hxy.2)
          ((SimpleGraph.reachable_iff_reflTransGen v w).1 (hconnected v w)))
  rwa [hunion] at hconn

theorem boundaryIncidenceGraph_connected_iff_carrier_connected
    (B : MLC.Quadratic.FiniteEmbeddedBoundaryGraph) :
    (boundaryIncidenceGraph B).Connected ↔ IsConnected B.carrier :=
  ⟨boundaryCarrier_connected_of_incidenceGraph_connected B,
    boundaryIncidenceGraph_connected_of_carrier_connected B⟩

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

/-- Exact frozen-target consumer for the finite incidence bridge.  This is a
conditional theorem: the bridge and graph connectivity are the remaining
geometric inputs, while nonemptiness of the target follows from the base
parameter `c`. -/
theorem green_sublevel_translate_inter_mandelbrot_connected_of_incidenceMotiveBridge
    (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet) (n : ℕ)
    (_hstraddle :
      ¬ ({c' | MLC.Quadratic.green_function c (c' - c) <
          (1 / 2 : ℝ) ^ n} ⊆ MLC.Quadratic.MandelbrotSet))
    (G : SimpleGraph V) (hG : G.Connected)
    (hbridge : IncidenceMotiveBridge
      (greenSublevelTranslateInterMandelbrot c n) G) :
    IsConnected (greenSublevelTranslateInterMandelbrot c n) := by
  have hcQ : c ∈ greenSublevelTranslateInterMandelbrot c n := by
    refine ⟨?_, hc⟩
    change MLC.Quadratic.green_function c (c - c) < (1 / 2 : ℝ) ^ n
    have h0 : MLC.Quadratic.green_function c 0 < (1 / 2 : ℝ) ^ n := by
      simpa only [MLC.Quadratic.GreenSublevel, Set.mem_setOf_eq] using
        (MLC.Quadratic.green_sublevel_contains_0 c n hc)
    simpa [sub_self] using h0
  letI : Nonempty (greenSublevelTranslateInterMandelbrot c n) :=
    ⟨⟨c, hcQ⟩⟩
  rw [isConnected_iff_connectedSpace]
  exact connectedSpace_of_incidenceMotiveBridge G hG hbridge

/-- Concrete boundary-graph specialization of the exact frozen-target
consumer.  Once an independent finite boundary carrier and its conservative
bridge are supplied, the preceding graph theorem discharges the target
connectivity. -/
theorem green_sublevel_translate_inter_mandelbrot_connected_of_boundaryIncidenceMotiveBridge
    (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet) (n : ℕ)
    (_hstraddle :
      ¬ ({c' | MLC.Quadratic.green_function c (c' - c) <
          (1 / 2 : ℝ) ^ n} ⊆ MLC.Quadratic.MandelbrotSet))
    (B : MLC.Quadratic.FiniteEmbeddedBoundaryGraph)
    (hcarrier : IsConnected B.carrier)
    (hbridge : IncidenceMotiveBridge
      (greenSublevelTranslateInterMandelbrot c n)
      (boundaryIncidenceGraph B)) :
    IsConnected (greenSublevelTranslateInterMandelbrot c n) :=
  green_sublevel_translate_inter_mandelbrot_connected_of_incidenceMotiveBridge
    c hc n _hstraddle (boundaryIncidenceGraph B)
    (boundaryIncidenceGraph_connected_of_carrier_connected B hcarrier) hbridge

end

end MLC.Motivic
