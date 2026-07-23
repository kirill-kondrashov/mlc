import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Connected.LocallyConnected
import Mlc.Quadratic.Complex.ParaPuzzleBasis

open Set
open scoped Topology

namespace MLC.Quadratic

noncomputable section

structure BoundaryArc where
  toFun : Set.Icc (0 : ℝ) 1 → ℂ
  continuous_toFun : Continuous toFun
  inj_toFun : Function.Injective toFun

instance : DecidableEq BoundaryArc := Classical.decEq _

namespace BoundaryArc

instance : CoeFun BoundaryArc (fun _ => Set.Icc (0 : ℝ) 1 → ℂ) where
  coe γ := γ.toFun

def carrier (γ : BoundaryArc) : Set ℂ := Set.range γ.toFun

lemma carrier_eq_image (γ : BoundaryArc) :
    γ.carrier = γ.toFun '' (Set.univ : Set (Set.Icc (0 : ℝ) 1)) := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, mem_univ _, rfl⟩
  · rintro ⟨x, -, rfl⟩
    exact ⟨x, rfl⟩

lemma isCompact_carrier (γ : BoundaryArc) : IsCompact γ.carrier := by
  rw [γ.carrier_eq_image]
  simpa using (isCompact_univ.image γ.continuous_toFun)

lemma isClosed_carrier (γ : BoundaryArc) : IsClosed γ.carrier :=
  γ.isCompact_carrier.isClosed

end BoundaryArc

structure FiniteEmbeddedBoundaryGraph where
  arcs : Finset BoundaryArc

namespace FiniteEmbeddedBoundaryGraph

def carrier (G : FiniteEmbeddedBoundaryGraph) : Set ℂ :=
  ⋃ γ ∈ G.arcs, γ.carrier

lemma mem_carrier_iff (G : FiniteEmbeddedBoundaryGraph) {z : ℂ} :
    z ∈ G.carrier ↔ ∃ γ ∈ G.arcs, z ∈ γ.carrier := by
  simp [carrier]

def carrierFinset (s : Finset BoundaryArc) : Set ℂ :=
  ⋃ γ ∈ s, γ.carrier

lemma carrier_eq_carrierFinset (G : FiniteEmbeddedBoundaryGraph) : G.carrier = carrierFinset G.arcs := rfl

lemma carrierFinset_empty : carrierFinset (∅ : Finset BoundaryArc) = ∅ := by
  simp [carrierFinset]

lemma carrierFinset_insert (γ : BoundaryArc) (s : Finset BoundaryArc) :
    carrierFinset (insert γ s) = γ.carrier ∪ carrierFinset s := by
  ext z
  simp [carrierFinset]

lemma isClosed_carrierFinset (s : Finset BoundaryArc) : IsClosed (carrierFinset s) := by
  classical
  refine Finset.induction_on s ?base ?step
  · simpa [carrierFinset_empty] using isClosed_empty
  · intro γ s _ hs
    simpa [carrierFinset_insert] using γ.isClosed_carrier.union hs

lemma isClosed_carrier (G : FiniteEmbeddedBoundaryGraph) : IsClosed G.carrier := by
  simpa [carrier_eq_carrierFinset] using isClosed_carrierFinset G.arcs

lemma isOpen_compl_carrier (G : FiniteEmbeddedBoundaryGraph) : IsOpen G.carrierᶜ :=
  G.isClosed_carrier.isOpen_compl

def window (G : FiniteEmbeddedBoundaryGraph) (z₀ : ℂ) : Set ℂ :=
  connectedComponentIn G.carrierᶜ z₀

lemma mem_window (G : FiniteEmbeddedBoundaryGraph) {z₀ : ℂ} (hz₀ : z₀ ∈ G.carrierᶜ) :
    z₀ ∈ G.window z₀ :=
  mem_connectedComponentIn hz₀

lemma isOpen_window (G : FiniteEmbeddedBoundaryGraph) (z₀ : ℂ) :
    IsOpen (G.window z₀) := by
  letI : LocallyConnectedSpace ℂ := complex_locally_connected
  simpa [window] using G.isOpen_compl_carrier.connectedComponentIn

lemma window_subset_compl_carrier (G : FiniteEmbeddedBoundaryGraph) (z₀ : ℂ) :
    G.window z₀ ⊆ G.carrierᶜ :=
  connectedComponentIn_subset _ _

lemma window_subset_window_of_carrier_subset {G H : FiniteEmbeddedBoundaryGraph} {z₀ : ℂ}
    (hsub : G.carrier ⊆ H.carrier)
    (_hzG : z₀ ∈ G.carrierᶜ)
    (hzH : z₀ ∈ H.carrierᶜ) :
    H.window z₀ ⊆ G.window z₀ := by
  have hcomp : H.carrierᶜ ⊆ G.carrierᶜ := by
    intro z hz hzG'
    exact hz (hsub hzG')
  have hsubset : H.window z₀ ⊆ G.carrierᶜ := by
    exact Set.Subset.trans (window_subset_compl_carrier H z₀) hcomp
  exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
    (mem_window H hzH) hsubset

end FiniteEmbeddedBoundaryGraph

structure FiniteEmbeddedBoundaryGraphFamily where
  graph : ℕ → FiniteEmbeddedBoundaryGraph

namespace FiniteEmbeddedBoundaryGraphFamily

def window (F : FiniteEmbeddedBoundaryGraphFamily) (n : ℕ) (z₀ : ℂ) : Set ℂ :=
  (F.graph n).window z₀

lemma isOpen_window (F : FiniteEmbeddedBoundaryGraphFamily) (n : ℕ) (z₀ : ℂ) :
    IsOpen (F.window n z₀) :=
  (F.graph n).isOpen_window z₀

lemma mem_window (F : FiniteEmbeddedBoundaryGraphFamily) (n : ℕ) {z₀ : ℂ}
    (hz : z₀ ∈ (F.graph n).carrierᶜ) : z₀ ∈ F.window n z₀ :=
  (F.graph n).mem_window hz

structure RefinementData (F : FiniteEmbeddedBoundaryGraphFamily) (z₀ : ℂ) : Prop where
  basepoint_avoids : ∀ n, z₀ ∈ (F.graph n).carrierᶜ
  carrier_antitone : ∀ {m n}, m ≤ n → (F.graph m).carrier ⊆ (F.graph n).carrier

lemma window_antitone_of_refinement
    {F : FiniteEmbeddedBoundaryGraphFamily} {z₀ : ℂ}
    (hF : RefinementData F z₀) {m n : ℕ} (hmn : m ≤ n) :
    F.window n z₀ ⊆ F.window m z₀ := by
  exact FiniteEmbeddedBoundaryGraph.window_subset_window_of_carrier_subset
    (hF.carrier_antitone hmn) (hF.basepoint_avoids m) (hF.basepoint_avoids n)

structure ShrinkageData (F : FiniteEmbeddedBoundaryGraphFamily) (z₀ : ℂ) : Prop where
  refinement : RefinementData F z₀
  basis : ∀ U ∈ 𝓝 z₀, ∃ n, F.window n z₀ ⊆ U

end FiniteEmbeddedBoundaryGraphFamily

end

end MLC.Quadratic
