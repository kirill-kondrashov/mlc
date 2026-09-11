import Mathlib.Topology.Compactness.Compact
import Mlc.CategoricalRoot

/-!
# Deformation and flow interfaces

The interfaces here separate consequences of a coherent parametrization or a
terminal radial extension from the unresolved construction of those data.
Nothing in this file asserts Mandelbrot local connectivity.
-/

namespace MLC
namespace FlowInterfaces

open Set Filter

noncomputable section

abbrev ClosedUnitDisk := {z : ℂ // ‖z‖ ≤ (1 : ℝ)}

/-- Uniform convergence of a sequence of maps on the closed unit disk. -/
def UniformLimit
    (f : ℕ → ClosedUnitDisk → ℂ)
    (g : ClosedUnitDisk → ℂ) : Prop :=
  ∀ ε > (0 : ℝ), ∃ N, ∀ n ≥ N, ∀ u,
    dist (f n u) (g u) < ε

structure CoherentParametrization (S : Set ℂ) where
  map : ℕ → ClosedUnitDisk → ℂ
  continuous_map : ∀ n, Continuous (map n)
  limit : ClosedUnitDisk → ℂ
  continuous_limit : Continuous limit
  uniform_limit : UniformLimit map limit
  target_closed : IsClosed S
  map_image_subset : ∀ n, Set.range (map n) ⊆ S
  limit_surjective : ∀ x ∈ S, ∃ u, limit u = x

theorem limit_image_subset (P : CoherentParametrization S) :
    Set.range P.limit ⊆ S := by
  intro x hx
  rcases hx with ⟨u, rfl⟩
  apply P.target_closed.closure_subset
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := P.uniform_limit ε hε
  refine ⟨P.map N u, P.map_image_subset N ⟨u, rfl⟩, ?_⟩
  simpa [dist_comm] using hN N le_rfl u

theorem limit_image_eq (P : CoherentParametrization S) :
    Set.range P.limit = S := by
  apply Subset.antisymm
  · exact limit_image_subset P
  · intro x hx
    obtain ⟨u, hu⟩ := P.limit_surjective x hx
    exact ⟨u, hu⟩

/-- The explicit terminal-extension obligation for an exterior radial flow. -/
structure TerminalExtension (A S : Set ℂ) where
  extension : Set.Icc (1 : ℝ) (Real.exp 1) → ℂ → ℂ
  extension_continuous :
    Continuous (fun p : Set.Icc (1 : ℝ) (Real.exp 1) × ℂ =>
      extension p.1 p.2)
  image_subset : ∀ w x, extension w x ∈ A
  boundary_image : ∀ w x, w.1 = 1 → extension w x ∈ S
  retraction : ∀ x ∈ S,
    extension ⟨1, by
      have h := Real.add_one_le_exp (1 : ℝ)
      constructor
      · norm_num
      · linarith⟩ x = x

def RadialTerminalExtension (A S : Set ℂ) : Prop :=
  Nonempty (TerminalExtension A S)

/-- A root-facing flow input remains an explicit theorem hypothesis. -/
structure RootFlowInput (S : Set ℂ) where
  ambient : Set ℂ
  terminal : RadialTerminalExtension ambient S

theorem rootFlowInput_is_explicit (h : RootFlowInput S) :
    RadialTerminalExtension h.ambient S :=
  h.terminal

end
end FlowInterfaces
end MLC
