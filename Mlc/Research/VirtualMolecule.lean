import Mlc.Research.Programme
import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# The virtual-Molecule programme

The source paragraph in `arXiv:2512.24171/main.tex`, §4.5, says:

> Jointly with Kahn and Lyubich, we put forward a strategy to approach
> Problem 4.4 by considering partially invariant virtual Julia sets of
> M^(s). They are connected hulls of the corresponding Cantor small Julia
> sets within J_f and contain the critical orbit only up to an appropriate
> number of first returns. A posteriori, bounds for virtual Julia sets can be
> deduced by assuming a uniform hyperbolicity of the renormalization associated
> with M. The strategy towards Problem 4.4 is to develop such control a
> priori.

This module records the operational consequences of that paragraph. A virtual
Julia set is kept as explicit data: a compact connected hull inside the Julia
set, a finite first-return window, and partial invariance. A phase-parameter
realization then transports a return budget to the connected parameter nest
already used by the checked MLC kernel. Uniform hyperbolicity is not assumed
as a root input; `dynamicSeparationEstimate` is the a priori object that the
programme must construct.
-/

namespace MLC.Research

open Set Filter Topology Metric

noncomputable section

/-- First-return depths associated with the levels of a virtual-Molecule
    tower. -/
structure FirstReturnSchedule where
  depth : ℕ → ℕ
  positive : ∀ n, 0 < depth n
  strictly_increasing : StrictMono depth

/-- The critical-orbit segment ending at the prescribed first return. -/
def CriticalOrbitPrefix
    (c : ℂ) (returns : FirstReturnSchedule) (n : ℕ) : Set ℂ :=
  {z | ∃ k ≤ returns.depth n, z = MLC.Quadratic.orbit c 0 k}

/-- Partially invariant virtual Julia sets for the quadratic polynomial
    `f_c`.  `smallJulia n` is the Cantor source, while `carrier n` is the
    connected hull retained inside `J_c`. -/
structure VirtualJuliaNest (c : ℂ) where
  smallJulia : ℕ → Set ℂ
  carrier : ℕ → Set ℂ
  returns : FirstReturnSchedule
  smallJulia_nonempty : ∀ n, (smallJulia n).Nonempty
  smallJulia_compact : ∀ n, IsCompact (smallJulia n)
  smallJulia_totallyDisconnected :
    ∀ n, TotallyDisconnectedSpace (smallJulia n)
  smallJulia_no_isolated :
    ∀ n x, x ∈ smallJulia n →
      x ∈ closure (smallJulia n \ {x})
  smallJulia_subset_carrier : ∀ n, smallJulia n ⊆ carrier n
  carrier_subset_julia : ∀ n, carrier n ⊆ MLC.Quadratic.J c
  carrier_connected : ∀ n, IsConnected (carrier n)
  carrier_compact : ∀ n, IsCompact (carrier n)
  nested : ∀ n, carrier (n + 1) ⊆ carrier n
  partially_invariant :
    ∀ n, MapsTo ((MLC.Quadratic.fc c)^[returns.depth n])
      (carrier n) (carrier n)
  critical_prefix_subset :
    ∀ n, CriticalOrbitPrefix c returns n ⊆ carrier n

/-- Dynamical separation control on the virtual hulls. This is the concrete
    a priori budget that must eventually be extracted from the near-degenerate
    argument. -/
def VirtualJuliaNest.SeparationEstimate
    {c : ℂ} (V : VirtualJuliaNest c) (cost : ℕ → ℝ) : Prop :=
  ∀ ε > (0 : ℝ), ∃ C : ℝ, ∀ n z, z ∈ closure (V.carrier n) →
    ε ≤ dist z 0 → (∑ j ∈ Finset.range n, cost j) ≤ C

/-- A phase--parameter realization from connected parameter pieces into
    virtual Julia hulls. -/
structure VirtualPhaseParameter
    (c : ℂ) (V : VirtualJuliaNest c)
    (D : ConnectedNest MLC.Quadratic.MandelbrotSet c) where
  chart : ℕ → ℂ → ℂ
  continuous_chart : ∀ n, Continuous (chart n)
  mapsTo_carrier : ∀ n, MapsTo (chart n) (D.piece n) (V.carrier n)
  chart_center : ∀ n, chart n c = 0
  parameterDistanceBound : ℝ
  parameterDistanceBound_pos : 0 < parameterDistanceBound
  parameterDistance_le :
    ∀ n z, z ∈ closure (D.piece n) →
      dist z c ≤ parameterDistanceBound * dist (chart n z) 0

/-- A dynamical separation estimate transfers through a phase--parameter
    realization to the parameter nest. -/
theorem VirtualPhaseParameter.parameterSeparationEstimate
    {c : ℂ} {V : VirtualJuliaNest c}
    {D : ConnectedNest MLC.Quadratic.MandelbrotSet c}
    (P : VirtualPhaseParameter c V D) {cost : ℕ → ℝ}
    (hVirtual : V.SeparationEstimate cost) :
    D.SeparationEstimate cost := by
  intro ε hε
  obtain ⟨C, hC⟩ := hVirtual
    (ε / P.parameterDistanceBound)
    (div_pos hε P.parameterDistanceBound_pos)
  refine ⟨C, ?_⟩
  intro n z hz hDistance
  have hzCarrier :
      P.chart n z ∈ closure (V.carrier n) :=
    (P.mapsTo_carrier n).closure (P.continuous_chart n) hz
  have hDynamicalDistance :
      ε / P.parameterDistanceBound ≤ dist (P.chart n z) 0 := by
    rw [div_le_iff₀ P.parameterDistanceBound_pos]
    rw [mul_comm]
    exact hDistance.trans (P.parameterDistance_le n z hz)
  exact hC n (P.chart n z) hzCarrier hDynamicalDistance

/-- The concrete a priori-control package sought in Dudko's virtual-Molecule
    programme. The checked MLC kernel needs precisely its return budget and
    parameter-side separation estimate. -/
structure VirtualMoleculeAPrioriControl (c : ℂ) where
  parameter_mem : c ∈ MLC.Quadratic.MandelbrotSet
  virtualJulia : VirtualJuliaNest c
  budget : ReturnBudget
  parameterNest : ConnectedNest MLC.Quadratic.MandelbrotSet c
  phaseParameter : VirtualPhaseParameter c virtualJulia parameterNest
  linearLossControl : budget.LinearLossControl
  dynamicSeparationEstimate :
    virtualJulia.SeparationEstimate budget.cost

/-- Forget the dynamical data and retain exactly the parameter realization
    consumed by the checked MLC kernel. -/
def VirtualMoleculeAPrioriControl.parameterRealization
    {c : ℂ} (V : VirtualMoleculeAPrioriControl c) :
    ParameterRealization MLC.Quadratic.MandelbrotSet c V.budget where
  nest := V.parameterNest
  separation :=
    V.phaseParameter.parameterSeparationEstimate V.dynamicSeparationEstimate

/-- Add the virtual-Molecule branch to an admissible return system. -/
def CandidateSystem.withVirtualMolecule (A : CandidateSystem) :
    CandidateSystem where
  admissible c b :=
    A.admissible c b ∨
      ∃ V : VirtualMoleculeAPrioriControl c, V.budget = b

/-- Problem 4.3's known realization extends to every virtual-Molecule
    a priori-control witness. -/
theorem CandidateSystem.withVirtualMolecule_realization
    (A : CandidateSystem) (h : A.Realization) :
    A.withVirtualMolecule.Realization := by
  intro c hc b hAdmissible hControl
  rcases hAdmissible with hBase | hVirtual
  · exact h c hc b hBase hControl
  · rcases hVirtual with ⟨V, rfl⟩
    exact ⟨V.parameterRealization⟩

/-- Completion of the virtual-Molecule branch: every boundary parameter is
    already covered by Problem 4.3 or admits a virtual-Julia a priori control. -/
def CandidateSystem.VirtualMoleculeCompletion (A : CandidateSystem) : Prop :=
  ∀ c ∈ MLC.Quadratic.MandelbrotSet,
    c ∈ interior MLC.Quadratic.MandelbrotSet ∨
      A.Eligible c ∨ Nonempty (VirtualMoleculeAPrioriControl c)

/-- The completion above is exactly global coverage of the extended
    candidate system. -/
theorem CandidateSystem.withVirtualMolecule_coverage_iff_completion
    (A : CandidateSystem) :
    A.withVirtualMolecule.Coverage ↔ A.VirtualMoleculeCompletion := by
  constructor
  · intro hCoverage c hc
    rcases hCoverage c hc with hInterior | hEligible
    · exact Or.inl hInterior
    rcases hEligible with ⟨b, hAdmissible, hControl⟩
    rcases hAdmissible with hBase | hVirtual
    · exact Or.inr (Or.inl ⟨b, hBase, hControl⟩)
    · rcases hVirtual with ⟨V, -⟩
      exact Or.inr (Or.inr ⟨V⟩)
  · intro hCompletion c hc
    rcases hCompletion c hc with hInterior | hResidual
    · exact Or.inl hInterior
    right
    rcases hResidual with hBase | hVirtual
    · rcases hBase with ⟨b, hAdmissible, hControl⟩
      exact ⟨b, Or.inl hAdmissible, hControl⟩
    · rcases hVirtual with ⟨V⟩
      exact ⟨V.budget, Or.inr ⟨V, rfl⟩, V.linearLossControl⟩

end

end MLC.Research
