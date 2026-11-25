import Mlc.Research.Programme

/-!
# Dudko's remaining MLC frontier

This module packages the two open inputs identified at the end of
arXiv:2512.24171.  The checked arguments from the near-degenerate regime are
represented by the topological and numerical reductions in
`Mlc.Research.ParameterGeometry` and `Mlc.Research.Programme`.

Problem 4.3 supplies the admissible return system and its analytic realization.
Problem 4.4 is the virtual-Molecule interpolation assertion that the boundary
parameters omitted by this system do not occur.  No Lean `axiom` is introduced:
both statements remain explicit root inputs.
-/

namespace MLC
namespace Dudko

open MLC.Research

/-- Operational root-facing form of Problem 4.3.

    The system records the established near-degenerate arguments together with
    the still-open unbounded pseudo-Siegel case.  Its realization is the
    parameter-geometric conclusion used by the checked M1 reduction. -/
structure Problem43PseudoSiegelAPrioriBoundsData where
  system : CandidateSystem
  realization : system.Realization

/-- The boundary residual left after applying the system furnished by
    Problem 4.3.  These are precisely the virtual-Molecule parameters that
    require interpolation control. -/
def VirtualMoleculeResidual
    (p43 : Problem43PseudoSiegelAPrioriBoundsData) (c : ℂ) : Prop :=
  c ∈ MLC.Quadratic.MandelbrotSet ∧
    c ∉ interior MLC.Quadratic.MandelbrotSet ∧
    ¬ p43.system.Eligible c

/-- Operational root-facing form of Dudko's Interpolation Problem 4.4. -/
structure Problem44VirtualMoleculeData
    (p43 : Problem43PseudoSiegelAPrioriBoundsData) : Prop where
  virtual_molecule_residual_empty :
    ∀ c, ¬ VirtualMoleculeResidual p43 c

/-- Problem 4.4 completes parameter coverage for the system from Problem 4.3. -/
theorem Problem44VirtualMoleculeData.coverage
    {p43 : Problem43PseudoSiegelAPrioriBoundsData}
    (p44 : Problem44VirtualMoleculeData p43) :
    p43.system.Coverage := by
  intro c hc
  by_cases hInterior : c ∈ interior MLC.Quadratic.MandelbrotSet
  · exact Or.inl hInterior
  · right
    by_contra hNotEligible
    exact p44.virtual_molecule_residual_empty c ⟨hc, hInterior, hNotEligible⟩

/-- Dudko's two open problems close the checked near-degenerate argument. -/
theorem mlc_of_problem43_problem44
    (p43 : Problem43PseudoSiegelAPrioriBoundsData)
    (p44 : Problem44VirtualMoleculeData p43) :
    LocallyConnectedSpace MLC.Quadratic.MandelbrotSet :=
  p43.system.locallyConnectedSpace_of_realization_coverage
    p43.realization p44.coverage

/-- The complete two-problem root input described at the end of
    arXiv:2512.24171 §4.5. -/
structure DudkoFrontierInput where
  problem43 : Problem43PseudoSiegelAPrioriBoundsData
  problem44 : Problem44VirtualMoleculeData problem43

/-- The existing checked M1 chain transforms the two explicit open problems
    into local connectedness of the Mandelbrot set. -/
theorem DudkoFrontierInput.locallyConnectedSpace
    (h : DudkoFrontierInput) :
    LocallyConnectedSpace MLC.Quadratic.MandelbrotSet :=
  mlc_of_problem43_problem44 h.problem43 h.problem44

/-- Compatibility name retained for categorical/package consumers. -/
abbrev ResidualOpenVirtualNearMoleculeData :=
  DudkoFrontierInput

/-- A proposition-level marker for the residual package. -/
def CategoricalResidualOpenVirtualNearMoleculeData : Prop :=
  Nonempty DudkoFrontierInput

theorem categoricalResidualOpenVirtualNearMoleculeData_iff :
    CategoricalResidualOpenVirtualNearMoleculeData ↔
      Nonempty ResidualOpenVirtualNearMoleculeData :=
  Iff.rfl

end Dudko

/-- Public compatibility name for Dudko's Problem 4.3. -/
abbrev Problem43PseudoSiegelAPrioriBoundsData :=
  Dudko.Problem43PseudoSiegelAPrioriBoundsData

/-- Public compatibility name for Dudko's Interpolation Problem 4.4. -/
abbrev Problem44VirtualMoleculeData
    (p43 : Problem43PseudoSiegelAPrioriBoundsData) :=
  Dudko.Problem44VirtualMoleculeData p43

/-- Public compatibility name for the complete two-problem frontier. -/
abbrev ResidualOpenVirtualNearMoleculeData :=
  Dudko.DudkoFrontierInput

/-- Public proposition-level marker for the complete categorical frontier. -/
def CategoricalResidualOpenVirtualNearMoleculeData : Prop :=
  Dudko.CategoricalResidualOpenVirtualNearMoleculeData

theorem categoricalResidualOpenVirtualNearMoleculeData_iff :
    CategoricalResidualOpenVirtualNearMoleculeData ↔
      Nonempty ResidualOpenVirtualNearMoleculeData :=
  Iff.rfl

end MLC
