import Mlc.Research.VirtualMolecule

/-!
# Dudko's remaining MLC frontier

Problem 4.3 supplies the admissible return system and its analytic realization.
Problem 4.4 is the virtual-Molecule interpolation assertion that every
uncovered boundary parameter admits a virtual-Julia a priori control. No
project axiom is introduced.
-/

namespace MLC

open Research

/-- Operational root-facing form of Problem 4.3. -/
structure Problem43PseudoSiegelAPrioriBoundsData where
  system : CandidateSystem
  realization : system.Realization

/-- Operational root-facing form of Dudko's Interpolation Problem 4.4. -/
structure Problem44VirtualMoleculeData
    (p43 : Problem43PseudoSiegelAPrioriBoundsData) : Prop where
  virtualMoleculeCompletion :
    p43.system.VirtualMoleculeCompletion

/-- Problem 4.4 completes parameter coverage for the candidate system
    augmented by virtual-Julia controls. -/
theorem Problem44VirtualMoleculeData.coverage
    {p43 : Problem43PseudoSiegelAPrioriBoundsData}
    (p44 : Problem44VirtualMoleculeData p43) :
    p43.system.withVirtualMolecule.Coverage :=
  (p43.system.withVirtualMolecule_coverage_iff_completion).2
    p44.virtualMoleculeCompletion

/-- Problems 4.3 and 4.4 close the checked near-degenerate argument. -/
theorem mlc_of_problem43_problem44
    (p43 : Problem43PseudoSiegelAPrioriBoundsData)
    (p44 : Problem44VirtualMoleculeData p43) :
    LocallyConnectedSpace MLC.Quadratic.MandelbrotSet :=
  p43.system.withVirtualMolecule.locallyConnectedSpace_of_realization_coverage
    (p43.system.withVirtualMolecule_realization p43.realization)
    p44.coverage

end MLC
