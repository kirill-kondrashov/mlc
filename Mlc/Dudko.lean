import Mlc.Research.Programme

/-!
# Dudko's remaining MLC frontier

Problem 4.3 supplies the admissible return system and its analytic realization.
Problem 4.4 is the virtual-Molecule interpolation assertion that removes the
uncovered boundary residual. No project axiom is introduced.
-/

namespace MLC

open Research

/-- Operational root-facing form of Problem 4.3. -/
structure Problem43PseudoSiegelAPrioriBoundsData where
  system : CandidateSystem
  realization : system.Realization

/-- Boundary parameters not covered after applying Problem 4.3. -/
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

/-- Problem 4.4 completes parameter coverage for Problem 4.3's system. -/
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

/-- Problems 4.3 and 4.4 close the checked near-degenerate argument. -/
theorem mlc_of_problem43_problem44
    (p43 : Problem43PseudoSiegelAPrioriBoundsData)
    (p44 : Problem44VirtualMoleculeData p43) :
    LocallyConnectedSpace MLC.Quadratic.MandelbrotSet :=
  p43.system.locallyConnectedSpace_of_realization_coverage
    p43.realization p44.coverage

end MLC
