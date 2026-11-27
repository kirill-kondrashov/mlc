import Mlc.CategoricalRoot
import Mlc.Research.Published
import Mlc.Research.Problem43
import Mlc.Research.Problem44

/-!
# The programme: Problems 4.3 and 4.4 as a tree of lemmas

`MLC.RootInput` has two open inputs, Dudko's Problems 4.3 and 4.4, packaged as a candidate
system with its realization and as the virtual-Molecule completion. This module shows how
they follow from finer lemmas, one structure field each:

| field | lemma | source |
| --- | --- | --- |
| `transfer` | phase–parameter transfer | Kahn–Lyubich, Lyubich |
| `yoccoz` | parameters that are not infinitely renormalizable | Yoccoz, Hubbard |
| `teichmuller` | Teichmüller contraction for bounded type, §4.3 | Dudko–Lyubich, arXiv:2309.02107 |
| `boundedType` | dichotomy (4.6) of Theorem 4.1 | Dudko–Lyubich; Kahn |
| `antiMolecule` | amplification (4.3), (4.5) | Kahn–Lyubich |
| `neutral` | Theorem 4.2 | Dudko–Lyubich |
| `quadraticGrowth` | Theorem D, the class `QG_N` | Cheraghi–Shishikura, arXiv:1509.07843 |
| `unboundedTeichmuller`, `unboundedJumpCap`, `unboundedDichotomy` | Problem 4.3 | proposed reading of §4.4 |
| `virtualJulia`, `virtualTeichmuller`, `virtualDichotomy`, `virtualJumpCap`,
  `virtualLinearDichotomy`, `virtualTransfer` | Problem 4.4 | proposed reading of §4.5 |

The theorem `mlc_of_programme` is proved in Lean from these fields for every geometric
dictionary; the fields themselves are hypotheses, not proved. When a lemma is proved, its
field is removed from the structure and the theorem constructs it.
-/

namespace MLC

open Research Set

/-- The lemmas of the programme for the geometric dictionary `G`. -/
structure Research.ProgrammeInput (G : Geometry) : Prop where
  /-- phase–parameter transfer (shared by all classes with a tower) -/
  transfer : G.Transfer
  /-- published: the parameters that are not infinitely renormalizable -/
  yoccoz : G.Yoccoz
  /-- published: the Teichmüller contraction of the levels of bounded type, §4.3 -/
  teichmuller : G.TeichmullerContraction
  /-- published: Theorem 4.1, the dichotomy for bounded type -/
  boundedType : G.BoundedTypeInputs
  /-- published: the anti-Molecule condition, §4.1–§4.2 -/
  antiMolecule : G.AntiMoleculeInputs
  /-- published: Theorem 4.2, neutral parameters -/
  neutral : G.Neutral
  /-- published: Theorem D of Cheraghi–Shishikura, the satellite types of quadratic growth -/
  quadraticGrowth : G.QuadraticGrowth
  /-- Problem 4.3: the Teichmüller contraction for the pseudo-Siegel degeneration -/
  unboundedTeichmuller : G.UnboundedTeichmuller
  /-- Problem 4.3: the jumps of the degeneration at satellite levels of large relative period
  are capped -/
  unboundedJumpCap : G.UnboundedJumpCap
  /-- Problem 4.3: the dichotomy with an error at most linear in the period -/
  unboundedDichotomy : G.UnboundedDichotomy
  /-- Problem 4.4: partially invariant virtual Julia sets -/
  virtualJulia : G.VirtualJulia
  /-- Problem 4.4: Teichmüller contraction for the virtual levels -/
  virtualTeichmuller : G.VirtualTeichmuller
  /-- Problem 4.4, virtual bounded type: the dichotomy -/
  virtualDichotomy : G.VirtualDichotomy
  /-- Problem 4.4, virtual near-neutral: the jumps at levels of large relative period are
  capped -/
  virtualJumpCap : G.VirtualJumpCap
  /-- Problem 4.4, virtual near-neutral: the dichotomy with an error linear in the period -/
  virtualLinearDichotomy : G.VirtualLinearDichotomy
  /-- Problem 4.4: the virtual phase–parameter transfer -/
  virtualTransfer : G.VirtualTransfer

namespace Research.ProgrammeInput

variable {G : Geometry}

/-- Every boundary parameter is eligible for the system of the towers with a priori bounds,
or has a virtual a priori control. -/
theorem completion (h : ProgrammeInput G) : G.system.VirtualMoleculeCompletion :=
  { classes := by
      intro c hc
      by_cases hi : c ∈ interior MLC.Quadratic.MandelbrotSet
      · exact Or.inl hi
      right
      cases hcls : G.cls c
      · obtain ⟨b, hl, hr⟩ := h.yoccoz c hc hi hcls
        exact Or.inl (G.eligible_of_realization hr hl)
      · obtain ⟨b, hl, hr⟩ := h.neutral c hc hi hcls
        exact Or.inl (G.eligible_of_realization hr hl)
      · obtain ⟨B, hB⟩ := G.hasBound_of_bounded h.teichmuller h.boundedType hc hi hcls
        exact Or.inl (G.eligible_of_hasBound hB)
      · obtain ⟨B, hB⟩ := G.hasBound_of_antiMolecule h.antiMolecule hc hi hcls
        exact Or.inl (G.eligible_of_hasBound hB)
      · obtain ⟨b, hl, hr⟩ := h.quadraticGrowth c hc hi hcls
        exact Or.inl (G.eligible_of_realization hr hl)
      · obtain ⟨B, hB⟩ := G.hasBound_of_unbounded h.unboundedTeichmuller h.unboundedJumpCap
          h.unboundedDichotomy hc hi hcls
        exact Or.inl (G.eligible_of_hasBound hB)
      · exact Or.inr (G.virtualControl h.virtualJulia h.virtualTeichmuller h.virtualDichotomy
          h.virtualJumpCap h.virtualLinearDichotomy h.virtualTransfer hc hi (Or.inl hcls))
      · exact Or.inr (G.virtualControl h.virtualJulia h.virtualTeichmuller h.virtualDichotomy
          h.virtualJumpCap h.virtualLinearDichotomy h.virtualTransfer hc hi (Or.inr hcls)) }

/-- The lemmas of the programme give the first open input of the root: a candidate system
with its realization. -/
def problem43 (h : ProgrammeInput G) : Problem43PseudoSiegelAPrioriBoundsData where
  system := G.system
  realization := G.system_realization h.transfer

/-- The lemmas of the programme give the second open input of the root. -/
theorem problem44 (h : ProgrammeInput G) : Problem44VirtualMoleculeData h.problem43 :=
  ⟨h.completion⟩

end Research.ProgrammeInput

/-- The root input constructed from the lemmas of the programme. -/
def RootInput.ofProgramme {G : Geometry} (h : Research.ProgrammeInput G) : RootInput :=
  ⟨h.problem43, h.problem44⟩

/-- **MLC from the lemmas of the programme.** The local connectivity of `M` follows, for
every geometric dictionary, from the lemmas of `ProgrammeInput`. -/
theorem mlc_of_programme {G : Geometry} (h : Research.ProgrammeInput G) :
    LocallyConnectedSpace mandelbrotSet :=
  (RootInput.ofProgramme h).locallyConnectedSpace

end MLC
