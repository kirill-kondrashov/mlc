import Mlc.Research.ParameterGeometry
import Mlc.CategoricalMandelbrot

/-!
# Research frontier of the active MLC root

`CandidateSystem.admissible` must eventually be defined by genuine quadratic
returns and their geometric data. It is an explicit parameter, not an
uninterpreted project axiom or a predicate known to extend published classes.
M1 realization, global coverage, and publication novelty are separate claims.
-/

namespace MLC.Research

open Set Filter Topology Metric

noncomputable section

theorem subtype_ball_image {S : Set ℂ} {c : ℂ} (hc : c ∈ S) {r : ℝ}
    (hball : ball c r ⊆ S) :
    Subtype.val '' ball (⟨c, hc⟩ : S) r = ball c r := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hz
    exact ⟨⟨z, hball hz⟩, hz, rfl⟩

theorem subtype_ball_preconnected {S : Set ℂ} {c : ℂ} (hc : c ∈ S) {r : ℝ}
    (hball : ball c r ⊆ S) : IsPreconnected (ball (⟨c, hc⟩ : S) r) := by
  apply (Topology.IsInducing.isPreconnected_image
    (s := ball (⟨c, hc⟩ : S) r) (IsEmbedding.subtypeVal.isInducing)).mp
  rw [subtype_ball_image hc hball]
  exact (convex_ball c r).isPreconnected

theorem interior_small_ball {S : Set ℂ} {c : ℂ} (hc : c ∈ interior S)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ r, 0 < r ∧ r ≤ ε ∧ ball c r ⊆ S := by
  obtain ⟨δ, hδ, hδS⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hc)
  refine ⟨min δ ε, lt_min hδ hε, min_le_right _ _, ?_⟩
  exact (ball_subset_ball (min_le_left _ _)).trans hδS

theorem locallyConnectedAt_of_interior {S : Set ℂ} {c : ℂ}
    (hc : c ∈ S) (hinterior : c ∈ interior S) : LocallyConnectedAtSet S ⟨c, hc⟩ := by
  intro U hU
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp hU
  obtain ⟨r, hr, hrε, hrS⟩ := interior_small_ball hinterior hε
  exact ⟨ball (⟨c, hc⟩ : S) r, ball_mem_nhds _ hr,
    subtype_ball_preconnected hc hrS, (ball_subset_ball hrε).trans hεU⟩

/-- A slot for the independently defined dynamical admissibility condition.
The kernel checks the reduction for every such system; selecting a new
nonempty mathematical system is part of the research work. -/
structure CandidateSystem where
  admissible : ℂ → ReturnBudget → Prop

namespace CandidateSystem

variable (A : CandidateSystem)

/-- Numerical eligibility plus the system's dynamical admissibility test. -/
def Eligible (c : ℂ) : Prop :=
  ∃ b : ReturnBudget, A.admissible c b ∧ b.LinearLossControl

/-- M1: realize admissible controlled returns by connected parameter pieces
with the stated separation cost. This has not been proved for a new class. -/
def Realization : Prop :=
  ∀ (c : ℂ) (_hc : c ∈ MLC.Quadratic.MandelbrotSet) (b : ReturnBudget),
    A.admissible c b → b.LinearLossControl →
      Nonempty (ParameterRealization MLC.Quadratic.MandelbrotSet c b)

/-- A separate global obligation, stronger than a first publication on a
restricted class. It does not follow from M1 realization. -/
def Coverage : Prop :=
  ∀ c ∈ MLC.Quadratic.MandelbrotSet,
    c ∈ interior MLC.Quadratic.MandelbrotSet ∨ A.Eligible c

theorem eligible_of_data {c : ℂ} {b : ReturnBudget}
    (hadm : A.admissible c b) (hcontrol : b.LinearLossControl) : A.Eligible c :=
  ⟨b, hadm, hcontrol⟩

theorem realize_eligible (h : A.Realization) {c : ℂ}
    (hc : c ∈ MLC.Quadratic.MandelbrotSet) (he : A.Eligible c) :
    ∃ b : ReturnBudget, b.LinearLossControl ∧
      Nonempty (ParameterRealization MLC.Quadratic.MandelbrotSet c b) := by
  obtain ⟨b, ha, hb⟩ := he
  exact ⟨b, hb, h c hc b ha hb⟩

theorem locallyConnectedAt_eligible (h : A.Realization) {c : ℂ}
    (hc : c ∈ MLC.Quadratic.MandelbrotSet) (he : A.Eligible c) :
    LocallyConnectedAtSet MLC.Quadratic.MandelbrotSet ⟨c, hc⟩ := by
  obtain ⟨b, hb, ⟨D⟩⟩ := A.realize_eligible h hc he
  exact D.locallyConnectedAt hc hb

theorem locallyConnectedAt_covered (h : A.Realization) {c : ℂ}
    (hc : c ∈ MLC.Quadratic.MandelbrotSet)
    (hcover : c ∈ interior MLC.Quadratic.MandelbrotSet ∨ A.Eligible c) :
    LocallyConnectedAtSet MLC.Quadratic.MandelbrotSet ⟨c, hc⟩ := by
  rcases hcover with hi | he
  · exact locallyConnectedAt_of_interior hc hi
  · exact A.locallyConnectedAt_eligible h hc he

theorem locallyConnectedSpace_of_realization_coverage
    (h : A.Realization) (hcover : A.Coverage) :
    LocallyConnectedSpace MLC.Quadratic.MandelbrotSet := by
  apply (locallyConnectedSpace_iff_pointwise _).mpr
  intro c
  exact A.locallyConnectedAt_covered h c.property (hcover c c.property)

/-- The additional witness required before claiming an extension of the
published parameter range. `published` must be independently specified. -/
def StrictExtension (published : Set ℂ) : Prop :=
  ∃ c ∈ MLC.Quadratic.MandelbrotSet, A.Eligible c ∧ c ∉ published

theorem extension_point_is_locallyConnected
    {published : Set ℂ} (h : A.Realization) (hext : A.StrictExtension published) :
    ∃ c, ∃ hc : c ∈ MLC.Quadratic.MandelbrotSet,
      c ∉ published ∧ LocallyConnectedAtSet MLC.Quadratic.MandelbrotSet ⟨c, hc⟩ := by
  obtain ⟨c, hc, he, hp⟩ := hext
  exact ⟨c, hc, hp, A.locallyConnectedAt_eligible h hc he⟩

end CandidateSystem

end
end MLC.Research
