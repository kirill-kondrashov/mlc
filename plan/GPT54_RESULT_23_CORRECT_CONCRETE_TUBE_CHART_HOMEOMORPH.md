# GPT-5.4 Result 23: Correct concrete tube chart using `Homeomorph`

## Scope

This was a read-only corrective audit. I read Task 23, Result 22, and Supervisor
Review 22; used `/tmp` Lean probes only; wrote this result artifact; and did not
edit repository source files or commit.

## Decision

**Decision (2): chart and atlas compile, but the full fiber-homeomorphism theorem
still needs one small preliminary subtype-homeomorphism lemma.**

The corrected chart/atlas layer is now compile-tested with:
- the canonical projection `tubeProj : total → Λ`;
- a genuine `Homeomorph` on the exact source subtype
  `{p : total // tubeProj hscope p ∈ baseSet}`;
- the full target type `baseSet × DiskType model`;
- projection compatibility;
- an atlas assigning such a chart at every parameter point;
- a derived projection-surjectivity witness from a chosen disk point.

What remains for the full “fiber over `c` is homeomorphic to `DiskType model`” claim
is the final subtype simplification from

```lean
{y : baseSet × DiskType model // ((y.1 : baseSet) : Λ) = c}
```

to `DiskType model`.

## Corrected compiled code

Exact command:

```bash
cd /home/kir/pers/mlc && cat > /tmp/task23_probe.lean <<'EOF'
import Mlc.AnalyticQuadraticLikeFamilyCore
import Mathlib.Analysis.Complex.Basic

open Set
open scoped Classical

namespace Molecule

abbrev OpenUnitDisk : Type := {z : ℂ // z ∈ Metric.ball (0 : ℂ) 1}
abbrev ClosedUnitDisk : Type := {z : ℂ // z ∈ Metric.closedBall (0 : ℂ) 1}

inductive DiskModel
  | openUnit
  | closedUnit

abbrev DiskType : DiskModel → Type
  | .openUnit => OpenUnitDisk
  | .closedUnit => ClosedUnitDisk

instance diskTypeTopologicalSpace (model : DiskModel) : TopologicalSpace (DiskType model) := by
  cases model <;> infer_instance

instance : Nonempty OpenUnitDisk := ⟨⟨0, by simp [Metric.mem_ball]⟩⟩
instance : Nonempty ClosedUnitDisk := ⟨⟨0, by simp [Metric.mem_closedBall]⟩⟩

section Tube

variable {Λ : Set ℂ} {total : Set (ℂ × ℂ)}
variable (hscope : total ⊆ Λ ×ˢ (Set.univ : Set ℂ))

abbrev tubeProj (p : total) : Λ :=
  ⟨p.1.1, (hscope p.2).1⟩

@[simp] theorem tubeProj_coe (p : total) : ((tubeProj hscope p : Λ) : ℂ) = p.1.1 := rfl

abbrev TubeSource (baseSet : Set Λ) := {p : total // tubeProj hscope p ∈ baseSet}
abbrev TubeTarget (baseSet : Set Λ) (model : DiskModel) := baseSet × DiskType model

structure ConcreteTubeChart (model : DiskModel) where
  baseSet : Set Λ
  isOpen_baseSet : IsOpen baseSet
  homeomorph : TubeSource hscope baseSet ≃ₜ TubeTarget baseSet model
  proj_fst : ∀ p : TubeSource hscope baseSet, ((homeomorph p).1 : Λ) = tubeProj hscope p

structure ConcreteTubeAtlas (model : DiskModel) where
  chartAt : ∀ c : Λ, ConcreteTubeChart hscope model
  mem_baseSet_chartAt : ∀ c : Λ, c ∈ (chartAt c).baseSet

noncomputable def someDiskPoint (model : DiskModel) : DiskType model := by
  cases model
  · exact Classical.choice inferInstance
  · exact Classical.choice inferInstance

noncomputable def pointOverBase (model : DiskModel) (A : ConcreteTubeAtlas hscope model) (c : Λ) : total :=
  ((A.chartAt c).homeomorph.symm ⟨⟨c, A.mem_baseSet_chartAt c⟩, someDiskPoint model⟩).1

@[simp] theorem pointOverBase_proj_val (model : DiskModel) (A : ConcreteTubeAtlas hscope model) (c : Λ) :
    ((tubeProj hscope (pointOverBase hscope model A c) : Λ) : ℂ) = (c : ℂ) := by
  let q : TubeSource hscope ((A.chartAt c).baseSet) :=
    (A.chartAt c).homeomorph.symm ⟨⟨c, A.mem_baseSet_chartAt c⟩, someDiskPoint model⟩
  have hfst := (A.chartAt c).proj_fst q
  simpa [pointOverBase, q] using congrArg Subtype.val hfst.symm

@[simp] theorem pointOverBase_proj (model : DiskModel) (A : ConcreteTubeAtlas hscope model) (c : Λ) :
    tubeProj hscope (pointOverBase hscope model A c) = c := by
  apply Subtype.ext
  simpa using pointOverBase_proj_val hscope model A c

structure QuadraticLikeTube (F : AnalyticQuadraticLikeFamilyCore)
    (model : DiskModel)
    (total : Set (ℂ × ℂ))
    (hscope : total ⊆ F.parameterSet ×ˢ (Set.univ : Set ℂ)) where
  atlas : ConcreteTubeAtlas hscope model

structure QuadraticLikeFamilyWithConcreteTubes (modelU modelV : DiskModel) where
  core : AnalyticQuadraticLikeFamilyCore
  sourceTube : QuadraticLikeTube core modelU core.totalU core.scoped_totalU
  targetTube : QuadraticLikeTube core modelV core.totalV core.scoped_totalV

end Tube
end Molecule
EOF
lake env lean /tmp/task23_probe.lean
```

Compilation result:
- **passed**
- only warning: unused variable `c` in `chartAt`

## A. Canonical projection

The exact canonical projection is:

```lean
abbrev tubeProj (p : total) : Λ :=
  ⟨p.1.1, (hscope p.2).1⟩
```

Compile-tested simp lemma:

```lean
@[simp] theorem tubeProj_coe (p : total) : ((tubeProj hscope p : Λ) : ℂ) = p.1.1 := rfl
```

This confirms Task 23.A: the first coordinate plus `hscope` gives the canonical
projection, so no redundant arbitrary projection field should be stored.

## B. Correct local chart

The corrected chart is:

```lean
abbrev TubeSource (baseSet : Set Λ) := {p : total // tubeProj hscope p ∈ baseSet}
abbrev TubeTarget (baseSet : Set Λ) (model : DiskModel) := baseSet × DiskType model

structure ConcreteTubeChart (model : DiskModel) where
  baseSet : Set Λ
  isOpen_baseSet : IsOpen baseSet
  homeomorph : TubeSource hscope baseSet ≃ₜ TubeTarget baseSet model
  proj_fst : ∀ p : TubeSource hscope baseSet, ((homeomorph p).1 : Λ) = tubeProj hscope p
```

This fixes all review-22 objections:
- source is the exact projection preimage by type;
- target is the full base-times-disk product by type;
- the map is a genuine `Homeomorph`, not just inverse data;
- there are no arbitrary `source`/`target` subset fields;
- there is no redundant `openBase` duplication.

### Subtype coercion shape

The key projection-compatibility coercion is:

```lean
((homeomorph p).1 : Λ) = tubeProj hscope p
```

because:
- `homeomorph p : baseSet × DiskType model`
- `(homeomorph p).1 : baseSet`
- coercing again gives `((homeomorph p).1 : Λ)`.

## C. Atlas and projection surjectivity

The corrected atlas compiles as:

```lean
structure ConcreteTubeAtlas (model : DiskModel) where
  chartAt : ∀ c : Λ, ConcreteTubeChart hscope model
  mem_baseSet_chartAt : ∀ c : Λ, c ∈ (chartAt c).baseSet
```

I also compile-tested the nonempty disk witnesses needed to derive preimages:

```lean
instance : Nonempty OpenUnitDisk := ⟨⟨0, by simp [Metric.mem_ball]⟩⟩
instance : Nonempty ClosedUnitDisk := ⟨⟨0, by simp [Metric.mem_closedBall]⟩⟩
```

and then defined a chart-based preimage point:

```lean
noncomputable def pointOverBase (model : DiskModel) (A : ConcreteTubeAtlas hscope model) (c : Λ) : total :=
  ((A.chartAt c).homeomorph.symm ⟨⟨c, A.mem_baseSet_chartAt c⟩, someDiskPoint model⟩).1
```

with compile-tested theorem:

```lean
@[simp] theorem pointOverBase_proj ... :
  tubeProj hscope (pointOverBase hscope model A c) = c
```

So the atlas data now genuinely imply projection surjectivity over the parameter
set.

## D. Fiber homeomorphism status

The corrected chart data do **not yet immediately** yield a homeomorphism

```lean
{p : total // tubeProj hscope p = c} ≃ₜ DiskType model
```

for arbitrary `c ∈ chart.baseSet` without one more subtype simplification lemma.

What the chart data naturally give first is a homeomorphism candidate to the sliced
product subtype:

```lean
{y : baseSet × DiskType model // ((y.1 : baseSet) : Λ) = c}
```

The remaining missing ingredient is a small project-local or reusable lemma that this
subtype is homeomorphic to `DiskType model` by identifying the unique base component
with `c` once `hc : c ∈ baseSet` is fixed.

A correct next theorem signature is therefore:

```lean
noncomputable def fiberHomeomorphDisk
    (chart : ConcreteTubeChart hscope model) (c : Λ) (hc : c ∈ chart.baseSet) :
    {p : total // tubeProj hscope p = c} ≃ₜ DiskType model
```

but its proof should be factored through the intermediate subtype above, plus a small
lemma of the schematic form:

```lean
noncomputable def baseFiberSliceHomeomorph
    (baseSet : Set Λ) (model : DiskModel) (c : Λ) (hc : c ∈ baseSet) :
    {y : baseSet × DiskType model // ((y.1 : baseSet) : Λ) = c} ≃ₜ DiskType model
```

I did **not** claim this theorem without that explicit subtype-homeomorphism step.

## E. Integration

The integration layer compiles as:

```lean
structure QuadraticLikeTube (F : AnalyticQuadraticLikeFamilyCore)
    (model : DiskModel)
    (total : Set (ℂ × ℂ))
    (hscope : total ⊆ F.parameterSet ×ˢ (Set.univ : Set ℂ)) where
  atlas : ConcreteTubeAtlas hscope model

structure QuadraticLikeFamilyWithConcreteTubes (modelU modelV : DiskModel) where
  core : AnalyticQuadraticLikeFamilyCore
  sourceTube : QuadraticLikeTube core modelU core.totalU core.scoped_totalU
  targetTube : QuadraticLikeTube core modelV core.totalV core.scoped_totalV
```

This ties source and target tube atlases directly to the core total spaces and their
existing scoping fields, with no duplicate total/scoping storage and no opaque
local-triviality/Jordan propositions.

## Supporting checks

I also ran:

```bash
cd /home/kir/pers/mlc && cat > /tmp/task23_checks.lean <<'EOF'
import Mathlib.Analysis.Complex.Basic

open Set

#check Homeomorph
#check Continuous
#check Metric.ball
#check Metric.closedBall
#check Subtype.ext
EOF
lake env lean /tmp/task23_checks.lean
```

This passed and confirmed the key names used in the corrected design.

## Full `git status --short`

```text
M Mlc.lean
?? Mlc/AnalyticQuadraticLikeFamilyCore.lean
?? Mlc/BMolFilledJulia.lean
?? Mlc/GenuineBMol.lean
?? plan/GPT54_PROMPT_11_QUADRATIC_LIKE_FAMILY_FOUNDATION_AUDIT.md
?? plan/GPT54_PROMPT_12_BMOL_FILLED_JULIA_DEFINITION.md
?? plan/GPT54_PROMPT_13_IMPLEMENT_BMOL_FILLED_JULIA_FOUNDATION.md
?? plan/GPT54_PROMPT_14_GENUINE_BMOL_FAMILY_REFINEMENT_AUDIT.md
?? plan/GPT54_PROMPT_15_IMPLEMENT_GENUINE_BMOL_REFINEMENT.md
?? plan/GPT54_PROMPT_16_CORRECT_GENUINE_BMOL_COMPACT_CONTAINMENT.md
?? plan/GPT54_PROMPT_17_ANALYTIC_QUADRATIC_LIKE_FAMILY_TOTAL_SPACE_AUDIT.md
?? plan/GPT54_PROMPT_18_CORRECT_ANALYTIC_FAMILY_TOTAL_SPACE_SPEC.md
?? plan/GPT54_PROMPT_19_DIRECT_SOURCE_CHECK_QUADRATIC_LIKE_FAMILY.md
?? plan/GPT54_PROMPT_20_IMPLEMENT_ANALYTIC_QUADRATIC_LIKE_FAMILY_CORE.md
?? plan/GPT54_PROMPT_21_QUADRATIC_LIKE_TUBE_BUNDLE_AUDIT.md
?? plan/GPT54_PROMPT_22_CONCRETE_TUBE_LOCAL_TRIVIALIZATION_ADAPTER.md
?? plan/GPT54_PROMPT_23_CORRECT_CONCRETE_TUBE_CHART_HOMEOMORPH.md
?? plan/GPT54_RESULT_09_SPECIFY_CANONICAL_PARAMETER_PIECE.md
?? plan/GPT54_RESULT_10_RENORMALIZATION_LOCUS_SPECIFICATION.md
?? plan/GPT54_RESULT_11_QUADRATIC_LIKE_FAMILY_FOUNDATION_AUDIT.md
?? plan/GPT54_RESULT_12_BMOL_FILLED_JULIA_DEFINITION.md
?? plan/GPT54_RESULT_13_IMPLEMENT_BMOL_FILLED_JULIA_FOUNDATION.md
?? plan/GPT54_RESULT_14_GENUINE_BMOL_FAMILY_REFINEMENT_AUDIT.md
?? plan/GPT54_RESULT_15_IMPLEMENT_GENUINE_BMOL_REFINEMENT.md
?? plan/GPT54_RESULT_16_CORRECT_GENUINE_BMOL_COMPACT_CONTAINMENT.md
?? plan/GPT54_RESULT_17_ANALYTIC_QUADRATIC_LIKE_FAMILY_TOTAL_SPACE_AUDIT.md
?? plan/GPT54_RESULT_18_CORRECT_ANALYTIC_FAMILY_TOTAL_SPACE_SPEC.md
?? plan/GPT54_RESULT_19_DIRECT_SOURCE_CHECK_QUADRATIC_LIKE_FAMILY.md
?? plan/GPT54_RESULT_20_IMPLEMENT_ANALYTIC_QUADRATIC_LIKE_FAMILY_CORE.md
?? plan/GPT54_RESULT_21_QUADRATIC_LIKE_TUBE_BUNDLE_AUDIT.md
?? plan/GPT54_RESULT_22_CONCRETE_TUBE_LOCAL_TRIVIALIZATION_ADAPTER.md
?? plan/GPT54_REVIEW_09_SPECIFY_CANONICAL_PARAMETER_PIECE.md
?? plan/GPT54_REVIEW_10_RENORMALIZATION_LOCUS_SPECIFICATION.md
?? plan/GPT54_REVIEW_11_QUADRATIC_LIKE_FAMILY_FOUNDATION_AUDIT.md
?? plan/GPT54_REVIEW_12_BMOL_FILLED_JULIA_DEFINITION.md
?? plan/GPT54_REVIEW_13_IMPLEMENT_BMOL_FILLED_JULIA_FOUNDATION.md
?? plan/GPT54_REVIEW_14_GENUINE_BMOL_FAMILY_REFINEMENT_AUDIT.md
?? plan/GPT54_REVIEW_15_IMPLEMENT_GENUINE_BMOL_REFINEMENT.md
?? plan/GPT54_REVIEW_16_CORRECT_GENUINE_BMOL_COMPACT_CONTAINMENT.md
?? plan/GPT54_REVIEW_17_ANALYTIC_QUADRATIC_LIKE_FAMILY_TOTAL_SPACE_AUDIT.md
?? plan/GPT54_REVIEW_18_CORRECT_ANALYTIC_FAMILY_TOTAL_SPACE_SPEC.md
?? plan/GPT54_REVIEW_19_DIRECT_SOURCE_CHECK_QUADRATIC_LIKE_FAMILY.md
?? plan/GPT54_REVIEW_20_IMPLEMENT_ANALYTIC_QUADRATIC_LIKE_FAMILY_CORE.md
?? plan/GPT54_REVIEW_21_QUADRATIC_LIKE_TUBE_BUNDLE_AUDIT.md
?? plan/GPT54_REVIEW_22_CONCRETE_TUBE_LOCAL_TRIVIALIZATION_ADAPTER.md
?? plan/GPT54_TASK_10_RENORMALIZATION_LOCUS_SPECIFICATION.md
?? plan/GPT54_TASK_11_QUADRATIC_LIKE_FAMILY_FOUNDATION_AUDIT.md
?? plan/GPT54_TASK_12_BMOL_FILLED_JULIA_DEFINITION.md
?? plan/GPT54_TASK_13_IMPLEMENT_BMOL_FILLED_JULIA_FOUNDATION.md
?? plan/GPT54_TASK_14_GENUINE_BMOL_FAMILY_REFINEMENT_AUDIT.md
?? plan/GPT54_TASK_15_IMPLEMENT_GENUINE_BMOL_REFINEMENT.md
?? plan/GPT54_TASK_16_CORRECT_GENUINE_BMOL_COMPACT_CONTAINMENT.md
?? plan/GPT54_TASK_17_ANALYTIC_QUADRATIC_LIKE_FAMILY_TOTAL_SPACE_AUDIT.md
?? plan/GPT54_TASK_18_CORRECT_ANALYTIC_FAMILY_TOTAL_SPACE_SPEC.md
?? plan/GPT54_TASK_19_DIRECT_SOURCE_CHECK_QUADRATIC_LIKE_FAMILY.md
?? plan/GPT54_TASK_20_IMPLEMENT_ANALYTIC_QUADRATIC_LIKE_FAMILY_CORE.md
?? plan/GPT54_TASK_21_QUADRATIC_LIKE_TUBE_BUNDLE_AUDIT.md
?? plan/GPT54_TASK_22_CONCRETE_TUBE_LOCAL_TRIVIALIZATION_ADAPTER.md
?? plan/GPT54_TASK_23_CORRECT_CONCRETE_TUBE_CHART_HOMEOMORPH.md
```

## Confirmation

Only this result artifact was written in the repository. No repository Lean source
files were edited, and no commit was made.

## Exact next worker task

Implement the small subtype-homeomorphism lemma identifying
`{y : baseSet × DiskType model // ((y.1 : baseSet) : Λ) = c}` with `DiskType model`,
then finish the theorem `fiberHomeomorphDisk` for corrected concrete tube charts and
expose it from the project-local tube layer.
