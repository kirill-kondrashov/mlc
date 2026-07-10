# GPT-5.4 Result 16: Correct GenuineBMol compact containment

## Summary

Corrected `Mlc/GenuineBMol.lean` so the public compact-containment predicate now explicitly contains both required parts:

- `IsCompact (closure U)`
- `closure U ⊆ V`

The corrected module keeps the coercion to `BMol`, removes the earlier tautological filled-Julia simp lemmas, and adds the requested projection lemmas plus a small convenience constructor from a vendored `BMol` and compactness of `closure U`.

## Files changed

- `Mlc/GenuineBMol.lean`
- `plan/GPT54_RESULT_16_CORRECT_GENUINE_BMOL_COMPACT_CONTAINMENT.md` (this report)

Per task scope, no other source file was modified.

## Corrected declarations

The misleading BMol-only abbreviation

```lean
abbrev HasCompactClosureInV (g : BMol) : Prop :=
  IsCompact (closure g.U)
```

was replaced by the reusable set-level predicate:

```lean
def IsCompactlyContainedIn (U V : Set ℂ) : Prop :=
  IsCompact (closure U) ∧ closure U ⊆ V
```

`GenuineBMol` now stores the complete predicate:

```lean
structure GenuineBMol where
  toBMol : BMol
  compact_containment : IsCompactlyContainedIn toBMol.U toBMol.V
```

The coercion was retained:

```lean
instance : Coe GenuineBMol BMol := ⟨GenuineBMol.toBMol⟩
```

## Added API lemmas

Added the requested elementary projection lemmas:

```lean
lemma isCompact_closure_U (g : GenuineBMol) :
    IsCompact (closure g.toBMol.U) :=
  g.compact_containment.1

lemma closure_U_subset_V (g : GenuineBMol) :
    closure g.toBMol.U ⊆ g.toBMol.V :=
  g.compact_containment.2
```

Also added the small convenience constructor justified by the vendored field
`g.closure_subset`:

```lean
def mkOfIsCompactClosure (g : BMol) (hcompact : IsCompact (closure g.U)) : GenuineBMol where
  toBMol := g
  compact_containment := ⟨hcompact, g.closure_subset⟩
```

## Removed prior tautological filled-Julia lemmas

The prior correction review noted that the three old simp lemmas were definitional restatements and did not expose the compact-containment API. They were removed in this narrow correction. Reuse of `filledJuliaSet` still follows from the coercion `GenuineBMol → BMol`.

## Verification

Commands run:

```bash
cd /home/kir/pers/mlc && lake env lean Mlc/GenuineBMol.lean
cd /home/kir/pers/mlc && lake build
cd /home/kir/pers/mlc && git --no-pager diff -- Mlc/GenuineBMol.lean
cd /home/kir/pers/mlc && git --no-pager status --short
```

Additional placeholder scan:

- searched `Mlc/GenuineBMol.lean` for `axiom|sorry|admit` with the built-in grep tool

Outcomes:

- `lake env lean Mlc/GenuineBMol.lean`: **passed**
- `lake build`: **passed**
- placeholder scan: **no matches**
- full build emitted only pre-existing warnings in unrelated files

## Final corrected file content

```lean
import Molecule.BMol
import Mlc.BMolFilledJulia

namespace Molecule

/-- A set `U` is compactly contained in `V` in the ambient plane. -/
def IsCompactlyContainedIn (U V : Set ℂ) : Prop :=
  IsCompact (closure U) ∧ closure U ⊆ V

/-- A local refinement of `BMol` adding genuine compact containment. -/
structure GenuineBMol where
  toBMol : BMol
  compact_containment : IsCompactlyContainedIn toBMol.U toBMol.V

instance : Coe GenuineBMol BMol := ⟨GenuineBMol.toBMol⟩

@[simp] lemma genuineBMol_toBMol (g : GenuineBMol) :
    g.toBMol = (g : BMol) := rfl

lemma isCompact_closure_U (g : GenuineBMol) :
    IsCompact (closure g.toBMol.U) :=
  g.compact_containment.1

lemma closure_U_subset_V (g : GenuineBMol) :
    closure g.toBMol.U ⊆ g.toBMol.V :=
  g.compact_containment.2

/-- Build a genuine BMol from a vendored `BMol` plus compactness of `closure U`. -/
def mkOfIsCompactClosure (g : BMol) (hcompact : IsCompact (closure g.U)) : GenuineBMol where
  toBMol := g
  compact_containment := ⟨hcompact, g.closure_subset⟩

end Molecule
```

## Full `git status --short`

```text
 M Mlc.lean
?? Mlc/BMolFilledJulia.lean
?? Mlc/GenuineBMol.lean
?? plan/GPT54_PROMPT_11_QUADRATIC_LIKE_FAMILY_FOUNDATION_AUDIT.md
?? plan/GPT54_PROMPT_12_BMOL_FILLED_JULIA_DEFINITION.md
?? plan/GPT54_PROMPT_13_IMPLEMENT_BMOL_FILLED_JULIA_FOUNDATION.md
?? plan/GPT54_PROMPT_14_GENUINE_BMOL_FAMILY_REFINEMENT_AUDIT.md
?? plan/GPT54_PROMPT_15_IMPLEMENT_GENUINE_BMOL_REFINEMENT.md
?? plan/GPT54_PROMPT_16_CORRECT_GENUINE_BMOL_COMPACT_CONTAINMENT.md
?? plan/GPT54_RESULT_09_SPECIFY_CANONICAL_PARAMETER_PIECE.md
?? plan/GPT54_RESULT_10_RENORMALIZATION_LOCUS_SPECIFICATION.md
?? plan/GPT54_RESULT_11_QUADRATIC_LIKE_FAMILY_FOUNDATION_AUDIT.md
?? plan/GPT54_RESULT_12_BMOL_FILLED_JULIA_DEFINITION.md
?? plan/GPT54_RESULT_13_IMPLEMENT_BMOL_FILLED_JULIA_FOUNDATION.md
?? plan/GPT54_RESULT_14_GENUINE_BMOL_FAMILY_REFINEMENT_AUDIT.md
?? plan/GPT54_RESULT_15_IMPLEMENT_GENUINE_BMOL_REFINEMENT.md
?? plan/GPT54_REVIEW_09_SPECIFY_CANONICAL_PARAMETER_PIECE.md
?? plan/GPT54_REVIEW_10_RENORMALIZATION_LOCUS_SPECIFICATION.md
?? plan/GPT54_REVIEW_11_QUADRATIC_LIKE_FAMILY_FOUNDATION_AUDIT.md
?? plan/GPT54_REVIEW_12_BMOL_FILLED_JULIA_DEFINITION.md
?? plan/GPT54_REVIEW_13_IMPLEMENT_BMOL_FILLED_JULIA_FOUNDATION.md
?? plan/GPT54_REVIEW_14_GENUINE_BMOL_FAMILY_REFINEMENT_AUDIT.md
?? plan/GPT54_REVIEW_15_IMPLEMENT_GENUINE_BMOL_REFINEMENT.md
?? plan/GPT54_TASK_10_RENORMALIZATION_LOCUS_SPECIFICATION.md
?? plan/GPT54_TASK_11_QUADRATIC_LIKE_FAMILY_FOUNDATION_AUDIT.md
?? plan/GPT54_TASK_12_BMOL_FILLED_JULIA_DEFINITION.md
?? plan/GPT54_TASK_13_IMPLEMENT_BMOL_FILLED_JULIA_FOUNDATION.md
?? plan/GPT54_TASK_14_GENUINE_BMOL_FAMILY_REFINEMENT_AUDIT.md
?? plan/GPT54_TASK_15_IMPLEMENT_GENUINE_BMOL_REFINEMENT.md
?? plan/GPT54_TASK_16_CORRECT_GENUINE_BMOL_COMPACT_CONTAINMENT.md
```

## Confirmation

The correction is complete within the authorized scope. No analytic-family machinery was added, no dependency was edited, and no commit was made.
