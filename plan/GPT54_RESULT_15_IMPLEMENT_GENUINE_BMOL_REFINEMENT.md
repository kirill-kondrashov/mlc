# GPT-5.4 Result 15: Implement genuine BMol refinement

## Summary

Implemented the small local compact-containment refinement authorized by Result 14 and reduced the broad import in `Mlc/BMolFilledJulia.lean` to the smaller direct `Molecule.BMol` import path. No analytic-family machinery was added.

## Files changed

- `Mlc/BMolFilledJulia.lean`
- `Mlc/GenuineBMol.lean` (new)
- `Mlc.lean`
- `plan/GPT54_RESULT_15_IMPLEMENT_GENUINE_BMOL_REFINEMENT.md` (this report)

No vendored dependency was edited.

## Implementation details

### 1. Import cleanup in `Mlc/BMolFilledJulia.lean`

Replaced:

```lean
import Mlc.RenormalizationTypes
```

with:

```lean
import Molecule.BMol
```

while keeping the existing intrinsic filled Julia declarations unchanged.

### 2. New local refinement module `Mlc/GenuineBMol.lean`

Added the compact-containment refinement layer in namespace `Molecule`:

```lean
abbrev HasCompactClosureInV (g : BMol) : Prop :=
  IsCompact (closure g.U)

structure GenuineBMol where
  toBMol : BMol
  compact_closure : HasCompactClosureInV toBMol

instance : Coe GenuineBMol BMol := ⟨GenuineBMol.toBMol⟩
```

Added the small reuse lemmas needed to show compatibility with the intrinsic filled Julia API:

```lean
@[simp] lemma genuineBMol_toBMol (g : GenuineBMol) :
    g.toBMol = (g : BMol) := rfl

@[simp] lemma genuine_filledJuliaSet_def (g : GenuineBMol) :
    filledJuliaSet (g : BMol) = {z : ℂ | ∀ n : ℕ, (((g : BMol).f)^[n]) z ∈ (g : BMol).U} := rfl

@[simp] lemma genuine_filledJuliaConnected_iff (g : GenuineBMol) :
    FilledJuliaConnected (g : BMol) ↔ IsConnected (filledJuliaSet (g : BMol)) := Iff.rfl
```

### 3. Root library import

Added:

```lean
import Mlc.GenuineBMol
```

to `Mlc.lean`.

## Verification

Commands run:

```bash
cd /home/kir/pers/mlc && lake env lean Mlc/BMolFilledJulia.lean && lake env lean Mlc/GenuineBMol.lean
cd /home/kir/pers/mlc && lake build
cd /home/kir/pers/mlc && git --no-pager diff -- Mlc/BMolFilledJulia.lean Mlc/GenuineBMol.lean Mlc.lean
cd /home/kir/pers/mlc && git --no-pager status --short
```

Outcomes:

- focused module check: **passed**
- full `lake build`: **passed**
- build emitted only pre-existing warnings in unrelated files
- inspected final diff and final git status

## Final file snapshots

`Mlc/BMolFilledJulia.lean`

```lean
import Molecule.BMol
import Mathlib.Topology.Connected.Basic
```

The rest of the file’s declarations remained the same.

`Mlc/GenuineBMol.lean`

```lean
import Molecule.BMol
import Mlc.BMolFilledJulia

namespace Molecule

abbrev HasCompactClosureInV (g : BMol) : Prop :=
  IsCompact (closure g.U)

structure GenuineBMol where
  toBMol : BMol
  compact_closure : HasCompactClosureInV toBMol

instance : Coe GenuineBMol BMol := ⟨GenuineBMol.toBMol⟩
```

plus the three simp/reuse lemmas listed above.

## Honest scope check

This task implemented only the compact-containment refinement and import cleanup authorized by the task/result chain.

It did **not**:

- add analytic-family structure;
- modify vendored `Molecule/BMol.lean`;
- add axioms, `sorry`, or `admit`;
- claim Theorem 10.1 inputs are now satisfied;
- make any commit.

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
?? plan/GPT54_RESULT_09_SPECIFY_CANONICAL_PARAMETER_PIECE.md
?? plan/GPT54_RESULT_10_RENORMALIZATION_LOCUS_SPECIFICATION.md
?? plan/GPT54_RESULT_11_QUADRATIC_LIKE_FAMILY_FOUNDATION_AUDIT.md
?? plan/GPT54_RESULT_12_BMOL_FILLED_JULIA_DEFINITION.md
?? plan/GPT54_RESULT_13_IMPLEMENT_BMOL_FILLED_JULIA_FOUNDATION.md
?? plan/GPT54_RESULT_14_GENUINE_BMOL_FAMILY_REFINEMENT_AUDIT.md
?? plan/GPT54_REVIEW_09_SPECIFY_CANONICAL_PARAMETER_PIECE.md
?? plan/GPT54_REVIEW_10_RENORMALIZATION_LOCUS_SPECIFICATION.md
?? plan/GPT54_REVIEW_11_QUADRATIC_LIKE_FAMILY_FOUNDATION_AUDIT.md
?? plan/GPT54_REVIEW_12_BMOL_FILLED_JULIA_DEFINITION.md
?? plan/GPT54_REVIEW_13_IMPLEMENT_BMOL_FILLED_JULIA_FOUNDATION.md
?? plan/GPT54_REVIEW_14_GENUINE_BMOL_FAMILY_REFINEMENT_AUDIT.md
?? plan/GPT54_TASK_10_RENORMALIZATION_LOCUS_SPECIFICATION.md
?? plan/GPT54_TASK_11_QUADRATIC_LIKE_FAMILY_FOUNDATION_AUDIT.md
?? plan/GPT54_TASK_12_BMOL_FILLED_JULIA_DEFINITION.md
?? plan/GPT54_TASK_13_IMPLEMENT_BMOL_FILLED_JULIA_FOUNDATION.md
?? plan/GPT54_TASK_14_GENUINE_BMOL_FAMILY_REFINEMENT_AUDIT.md
?? plan/GPT54_TASK_15_IMPLEMENT_GENUINE_BMOL_REFINEMENT.md
```

## Confirmation

Implementation and verification are complete within scope. No commit was made.
