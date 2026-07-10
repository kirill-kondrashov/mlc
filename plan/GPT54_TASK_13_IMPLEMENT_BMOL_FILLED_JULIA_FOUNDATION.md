# GPT-5.4 Worker Task 13: Implement the intrinsic BMol filled Julia foundation

**Repository:** `/home/kir/pers/mlc`
**Mode:** small Lean implementation
**Target file:** `Mlc/BMolFilledJulia.lean`
**Result file:** `plan/GPT54_RESULT_13_IMPLEMENT_BMOL_FILLED_JULIA_FOUNDATION.md`

## Safety and scope

Read:

- `plan/GPT54_RESULT_12_BMOL_FILLED_JULIA_DEFINITION.md`;
- `plan/GPT54_REVIEW_12_BMOL_FILLED_JULIA_DEFINITION.md`.

Implement only the accepted intrinsic-definition layer. Do not modify vendored
dependencies. Do not change `parameterToBMol`, add a normalized quadratic
constructor, assert straightening, or prove connectivity of any fiber or parameter
locus. Introduce no `axiom`, `sorry`, or `admit`.

Preserve unrelated working-tree changes. Do not commit.

## Required implementation

Create `Mlc/BMolFilledJulia.lean` with the smallest sufficient imports and
declarations in namespace `Molecule`:

1. `filledJuliaSet (g : BMol) : Set ℂ`, intrinsically defined by every iterate of
   `g.f` remaining in `g.U`;
2. `[simp] mem_filledJuliaSet_iff`;
3. `filledJuliaSet_eq_iInter_preimage`;
4. `FilledJuliaConnected (g : BMol) : Prop := IsConnected (filledJuliaSet g)`;
5. `BMolParameterFamily (α : Type*)` with exactly a parameter set and a map into
   `BMol`;
6. `BMolParameterFamily.connectednessLocus`;
7. `[simp] mem_connectednessLocus_iff`.

Use the compile-tested shapes from Result 12, correcting style or namespace details
only as needed. Add concise docstrings. Avoid placeholder property fields.

Add `import Mlc.BMolFilledJulia` to `Mlc.lean` so the new module is part of the root
library build.

## Verification

Run:

```bash
lake env lean Mlc/BMolFilledJulia.lean
lake build
```

Also search the changed files for `axiom`, `sorry`, and `admit`, inspect the final
diff, and report the complete `git status --short`.

If compilation reveals a small signature or import issue, fix it within the stated
scope. If the accepted mathematical definition itself cannot compile without a
material redesign, stop and document the blocker rather than weakening it.

## Result report

Write `plan/GPT54_RESULT_13_IMPLEMENT_BMOL_FILLED_JULIA_FOUNDATION.md` summarizing:

- declarations added;
- files changed;
- verification commands and outcomes;
- any deviations from the accepted signatures;
- full `git status --short`;
- confirmation that no commit was made.

The Lean source changes and this result artifact are authorized. Do not edit other
plan/review/task files.
