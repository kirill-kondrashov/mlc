# GPT-5.4 Worker Task 15: Implement genuine BMol compact containment

**Repository:** `/home/kir/pers/mlc`
**Mode:** small Lean implementation
**New file:** `Mlc/GenuineBMol.lean`
**Result file:** `plan/GPT54_RESULT_15_IMPLEMENT_GENUINE_BMOL_REFINEMENT.md`

## Safety and scope

Read Result 14 and Supervisor Review 14. Preserve all unrelated working-tree
changes. Do not edit vendored dependencies and do not commit. Introduce no
`axiom`, `sorry`, or `admit`.

This task is limited to compact containment and import cleanup. Do not implement
`AnalyticBMolFamily`, holomorphic motion, tubing, winding conditions,
straightening, or degree claims.

## Required changes

### 1. Reduce the filled-Julia import

In `Mlc/BMolFilledJulia.lean`, replace the broad
`import Mlc.RenormalizationTypes` with the smallest direct import verified by
Result 14, retaining any basic topology import genuinely needed. Do not change the
existing declarations or their semantics.

### 2. Add explicit compact-containment API

Create `Mlc/GenuineBMol.lean`. In namespace `Molecule`, define a concrete
set-level compact-containment predicate whose expansion contains both:

```lean
IsCompact (closure U)
closure U ⊆ V
```

Choose a collision-free descriptive name after searching the repository and
Mathlib. Add elementary projection/simp lemmas for the two conjuncts if useful.

Define a wrapper structure `GenuineBMol` containing:

- `toBMol : BMol`;
- a proof that `toBMol.U` is compactly contained in `toBMol.V` according to the
  explicit predicate.

Provide the standard coercion from `GenuineBMol` to `BMol`. Add only small
compile-oriented lemmas demonstrating access to compactness, closure inclusion,
and reuse of `filledJuliaSet`. Do not duplicate the filled Julia definition.

The wrapper proof may use the existing `toBMol.closure_subset` when constructing
examples, but the public compact-containment predicate must state both parts.

### 3. Root import

Add `import Mlc.GenuineBMol` to `Mlc.lean` so the module is built by the root
library. Avoid redundant ordering changes.

## Verification

Run:

```bash
lake env lean Mlc/BMolFilledJulia.lean
lake env lean Mlc/GenuineBMol.lean
lake build
```

Search the changed Lean files for `axiom`, `sorry`, and `admit`; inspect the full
diff and report complete `git status --short`.

## Result report

Write only the authorized result artifact in addition to the Lean changes:
`plan/GPT54_RESULT_15_IMPLEMENT_GENUINE_BMOL_REFINEMENT.md`.

Report exact declarations, imports, verification outcomes, changed files, any
deviation, full status, and confirmation that no commit was made.
