# GPT-5.4 Worker Task 16: Correct GenuineBMol compact containment

**Repository:** `/home/kir/pers/mlc`
**Mode:** narrow corrective Lean implementation
**Target:** `Mlc/GenuineBMol.lean`
**Result file:** `plan/GPT54_RESULT_16_CORRECT_GENUINE_BMOL_COMPACT_CONTAINMENT.md`

## Safety and scope

Read Task 15, Result 15, and Supervisor Review 15. Preserve unrelated working-tree
changes. Do not edit vendored dependencies, add analytic-family machinery, or
commit. Introduce no `axiom`, `sorry`, or `admit`.

Only `Mlc/GenuineBMol.lean` and the new Result 16 report are authorized for
modification. `Mlc/BMolFilledJulia.lean` and `Mlc.lean` are already correct and
must remain unchanged.

## Required correction

Replace the incomplete predicate with an explicit compact-containment definition
that contains both:

```lean
IsCompact (closure U)
closure U ⊆ V
```

Prefer a reusable set-level declaration over a misleading BMol-only abbreviation.
Search the repository and Mathlib for naming collisions before selecting its name.

Update `GenuineBMol.compact_closure` (renaming the field if clearer) to store the
complete predicate for `toBMol.U` and `toBMol.V`.

Provide elementary lemmas that expose:

- compactness of `closure g.toBMol.U`;
- inclusion `closure g.toBMol.U ⊆ g.toBMol.V`.

Retain the coercion to `BMol`. Remove or retain the existing tautological
filled-Julia simp lemmas according to ordinary Lean API quality, but do not
duplicate `filledJuliaSet` and do not claim new dynamics.

Because every underlying `BMol` already has `closure_subset`, a convenience
constructor from a `BMol` plus `IsCompact (closure g.U)` may be added if it remains
small and fully proved.

## Verification

Run:

```bash
lake env lean Mlc/GenuineBMol.lean
lake build
```

Search the changed module for `axiom`, `sorry`, and `admit`; inspect the exact diff
and full `git status --short`.

## Result report

Write `plan/GPT54_RESULT_16_CORRECT_GENUINE_BMOL_COMPACT_CONTAINMENT.md` with the
corrected signatures, verification outcomes, changed files, complete status, and
confirmation that no commit was made.
