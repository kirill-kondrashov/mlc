# GPT-5.4 Worker Task 02: Formalize the carving-motion no-go theorem

**Repository:** `/home/kir/pers/mlc`  
**Authorized source edit:** `Mlc/ParaPuzzleCarvingReduction.lean` only  
**Result file:** `plan/GPT54_RESULT_02_FORMALIZE_CARVING_NOGO.md`

## Communication

Write the report first to
`plan/.GPT54_RESULT_02_FORMALIZE_CARVING_NOGO.md.tmp`, then atomically rename it
to the final result path. Do not commit or communicate through copied CLI text.

## Goal

Add a sorry-free theorem of this shape:

```lean
theorem not_paraPieceCarvedByMotion_of_straddling
    {c : ℂ} (hc : c ∈ MandelbrotSet) (n : ℕ)
    (hstraddle : ¬ ({c' | green_function c (c' - c) < (1 / 2 : ℝ) ^ n}
      ⊆ MandelbrotSet)) :
    ¬ ParaPieceCarvedByMotion c n
```

Minor binder changes are allowed. Do not alter `ParaPieceCarvedByMotion`, the
frontier axiom, or downstream theorems.

## Required proof architecture

1. Prove a small helper that a time slice of `SpaceHolomorphicMotion` maps an
   open source to an open image.
2. Obtain local analyticity from `h_space_holo`, `hU_open`, and `hEU`.
3. Use local complex open mapping and `h_inj` to exclude local constancy.
4. Prove the target intersection is not open by relative clopen contradiction:
   connectedness from `green_sublevel_translate_connected hc n`, the inside
   point `c`, an outside point from `hstraddle`, and closedness of
   `MandelbrotSet`.
5. Contradict the exact image equality in the carving witness.

A different architecture is allowed only if the report verifies its APIs and
explains why it is simpler.

## Constraints

- No new `axiom`, `sorry`, `admit`, or target-strength hook.
- Edit only the authorized Lean file plus the result report.
- A necessary Mathlib import in that file is allowed.
- Preserve existing changes; do not commit.
- Do not attempt to discharge or modify the frontier axiom.

## Verification

Run at minimum:

```bash
lake env lean Mlc/ParaPuzzleCarvingReduction.lean
```

If practical, run a focused `#print axioms` check for the new theorem. Inspect
the final diff and `git status --short`.

## Result report

Report final theorem types, proof architecture, files changed, exact verification
results, remaining concerns, diff summary with line references, and explicit
confirmation of no axiom/sorry/admit, no frontier change, and no commit.

The atomic appearance of the final result file is the completion signal. Stop
afterward.
