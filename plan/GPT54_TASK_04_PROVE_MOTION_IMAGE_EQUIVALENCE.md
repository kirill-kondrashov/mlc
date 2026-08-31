# GPT-5.4 Worker Task 04: Prove the motion-image predicate is circular

**Repository:** `/home/kir/pers/mlc`  
**Authorized Lean edit:** `Mlc/Quadratic/Complex/Bottcher/Slodkowski.lean` only  
**Result file:** `plan/GPT54_RESULT_04_PROVE_MOTION_IMAGE_EQUIVALENCE.md`

## Communication

Write the report through a temporary sibling and atomically rename it to the
final path. Do not commit or use copied CLI communication.

## Goal

Prove, without axioms or sorry, that `ParaPieceIsMotionImage c n` is equivalent
to connectivity of its exact target:

```lean
theorem paraPieceIsMotionImage_iff_connected (c : ℂ) (n : ℕ) :
    ParaPieceIsMotionImage c n ↔
      IsConnected
        ({c' | green_function c (c' - c) < (1 / 2 : ℝ) ^ n} ∩ MandelbrotSet)
```

The forward direction should reuse
`isConnected_greenSublevel_inter_mandelbrot_of_motionImage`.

For the reverse direction, construct an identity `SpaceHolomorphicMotion E` for
an arbitrary set `E`, with `f t z = z`, holomorphy domain `Set.univ`, and choose
`t = 0`. You may first add a reusable definition such as

```lean
noncomputable def identitySpaceHolomorphicMotion (E : Set ℂ) :
    SpaceHolomorphicMotion E
```

if no equivalent declaration already exists. Search first and reuse an existing
one if present.

## Purpose and documentation

The theorem is a guardrail showing that `ParaPieceIsMotionImage` is connectivity
packaging, not a smaller Douady–Hubbard input. Update only its nearby docstring or
add a docstring to the equivalence theorem. Do not rewrite unrelated historical
comments in this task.

## Constraints

- No new axiom, sorry, admit, or target-strength helper assumption.
- Do not alter existing definitions or theorem statements.
- Edit only the authorized Lean file and the result report.
- Do not modify the frontier axiom, PLAN 04, README, notebooks, or previous task
  artifacts.
- Preserve all pre-existing workspace changes; do not commit.

## Verification

Run:

```bash
lake env lean Mlc/Quadratic/Complex/Bottcher/Slodkowski.lean
make build
make check
```

Report exact outcomes, the final theorem type, full source diff or precise line
references, and complete `git status --short`. Explicitly confirm no
axiom/sorry/admit, no frontier change, and no commit.

The final result file is the completion signal. Stop after creating it.
