# GPT-5.4 Worker Task 01: Parameter-connectivity specification audit

**Role:** implementation/audit worker  
**Repository:** `/home/kir/pers/mlc`  
**Mode:** read-only for repository sources and plans  
**Result file:** `plan/GPT54_RESULT_01_PARAMETER_CONNECTIVITY_AUDIT.md`

## File-based communication protocol

Do not wait for anyone to copy terminal output or chat text between sessions.
Communicate the complete result by creating:

```text
plan/GPT54_RESULT_01_PARAMETER_CONNECTIVITY_AUDIT.md
```

Write the result to a temporary sibling file first:

```text
plan/.GPT54_RESULT_01_PARAMETER_CONNECTIVITY_AUDIT.md.tmp
```

and rename it to the final result path only when the report is complete. This
prevents the supervising session from reviewing a partially written report.

For this task, do not edit Lean sources, existing plan files, or any other
repository file. The result report is the sole authorized repository change.
Do not commit it.

## Goal

Audit the proposed `ParaPieceCarvedByMotion` route and determine the precise
Lean-level statement of the open-mapping obstruction. Do not attempt to prove
the frontier axiom.

## Relevant files

- `Mlc/ParaPuzzleCarvingReduction.lean`
- `Mlc/ParaPuzzleConnectivity.lean`
- `Mlc/Quadratic/Complex/Bottcher/Slodkowski.lean`
- `Mlc/Quadratic/Complex/ParaPuzzleBasis.lean`
- `Mlc/Quadratic/Complex/Axioms.lean`

Let

```lean
S(c,n) := {c' | green_function c (c' - c) < (1 / 2 : ℝ) ^ n}.
```

The suspected obstruction is:

1. `S(c,n)` is open, connected, and contains `c`.
2. A time slice of `SpaceHolomorphicMotion` is injective on `S(c,n)` and
   differentiable/holomorphic on an open superset.
3. Therefore its image of `S(c,n)` is open, by complex open mapping.
4. Under `c ∈ MandelbrotSet` and `¬ S(c,n) ⊆ MandelbrotSet`, the intersection
   `S(c,n) ∩ MandelbrotSet` is not open.
5. Hence `ParaPieceCarvedByMotion c n` is impossible in the straddling case.

## Tasks

### A. Check the mathematical argument

Inspect the exact definitions and report whether every step above is correct.
Pay particular attention to:

- whether `SpaceHolomorphicMotion` gives holomorphy on `S` itself or only on a
  larger set `U`;
- whether `U` is open;
- whether injectivity on `S` establishes the nonconstancy needed by open mapping;
- whether open mapping must be applied locally or componentwise;
- how to construct a point of `S ∩ frontier MandelbrotSet` from the straddling
  hypotheses, rather than merely asserting that such a point exists.

### B. Locate exact Mathlib APIs

Find and report exact theorem names and types for:

- openness of strict-sublevel preimages;
- complex open mapping for a differentiable or holomorphic nonconstant map;
- connected open subsets of `ℂ` being path connected, if that route is needed;
- showing that an open connected `S`, containing one point of a closed set `M`
  and one point outside `M`, makes `S ∩ M` non-open.

Mark every candidate theorem as either **confirmed** or **unconfirmed**. Include
the import that exposes each confirmed theorem. Do not infer theorem signatures
from memory.

### C. Reuse repository lemmas

Search for existing declarations proving or supplying:

- `IsOpen S(c,n)`;
- `IsConnected S(c,n)`;
- `c ∈ S(c,n)`;
- `IsClosed MandelbrotSet`.

Give exact declaration names, types, files, and line numbers. Identify any hidden
axiom dependencies relevant to the proposed no-go theorem.

### D. Propose theorem signatures

Propose the smallest useful no-go theorem signature. Prefer:

1. a reusable general topological or complex-analytic lemma; and
2. a short specialization proving the incompatibility of
   `ParaPieceCarvedByMotion` with the straddling hypothesis.

Do not implement these theorems in this task. Explain why each hypothesis is
needed and which confirmed API would prove it.

### E. Audit the claimed relationship to classical Yoccoz theory and MLC

Audit the claim that the universal connectivity target is merely the established
finitely-renormalizable Yoccoz theorem.

Trace the repository dependency from the connectivity declaration, together
with shrinking and classification inputs, to `LocallyConnectedAt` or
`mlc_conjecture`. Report exact declarations and file locations. Clearly separate:

- facts proved by the code;
- mathematical inferences from the architecture;
- literature claims that cannot be verified from repository contents.

Do not browse the web for this task. Flag literature questions for a later,
explicitly sourced audit.

## Required result-file structure

The final result file must contain these sections:

1. `## Executive finding`
2. `## Corrections to the suspected argument`
3. `## Declarations inspected`
4. `## Confirmed Mathlib APIs`
5. `## Unconfirmed or missing APIs`
6. `## Proposed Lean theorem signatures`
7. `## Dependency trace toward MLC`
8. `## Blockers`
   - mathematical;
   - missing repository definitions;
   - Mathlib/API;
   - proof engineering.
9. `## Commands and verification`
10. `## Change-safety confirmation`

In the final section, explicitly confirm all of the following:

- no Lean source was edited;
- no existing plan or documentation file was edited;
- the result file is the only repository change made by this task;
- no `axiom`, `sorry`, `admit`, or equivalent target-strength hypothesis was
  introduced;
- no commit was created.

Include `git status --short` output in the report so the supervisor can distinguish
pre-existing workspace changes from the result file.

## Completion signal

The atomic rename to

```text
plan/GPT54_RESULT_01_PARAMETER_CONNECTIVITY_AUDIT.md
```

is the completion signal. After creating it, stop. Do not begin implementation
or modify PLAN 04 without a new task file from the supervising session.
