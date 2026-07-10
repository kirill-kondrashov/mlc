# GPT-5.4 Worker Task 03: Audit the parapuzzle interface and parameter classes

**Repository:** `/home/kir/pers/mlc`  
**Mode:** read-only except for the result report  
**Result file:** `plan/GPT54_RESULT_03_PARAPUZZLE_INTERFACE_AUDIT.md`

## Communication

Write first to `plan/.GPT54_RESULT_03_PARAPUZZLE_INTERFACE_AUDIT.md.tmp`, then
atomically rename it to the final path. Do not commit. Do not edit Lean sources,
existing plans, README, notebooks, or previous task/review/result files.

## Goal

Determine whether the repository's `ParaPuzzlePieceAt` and the claimed
parameter↔dynamical correspondence match the classical parapuzzle object closely
enough to support a real, finite-level connectivity theorem. Identify the next
smallest non-circular formalization target. Do not implement it yet.

## Tasks

### A. Definition and equality audit

Trace the exact definition of `ParaPuzzlePieceAt` to primitives. Report its full
type and every definitional/theorem equality used to identify it with

```lean
{c' | green_function c (c' - c) < (1 / 2 : ℝ)^n}.
```

Determine whether this is merely a translated *fixed-base dynamical* sublevel or
whether it contains any moving-parameter critical-orbit, ray, wake, or puzzle
graph data. State the answer directly and support it with exact declarations.

### B. Inventory genuine parapuzzle infrastructure

Search all project and imported `Yoccoz` Lean sources for definitions/theorems
representing:

- parameter wakes or parapuzzle domains;
- moving dynamical puzzle graphs;
- parameter rays/equipotentials;
- phase-parameter maps;
- holomorphic motions indexed by the parameter;
- component/separation characterizations of parameter pieces.

For every candidate, give exact file, line, theorem type, dependencies, and
whether it contains mathematical content or only packages an assumption.

### C. Class coverage and dependency audit

Trace which parameter classes occur on the route to `mlc_conjecture`:

- finitely renormalizable;
- infinitely renormalizable branches/towers;
- neutral/Siegel/parabolic cases if represented;
- the residual virtual near-molecule package.

For each class, identify where parameter-piece connectivity and shrinking enter,
and whether the code proves them, assumes them, or transports them from another
hook. Do not infer literature coverage merely from docstrings.

### D. Assess the current target

Determine, from repository definitions alone, whether
`green_sublevel_translate_inter_mandelbrot_connected_straddling` is:

1. a standard finite-level classical parapuzzle connectivity theorem;
2. a stronger statement about an artificial fixed-base Green translate;
3. equivalent to or implied by another explicit project hook; or
4. unresolved from the code inspection.

Explain the evidence and distinguish formal conclusions from mathematical
interpretation.

### E. Propose the next implementation milestone

Give two candidate theorem signatures:

1. the smallest honest restricted theorem supported by existing definitions;
2. the first missing definition/theorem needed for a genuine finite-level
   parapuzzle construction.

For each, specify parameter hypotheses, dependencies, expected consumer, and why
it is not circular. Reject any signature whose assumptions already imply the
target by exact-image or packaged-connectivity clauses.

## Required verification and report contents

The report must include:

1. executive verdict;
2. definition/equality trace;
3. genuine-infrastructure inventory;
4. parameter-class dependency table;
5. assessment of the current target;
6. proposed next signatures;
7. exact commands run;
8. complete `git status --short` output;
9. explicit confirmation of no source/plan edits, no axiom/sorry/admit, and no
   commit.

Use `rg`/`rg --files` for searches. This task does not authorize web browsing;
flag literature claims requiring sourced external verification.

The final result file is the completion signal. Stop after creating it.
