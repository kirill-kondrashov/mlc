# GPT-5.4 Worker Task 07: Reproducible full-domain connectivity screening

**Repository:** `/home/kir/pers/mlc`  
**Mode:** read-only repository; numerical work under `/tmp`  
**Result file:** `plan/GPT54_RESULT_07_REPRODUCIBLE_FULL_DOMAIN_SCREENING.md`

## Communication and authorized writes

Write only the result report in the repository, using an atomic temporary-file
rename. Store scripts/data/images under `/tmp`. Do not edit repository sources,
plans, or prior artifacts; do not commit.

## Goal

Correct the methodological defects in Task 06 and decide whether the rabbit or
basilica secondary components persist when connectivity is computed on a domain
known to contain the entire target intersection.

This remains screening, not proof.

## Required experiment

### 1. Whole-target spatial domain

Use a square covering the repository's proved bound
`MandelbrotSet ⊆ closedBall 0 2`, with a small pixel margin, for example
`[-2.05,2.05]²`. Because the target is intersected with `M`, this contains the
entire true target. Do not infer connectivity from smaller crops.

### 2. Cases

At minimum run:

- `c = -1` (basilica), `n = 1,2,3`;
- rabbit approximation `c = -0.122561 + 0.744862 i`, `n = 1,2,3`;
- controls `c = 0` and `c = 0.25`, at least `n = 1,2`.

Explicitly label the rabbit experiments conditional on the approximate base
being in `M`; do not claim the theorem hypothesis is certified.

### 3. Resolution and iteration matrix

Use at least:

- resolutions `256²`, `512²`, and `1024²` if runtime permits; otherwise explain
  the measured resource limit;
- Mandelbrot iteration cutoffs `300` and `1000`;
- the same documented Green approximation parameters across comparisons.

### 4. Connectivity diagnostics

For every run report:

- component counts and sizes under both 4-neighbor and 8-neighbor adjacency;
- bounding box of every component above a stated size threshold;
- whether each component touches the outer grid boundary;
- minimum pixel/Chebyshev distance between each secondary component and the main
  component;
- whether the result changes with resolution or iteration cutoff.

If any mask point touches the outer boundary, flag the domain/bound computation
as inconsistent and do not interpret the run.

### 5. Reproducibility

Create a standalone script under `/tmp`, not an inline heredoc. In the result
report include:

- the complete script source in a fenced code block (or, if extremely long, a
  precise self-contained pseudocode plus a SHA-256 and full `/tmp` path; complete
  source is preferred);
- Python and dependency versions;
- exact command lines;
- SHA-256 of the JSON/CSV result data;
- enough summarized tables that the supervisor need not trust prose.

Do not use unavailable third-party packages without first recording the failure.

## Interpretation rules

- A component caused by crop boundaries is disqualified; the whole-domain setup
  should eliminate this issue.
- Persistence across resolution/cutoff is evidence only, not proof.
- Finite non-escape is not certified `M` membership.
- Pixel adjacency cannot certify topological separation.
- Do not recommend interval certification unless a secondary component persists
  on the whole domain, under both adjacency conventions, and its pixel count
  scales roughly with area rather than collapsing.

## Required decision

Choose exactly one:

1. no robust whole-domain candidate remains—Option A is not numerically refuted;
2. a robust whole-domain candidate remains—propose one bounded certification
   task with exact boxes/separator geometry;
3. computation is inconclusive—identify the precise resource/API blocker.

Do not call Option A true or false.

## Report contract

Include:

1. executive decision;
2. correction of Task 06 crop issue;
3. exact method and reproducibility material;
4. complete summarized result tables;
5. component bounding boxes/boundary diagnostics;
6. robustness interpretation;
7. next-step recommendation;
8. exact commands and failures;
9. complete `git status --short`;
10. confirmation of no repository edits beyond the result, no
   axiom/sorry/admit, and no commit.

The final result file is the completion signal. Stop afterward.
