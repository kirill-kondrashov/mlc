# GPT-5.4 Worker Task 19: Directly verify the quadratic-like family source definition

**Repository:** `/home/kir/pers/mlc`
**Mode:** read-only focused source verification
**Result file:** `plan/GPT54_RESULT_19_DIRECT_SOURCE_CHECK_QUADRATIC_LIKE_FAMILY.md`

## Safety

Write only the result report, via atomic rename. Do not edit Lean sources,
dependencies, plans, or prior artifacts; do not commit. Temporary extracted text
may be written only under `/tmp`.

Read Result 18 and Supervisor Review 18.

## Goal

Directly inspect the local Lyubich PDF and determine whether Result 18's compiled
minimal structure faithfully represents the bare quadratic-like family data.
This task is source verification, not another indirect summary and not an
implementation task.

## A. Reliable extraction

Convert the entire PDF to `/tmp` text and search that text for:

- `42.1`, `Quadratic-like families`, or the actual subsection heading;
- `Theorem 10.1`;
- `tube`, `proper`, `unfolded`, `equipped`, `tubing`;
- the definition of `M(g)`.

Useful prior full-text ranges were approximately `10580–10740`, but locate the
strings independently. Report exact commands and exact extracted line ranges.
Do not stop after a wrong page/range; continue until the definitions themselves
are found or demonstrate precisely that the local PDF text layer is unusable.

## B. Exact definition table

For each of the following, provide a short compliant quote, extracted-text line
location, and precise paraphrase:

1. tube over a parameter domain and its fiber/trivialization/projection data;
2. quadratic-like family;
3. proper family;
4. unfolded family;
5. equipped family, holomorphic motion, and tubing;
6. connectedness locus `M(g)`.

Separate bare-family fields from Theorem 10.1 hypotheses and later equipment.

## C. Validate Result 18 field-by-field

Compare the directly extracted definition with each proposed primitive field:

- open `parameterSet`;
- subtype-indexed `fiber : parameterSet → GenuineBMol`;
- open/scoped `totalU`, `totalV`;
- section equality with fiber domains;
- global representative `eval` and on-source agreement;
- `AnalyticOn ℂ eval totalU`.

Identify every source requirement absent from the skeleton and decide whether it
belongs in the minimal analytic-family structure or a later proper/unfolded/
equipped layer.

Pay special attention to whether a “tube” includes a fiber-preserving
trivialization/homeomorphism or boundary regularity beyond openness and sections.

## D. Final corrected signature

If direct evidence supports Result 18, reproduce its implementation-ready
signature and say no change is needed. If not, give a corrected compile-oriented
signature and compile-test it under `/tmp` with `lake env lean`.

Do not store derived sections as fields and do not permit total-space components
outside the parameter domain.

## E. Decision

Choose exactly one:

1. direct source confirms the Result 18 skeleton is ready for implementation;
2. one named tube/family field must be added before implementation;
3. the local source definition cannot be recovered reliably enough to proceed.

Give the exact next worker task but do not create its file.

## Report contract

Include commands, direct line locations, quotes/paraphrases, any temporary compile
outcome, complete `git status --short`, and confirmation that only the result
artifact was written and no commit was made.
