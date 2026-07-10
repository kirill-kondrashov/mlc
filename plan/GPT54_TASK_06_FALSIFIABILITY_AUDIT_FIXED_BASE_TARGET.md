# GPT-5.4 Worker Task 06: Falsifiability audit of the frozen-base target

**Repository:** `/home/kir/pers/mlc`  
**Mode:** read-only repository audit and reproducible numerical experiments  
**Result file:** `plan/GPT54_RESULT_06_FALSIFIABILITY_AUDIT_FIXED_BASE_TARGET.md`

## Authorized writes

- the result report;
- temporary numerical output under `/tmp` only.

Do not edit repository source, plans, documentation, notebooks, or scripts. Do
not commit. Write the final report through an atomic temporary-file rename.

## Goal

Assess whether Option A in revised PLAN 04—the universal connectivity of the
existing frozen-base set

```text
S(c,n) ∩ M,
S(c,n) = {c' | G_c(c' - c) < 2^{-n}},
```

for every `c ∈ M` and `n`—is mathematically plausible. Search for evidence of a
counterexample and distinguish rigorous falsification from pixel-grid artifacts.

This is not a request to prove or disprove MLC, and numerical disconnectedness
alone is not a proof.

## A. Locate and audit existing numerical work

Search all scripts, notebooks, plans, drafts, and generated notebook text for
experiments concerning:

- `green_sublevel_translate_inter_mandelbrot_connected`;
- the straddling case;
- connected components of translated Green sublevels intersected with `M`;
- the “program” previously used by Opus 4.8;
- claims that residual components are pixel noise.

Report exact paths, relevant functions/cells, parameters sampled, resolution,
escape cutoffs, and known limitations. Prefer `rg` and `rg --files`; if a tool is
unavailable, show the exact failed command and use a named fallback.

## B. Analyze structural plausibility

From definitions and basic Mandelbrot geometry, analyze whether an arbitrary
connected open neighborhood `S(c,n)` centered at `c` should have connected
intersection with `M`. Address:

- whether `S(c,n)` is convex, simply connected, full, or a topological disk;
- whether any proved property forces intersections with `M` to be connected;
- whether the family is known to be nested or a neighborhood basis;
- how satellite limbs, narrow necks, and holes in the complement could produce
  apparent or genuine separated intersections;
- why connectedness of `S` and `M` separately is insufficient.

Every statement must be tagged as checked from code, elementary inference, or
unverified dynamical intuition.

## C. Reproduce and strengthen numerical experiments

If an existing program is runnable without repository edits, run it on a
targeted suite including at least:

- `c = 0`, `-1`, and a main-cardioid boundary point;
- a basilica/root or satellite-near-neck parameter;
- the rabbit parameter used elsewhere in the repository;
- several levels `n`, especially genuinely straddling levels.

Use at least two spatial resolutions and two escape iteration cutoffs. Report
component sizes, pixel adjacency convention, bounding boxes, and whether small
components persist or converge toward the main component. Store bulky output in
`/tmp`, not the repository.

If no suitable program exists or dependencies prevent execution, do not create
one in the repository. Give a precise minimal experiment specification for the
next task instead.

## D. Counterexample certification criteria

State what would be needed to turn a numerical candidate into a rigorous
counterexample. At minimum discuss:

- certified inclusion of two compact subsets in `M ∩ S(c,n)`;
- a certified separating open set or crosscut lying in the complement of
  `M ∩ S(c,n)`;
- interval/error bounds for `G_c` and escape/non-escape claims;
- why finite non-escape iteration does not certify Mandelbrot membership;
- use of analytically certified hyperbolic components or known real slices where
  appropriate.

Do not call any candidate a counterexample unless these requirements are met.

## E. Decision recommendation

End with exactly one recommendation:

1. **Option A remains plausible**—state the independent theorem still needed;
2. **Option A is numerically suspect**—give the smallest rigorous certification
   task for the best candidate;
3. **Option A is formally/mathematically false**—only if a rigorous argument is
   actually supplied;
4. **Inconclusive**—state the precise missing computation or definition.

Also say whether PLAN 04 should next pursue Option A, switch to Option B, or run
one bounded certification task first.

## Required report contents

1. executive verdict;
2. inventory of existing programs/evidence;
3. structural analysis with evidence tags;
4. experiment method and complete summarized results;
5. strongest candidate and robustness checks;
6. rigorous-certification gap;
7. decision recommendation;
8. exact commands and failures;
9. complete `git status --short`;
10. confirmation of no repository edits, no axiom/sorry/admit, and no commit.

The final result file is the completion signal. Stop afterward.
