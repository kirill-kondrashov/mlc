# GPT-5.4 Worker Task 08: Sourced theorem-matching audit for Option A versus B

**Repository:** `/home/kir/pers/mlc`  
**Mode:** research/read-only; result report only  
**Result file:** `plan/GPT54_RESULT_08_SOURCED_THEOREM_MATCHING_AUDIT.md`

## Communication and safety

Write only the result report in the repository, via atomic rename. Do not edit
Lean sources, plans, docs, notebooks, or prior artifacts; do not commit.

This task explicitly authorizes literature lookup. Prefer primary sources:
original papers/monographs, author manuscripts, or precise theorem statements in
reputable surveys. Use repository `refs/` first. If internet tools are available,
use them; otherwise report the limitation and do not invent citations.

## Decision to support

Revised PLAN 04 requires choosing:

- **Option A:** retain the frozen-base target
  `{c' | G_c(c'-c) < 2^{-n}} ∩ M` and identify an independent theorem proving its
  connectivity; or
- **Option B:** replace/mediate it with a genuine finite-level parameter piece
  defined from parameter geometry.

The numerical screening found no counterexample but supplies no proof. Determine
whether established literature actually matches Option A's exact set.

## A. Normalize the repository target

State the target with every variable and hypothesis. Record exactly which
quantities are frozen at base `c` and which vary with `c'`. Compare it field by
field with classical definitions encountered in the literature:

- dynamical puzzle piece for `f_c`;
- parapuzzle/parameter puzzle piece containing `c`;
- parameter equipotential/ray/wake;
- phase-parameter map or critical-value condition for `f_{c'}`.

Produce a comparison table. Do not treat similar notation as equality.

## B. Primary-source theorem search

Locate precise statements for the finite-level connectivity/topology of
quadratic parapuzzle pieces and the parameter↔dynamical correspondence. For each
source give:

- full bibliographic identification and stable URL or repository ref path;
- theorem/proposition/section/page number;
- exact hypotheses and conclusion, paraphrased faithfully;
- whether the parameter-domain definition depends on the moving map `f_{c'}`;
- whether it states connectivity of the piece itself, its closure, its
  intersection with `M`, or something else.

Search especially for Douady–Hubbard/Yoccoz parapuzzles, phase-parameter
relations, and any claimed “wringing/tubing” result relevant to the exact target.

## C. Exact-match test for Option A

For every candidate theorem, attempt an explicit implication chain to

```text
IsConnected ({c' | G_c(c' - c) < 2^{-n}} ∩ M).
```

List every missing equality or inclusion. Classify each as:

- definitional;
- already proved in the repository;
- standard but requires formalization;
- unsupported;
- false/suspect.

An implication is accepted only if no step silently replaces frozen `G_c` by a
moving `G_{c'}` or replaces the translated Green sublevel with a parameter wake.

## D. Check the claimed global scope

Determine which parameter classes each sourced theorem covers: hyperbolic,
Misiurewicz, parabolic, finitely renormalizable, neutral/Siegel, infinitely
renormalizable, or all `c ∈ M`. Compare that scope to the universal quantifiers of
the repository axiom.

Do not say “Yoccoz proves it” without identifying the exact class and statement.

## E. Final decision

Choose exactly one:

1. **Option A matched:** cite a theorem and give a complete non-circular
   implication blueprint to the exact frozen-base target.
2. **Option A unmatched but potentially derivable:** identify the smallest
   genuinely new mathematical bridge and justify why it is plausible.
3. **Option B required:** classical theorems concern a different parameter object
   and no sourced implication to Option A exists.
4. **Inconclusive due to source access:** state exactly which source/page is still
   needed.

Then propose one next bounded Lean/research task. It must not use
`ParaPieceCarvedByMotion`, `ParaPieceIsMotionImage`, exact-image connected-source
existentials, or a packaged connectivity hypothesis.

## Citation and evidence rules

- Include direct links for web sources and exact paths for local refs.
- Quote no more than 25 words from any one source; paraphrase otherwise.
- Clearly mark inference versus source statement.
- Do not cite repository docstrings as literature evidence.
- If a source is secondary, label it secondary and do not use it as sole support
  for the final match.

## Report contract

Include:

1. executive decision;
2. normalized-target comparison table;
3. primary-source theorem inventory;
4. exact-match implication audits;
5. parameter-class coverage table;
6. final Option A/B decision;
7. next bounded task proposal;
8. exact searches/commands/tool limitations;
9. complete `git status --short`;
10. confirmation of no repository edits beyond the result, no
   axiom/sorry/admit, and no commit.

The final result file is the completion signal. Stop afterward.
