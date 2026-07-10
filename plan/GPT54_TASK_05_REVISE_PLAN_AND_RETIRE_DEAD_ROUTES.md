# GPT-5.4 Worker Task 05: Revise PLAN 04 and retire dead-route claims

**Repository:** `/home/kir/pers/mlc`  
**Authorized edits:**

- `plan/PLAN_04_parameter_connectivity.md`
- documentation comments only in
  `Mlc/ParaPuzzleCarvingReduction.lean`
- documentation comments only in
  `Mlc/Quadratic/Complex/Bottcher/Slodkowski.lean`

**Result file:** `plan/GPT54_RESULT_05_REVISE_PLAN_AND_RETIRE_DEAD_ROUTES.md`

## Communication

Write the result first to a temporary sibling file, then atomically rename it to
the final result path. Do not commit and do not rely on copied CLI/chat output.

## Goal

Bring the active plan and nearby source documentation into agreement with the
four checked audit/implementation results:

- `GPT54_RESULT_01_PARAMETER_CONNECTIVITY_AUDIT.md`
- `GPT54_RESULT_02_FORMALIZE_CARVING_NOGO.md`
- `GPT54_RESULT_03_PARAPUZZLE_INTERFACE_AUDIT.md`
- `GPT54_RESULT_04_PROVE_MOTION_IMAGE_EQUIVALENCE.md`

and supervisor reviews 01–04.

This is a documentation/specification task. Do not change any Lean definition,
theorem statement, proof term, import, axiom, or executable code.

## Required PLAN 04 corrections

Rewrite `plan/PLAN_04_parameter_connectivity.md` so it accurately records:

1. The live frontier is
   `green_sublevel_translate_inter_mandelbrot_connected_straddling`; the old
   unrestricted declaration is derived by the subset/straddling split.
2. `not_paraPieceCarvedByMotion_of_straddling` formally proves that
   `ParaPieceCarvedByMotion` is impossible on the live straddling stratum.
3. `paraPieceIsMotionImage_iff_connected` formally proves that
   `ParaPieceIsMotionImage` is equivalent to target connectedness and is not a
   reduction.
4. `ParaPuzzlePieceAt c n` is a translated frozen-base dynamical piece and, on
   `c ∈ M`, a translated frozen-base Green sublevel. It is not presently defined
   from parameter wakes, moving parameter graphs, parameter rays, or a
   phase-parameter component construction.
5. The universal target plus shrinking feeds into `LocallyConnectedAt`; calling
   it globally a routine finitely-renormalizable Yoccoz formalization gap is not
   justified by the repository.
6. Lambda-lemma, Słodkowski, and full-basin Böttcher development are paused for
   this goal until a canonical, independently defined geometric consumer exists.

The revised plan must distinguish:

- checked formal facts;
- mathematical interpretation;
- literature questions requiring a separate sourced audit.

## Required revised phases

PLAN 04 should give this concrete sequence:

### Phase 0 — completed guardrails

- record both formal dead-route theorems;
- prohibit exact-image/connected-witness replacement hooks.

### Phase 1 — choose and specify the intended parameter object

- either keep the frozen-base Green translate and identify an independent
  mathematical theorem that implies its intersection connectivity;
- or define a genuine finite-level parameter piece from independently specified
  parameter boundaries/wakes and a component construction.

### Phase 2 — restricted canonical construction

- choose one explicit parameter class and finite level;
- define the source, boundary motion/phase map, and target independently of
  connectedness;
- derive connectivity from component/separation topology.

### Phase 3 — classwise coverage audit and global assembly

- enumerate every class consumed by the MLC route;
- mark each proved, literature-backed but unformalized, or genuinely open;
- never hide uncovered content inside an exact-image existential or connectivity
  package.

Include strict go/no-go criteria for resuming analytic infrastructure work and
updated short-term/full success criteria.

## Source-docstring corrections

In the two authorized Lean files, update only comments/docstrings so that:

- `ParaPieceCarvedByMotion` is described as a refuted attempted interface, with a
  pointer to `not_paraPieceCarvedByMotion_of_straddling`;
- its conditional connectivity theorem is described as logically valid but
  unusable on the straddling frontier;
- `ParaPieceIsMotionImage` is described as connectivity packaging, with a pointer
  to `paraPieceIsMotionImage_iff_connected`;
- its image-connectivity theorem is not described as discharging/replacing the
  frontier by a smaller standard input;
- historical motivation may remain, but it must be clearly labelled historical
  and must not claim current feasibility.

Do not modify docstrings unrelated to these predicates.

## Constraints

- No Lean code or import changes.
- No new axiom, sorry, admit, definition, theorem, or hypothesis.
- Do not edit PLAN 00, README, notebooks, previous task artifacts, or any other
  file.
- Preserve all existing workspace changes; do not commit.

## Verification

Run:

```bash
git diff --check
lake env lean Mlc/ParaPuzzleCarvingReduction.lean
lake env lean Mlc/Quadratic/Complex/Bottcher/Slodkowski.lean
make check
```

Inspect `git diff` restricted to the three authorized files and confirm that the
two Lean diffs contain comment-only changes relative to the Task 04 workspace
state.

## Result report requirements

Report:

1. executive result;
2. PLAN 04 changes by section;
3. every source docstring changed, with line references;
4. exact verification outcomes;
5. complete `git status --short`;
6. explicit confirmation that no Lean code/import/theorem/definition changed,
   no axiom/sorry/admit was introduced, the frontier is unchanged, and no commit
   was created.

The final result file is the completion signal. Stop after creating it.
