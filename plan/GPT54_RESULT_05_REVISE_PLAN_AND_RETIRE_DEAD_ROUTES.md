# GPT54 Result 05 — Revise PLAN 04 and retire dead routes

## 1. Executive result

Completed the documentation/specification task.

Updated only the authorized files:
- `plan/PLAN_04_parameter_connectivity.md`
- documentation comments in `Mlc/ParaPuzzleCarvingReduction.lean`
- documentation comments in `Mlc/Quadratic/Complex/Bottcher/Slodkowski.lean`

Substantive outcome:
- PLAN 04 now reflects the checked state after Tasks/Reviews 01–04.
- Dead-route claims are retired explicitly.
- The source comments now describe:
  - `ParaPieceCarvedByMotion` as a historically motivated but formally refuted route on the live straddling frontier, via `not_paraPieceCarvedByMotion_of_straddling`;
  - `ParaPieceIsMotionImage` as connectivity packaging, via `paraPieceIsMotionImage_iff_connected`.

## 2. PLAN 04 changes by section

### Title / goal rewrite

Replaced the old plan title and goal centered on the unrestricted theorem with a plan centered on the actual live frontier:

```lean
MLC.green_sublevel_translate_inter_mandelbrot_connected_straddling
```

This now states explicitly that the unrestricted theorem is derived and the remaining primitive frontier is the straddling axiom only.

### Checked formal facts section

Added a dedicated section distinguishing checked formal facts from interpretation. It now records:

1. the live frontier is only the straddling case;
2. `not_paraPieceCarvedByMotion_of_straddling` kills the carving route on the live stratum;
3. `paraPieceIsMotionImage_iff_connected` shows motion-image is equivalent to target connectedness, hence not a reduction;
4. `ParaPuzzlePieceAt c n` is a frozen-base translated dynamical/Green-sublevel object, not a genuine parameter wake/ray/component definition;
5. the route into `LocallyConnectedAt` plus shrinking does not justify calling the remaining gap a routine finitely-renormalizable Yoccoz formalization omission.

### Interpretation vs literature split

Added separate sections for:
- repository-internal mathematical interpretation;
- literature-sensitive questions requiring a separate sourced audit.

This prevents the plan from silently treating literature expectations as checked repo facts.

### Revised phases

PLAN 04 now uses the required phase structure:

- **Phase 0 — completed guardrails**
  - records both dead-route facts;
  - prohibits exact-image / connected-witness replacement hooks.
- **Phase 1 — choose and specify the intended parameter object**
  - Option A: keep the frozen-base translated-Green target and find an independent theorem implying its connectivity;
  - Option B: define a genuine finite-level parameter object and compare it to the current target only if justified.
- **Phase 2 — restricted canonical construction**
  - one explicit parameter class and one finite level;
  - source / boundary motion / phase map / target defined independently of connectedness;
  - connectivity from component/separation topology.
- **Phase 3 — classwise coverage audit and global assembly**
  - enumerate every class used by the MLC route;
  - mark each as proved in repo, literature-backed but unformalized, or genuinely open.

### Go / no-go criteria

Added explicit no-go rules forbidding resumption of routes based on:
- existential exact-image witnesses;
- connected-reference-set packaging;
- transport data equivalent to `∃ S, IsConnected S ∧ S = target`;
- motion-image predicates whose only consumer is target connectedness.

Also added the required analytic-infrastructure pause criterion:
- λ-lemma, Słodkowski, and full-basin Böttcher work should not resume for this frontier until a canonical independently defined geometric consumer exists.

### Updated success criteria

Added short-term and full success criteria matching the current frontier:
- next step must choose Option A or B explicitly;
- no new reduction can lean on `ParaPieceCarvedByMotion` or `ParaPieceIsMotionImage`;
- final success is removal of `MLC.green_sublevel_translate_inter_mandelbrot_connected_straddling` from `make check`, with no weaker replacement axiom.

## 3. Source docstrings changed

### `Mlc/ParaPuzzleCarvingReduction.lean`

1. Module header docstring (`lines 4–20` in current file view)
   - changed from “carving-motion reduction of frontier axiom A” language
   - now states the live frontier is the straddling axiom and that this file proves the no-go fact `not_paraPieceCarvedByMotion_of_straddling`
   - clearly labels carving as historically motivated but not a viable remaining reduction

2. `ParaPieceCarvedByMotion` docstring (`lines 29–35`)
   - now describes it as an **attempted** carving interface
   - explicitly points to `not_paraPieceCarvedByMotion_of_straddling`
   - says it should not be treated as a currently viable reduction route

3. `isConnected_greenSublevel_inter_mandelbrot_of_carvedByMotion` docstring (`lines 44–49`)
   - now describes the theorem as logically valid but unusable on the live straddling frontier
   - explicitly cites the refutation of the hypothesis by `not_paraPieceCarvedByMotion_of_straddling`

### `Mlc/Quadratic/Complex/Bottcher/Slodkowski.lean`

1. `ParaPieceIsMotionImage` docstring (`lines 87–95`)
   - now describes the predicate as a motion-image **packaging predicate for the current target**
   - explicitly states that by `paraPieceIsMotionImage_iff_connected` it is equivalent to connectedness of that target
   - warns that it is not a smaller reduction input
   - historical Douady–Hubbard / Yoccoz motivation is retained but clearly labeled historical

2. `isConnected_greenSublevel_inter_mandelbrot_of_motionImage` docstring (`lines 118–124`)
   - now describes the theorem as a **conditional image-connectivity theorem**
   - explicitly states that, via `paraPieceIsMotionImage_iff_connected`, its hypothesis is equivalent to its conclusion for the same target
   - therefore it should not be described as a genuine reduction of the live frontier

## 4. Exact verification outcomes

### `git diff --check`

Command run:

```bash
git diff --check
```

Outcome:
- **passed**
- no whitespace / conflict-marker issues reported

### `lake env lean Mlc/ParaPuzzleCarvingReduction.lean`

Command run:

```bash
lake env lean Mlc/ParaPuzzleCarvingReduction.lean
```

Outcome:
- **passed**

### `lake env lean Mlc/Quadratic/Complex/Bottcher/Slodkowski.lean`

Command run:

```bash
lake env lean Mlc/Quadratic/Complex/Bottcher/Slodkowski.lean
```

Outcome:
- **passed**
- emitted the same local linter warnings as before in `Slodkowski.lean` (`try 'simp' instead of 'simpa'`)

### `make check`

Command run:

```bash
make check
```

Outcome:
- **passed**
- reported the same axiom set as before:

```text
✅ The proof of 'MLC.mlc_conjecture' is free of 'sorry'.
All axioms used:
- Quot.sound
- propext
- Classical.choice
- MLC.green_sublevel_translate_inter_mandelbrot_connected_straddling
- MLC.residualOpenVirtualNearMoleculeAxiom
```

### Restricted diff inspection

I inspected `git diff` restricted to:
- `plan/PLAN_04_parameter_connectivity.md`
- `Mlc/ParaPuzzleCarvingReduction.lean`
- `Mlc/Quadratic/Complex/Bottcher/Slodkowski.lean`

Result:
- the `plan/PLAN_04_parameter_connectivity.md` diff is the expected documentation rewrite;
- the `Slodkowski.lean` changes from this task are docstring corrections;
- `ParaPuzzleCarvingReduction.lean` contains the already-existing Task 02/Task 05 workspace state, so the repository diff still shows earlier theorem/import additions alongside this task’s comment updates.

Important clarification for this task:
- I made **no new Lean code/import/theorem/definition edits** while executing Task 05;
- the Lean edits for Task 05 were documentation-comment updates only.

## 5. Complete `git status --short`

```text
M Mlc/ParaPuzzleCarvingReduction.lean
 M Mlc/Quadratic/Complex/Bottcher/Slodkowski.lean
 M plan/PLAN_04_parameter_connectivity.md
?? plan/GPT54_RESULT_01_PARAMETER_CONNECTIVITY_AUDIT.md
?? plan/GPT54_RESULT_02_FORMALIZE_CARVING_NOGO.md
?? plan/GPT54_RESULT_03_PARAPUZZLE_INTERFACE_AUDIT.md
?? plan/GPT54_RESULT_04_PROVE_MOTION_IMAGE_EQUIVALENCE.md
?? plan/GPT54_REVIEW_01_PARAMETER_CONNECTIVITY_AUDIT.md
?? plan/GPT54_REVIEW_02_FORMALIZE_CARVING_NOGO.md
?? plan/GPT54_REVIEW_03_PARAPUZZLE_INTERFACE_AUDIT.md
?? plan/GPT54_REVIEW_04_PROVE_MOTION_IMAGE_EQUIVALENCE.md
?? plan/GPT54_TASK_01_PARAMETER_CONNECTIVITY_AUDIT.md
?? plan/GPT54_TASK_02_FORMALIZE_CARVING_NOGO.md
?? plan/GPT54_TASK_03_PARAPUZZLE_INTERFACE_AUDIT.md
?? plan/GPT54_TASK_04_PROVE_MOTION_IMAGE_EQUIVALENCE.md
?? plan/GPT54_TASK_05_REVISE_PLAN_AND_RETIRE_DEAD_ROUTES.md
```

## 6. Explicit compliance confirmation

- No Lean definition, theorem statement, proof term, executable code, or import was changed by Task 05.
- No new `axiom`, `sorry`, or `admit` was introduced.
- The frontier is unchanged.
- No commit was created.
- Existing workspace changes were preserved.

## 7. Final note on current plan state

PLAN 04 is now aligned with the checked facts from Tasks/Reviews 01–04:
- carving is dead on the live stratum;
- motion-image is packaging, not reduction;
- the next real work must choose a canonical parameter object/theorem route instead of reviving exact-image existential interfaces.
