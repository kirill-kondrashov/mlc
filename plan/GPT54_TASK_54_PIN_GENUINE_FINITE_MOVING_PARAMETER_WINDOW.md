# TASK 54 — Pin a genuine finite moving parameter window

## Global context

The live frontier remains:

```lean
MLC.green_sublevel_translate_inter_mandelbrot_connected_straddling
```

The current credible route is:

```text
genuine finite moving parameter window
→ connected relative window∩M
→ generic local-connectivity consumer
→ migrate downstream definitions
→ remove the frozen straddling axiom
```

Result 53 provides the corrected consumer-facing split:

```text
W n = open ambient window
K n = connectedness locus inside W n
```

The repository still has no verified concrete parameter-ray/equipotential graph
or proper unfolded equipped quadratic-like parameter window.

## Deliverable

Audit the exact repository/source support for one finite moving window. Search
and inspect:

- parameter external-coordinate/ray/equipotential declarations;
- `AnalyticQuadraticLikeFamilyCore`;
- `BMolParameterFamily`;
- any checked proper/unfolded/equipped family data;
- local reference statements specifying finite windows, wakes, roots, tips, or
  little-copy domains.

Choose one honest outcome.

### Outcome A — Minimal concrete window

Implement a focused definition of an actual `Set ℂ` representing a finite
moving parameter window, with elementary checked facts available from the
provider. It may be:

- a component of a complement of an explicitly defined finite graph; or
- a parameter domain supplied by a genuinely defined quadratic-like family.

At minimum, expose its basepoint and prove openness only if the current
definitions support it.

### Outcome B — Exact blocker

If neither candidate can be defined without inventing missing geometry, leave
sources unchanged and identify the first missing declaration/theorem. Explain
why existing dynamical Böttcher or incomplete family objects do not suffice, and
specify the smallest next task.

## Constraints

- Do not use the frozen Green translate.
- Do not define a window as an arbitrary `Set ℂ` with only abstract topology
  fields.
- Do not claim the source’s deep phase–parameter or connectedness theorem is
  formalized.
- No `sorry`, `admit`, or new axiom.
- Preserve Result 53’s window/locus split.
- Do not edit unrelated files or commit.

## Verification

For Outcome A, run focused checks, then:

```bash
lake build
lake env lean check_axioms.lean
```

For Outcome B, compile all probes used to establish the blocker and report the
exact commands/results.

## Result report

Write:

`plan/GPT54_RESULT_54_PIN_GENUINE_FINITE_MOVING_PARAMETER_WINDOW.md`

Report the concrete window/provider or the exact missing foundation, and state
which hypotheses are still needed before it can feed
`ConnectednessWindowParameterPieceData`.
