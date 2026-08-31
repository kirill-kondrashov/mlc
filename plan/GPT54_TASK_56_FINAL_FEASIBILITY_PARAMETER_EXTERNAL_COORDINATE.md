# TASK 56 — Final feasibility gate for the parameter external coordinate

## Global context

The live frontier is still:

```lean
MLC.green_sublevel_translate_inter_mandelbrot_connected_straddling
```

The moving-parameter replacement route now has:

- a generic open-window/local-connectivity consumer;
- an honest connectedness-locus definition;
- an honest ambient family-domain window;
- no finite parameter graph;
- no parameter rays/equipotentials;
- no parameter-plane external coordinate.

The remaining first foundation is the genuine whole-basin Böttcher evaluation
needed for:

```lean
parameterExternalCoord : {c : ℂ // c ∉ MandelbrotSet} → ℂ
```

## Deliverable

Audit whether the current repository can construct, for every
`c ∉ MandelbrotSet`, a canonical value obtained by extending the near-infinity
Böttcher coordinate to the basin and evaluating at `z = c`.

Use the existing checked declarations, especially:

```lean
LogSeriesBasinExtensionDataFor
EscapeTimeIndependentPullbackDataFor
MonodromyTrivialPullbackDataFor
```

and the local finite-level branch infrastructure. Track the exact logical
requirements:

1. critical value lies in the basin;
2. local pullback branches exist;
3. branches agree on connected overlaps after root-of-unity alignment;
4. finite continuations assemble along arbitrary basin paths;
5. endpoint monodromy is controlled;
6. the global value is holomorphic and agrees near infinity.

Choose one outcome:

### Outcome A — Honest minimal implementation

Only if all required bridges are already available, define the parameter
external coordinate and prove its basic exterior-valuedness/domain property.

### Outcome B — Exact final blocker

If any bridge is absent, do not add a placeholder or new axiom. Identify the
first missing theorem and explain why the completed finite local infrastructure
does not discharge it.

## Constraints

- Do not use `basinLogSeriesExtensionCandidate` as a genuine coordinate.
- Do not infer global monodromy from the finite mesh chain alone.
- Do not use the vacuous one-cell punctured-plane chart as continuation.
- No `sorry`, `admit`, or new axiom.
- No unrelated source edits or commit.

## Verification

For Outcome A, run:

```bash
lake build
lake env lean check_axioms.lean
```

For Outcome B, compile the probes used to establish the blocker and report
exact commands/results.

## Result report

Write:

`plan/GPT54_RESULT_56_FINAL_FEASIBILITY_PARAMETER_EXTERNAL_COORDINATE.md`

State whether the parameter coordinate can be implemented and, if not, the
precise theorem/data package that remains beyond the current code.
