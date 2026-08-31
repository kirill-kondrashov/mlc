# TASK 41 — Build or precisely block the parameter external-coordinate foundation

## Global context

The live frontier is:

```lean
MLC.green_sublevel_translate_inter_mandelbrot_connected_straddling
```

The current theorem proves the unrestricted Green-sublevel intersection by
splitting into:

1. the subset case, already discharged;
2. the straddling case, which still invokes the frontier axiom.

The repository audit concluded that the exact frozen-base theorem is not matched
by a verified classical parapuzzle theorem. The credible route is therefore to
replace the frozen surrogate by genuine moving parameter geometry:

```text
parameter external coordinate
→ parameter rays/equipotentials
→ finite parameter graph
→ component-defined parapuzzle piece
→ connected relative piece
→ downstream consumer migration
→ remove the frontier axiom
```

The first missing foundation is the parameter-plane external coordinate
`Φ_M(c) = B_c(c)` on the complement of the Mandelbrot set. Existing
`external_ray_map c`, `proxy_bottcher_map c`, and `BottcherParamInverse` objects
are primarily fixed-parameter dynamical-plane objects and must not be relabeled
as parameter-plane uniformization.

## Deliverable

First perform a feasibility audit against the checked repository APIs and the
local references. Then choose exactly one outcome:

### Outcome A — Minimal implementation

Only if the existing checked declarations genuinely support evaluation of the
fiber Böttcher coordinate at the critical value for `c ∉ MandelbrotSet`, create a
focused module defining:

```lean
parameterExternalCoord : {c : ℂ // c ∉ MandelbrotSet} → ℂ
```

and prove the smallest honest facts available, beginning with:

```lean
1 < ‖parameterExternalCoord c‖
```

Use existing definitions and theorem names rather than duplicating Böttcher
logic. Register the module in `Mlc.lean` in dependency order. Do not implement
parameter rays, equipotentials, finite graphs, or connectivity yet.

### Outcome B — Exact blocker

If the evaluation/well-definedness bridge is absent, make no source change.
Identify the first missing theorem or data structure precisely, explain why the
existing dynamical Böttcher declarations do not provide it, and specify the
smallest next worker task. A blocker is preferable to an unsound placeholder.

## Required constraints

- No `sorry`, `admit`, or declaration-level `axiom`.
- Do not use `basinLogSeriesExtensionCandidate` as a global parameter coordinate.
- Do not identify a fixed-`c` dynamical external ray map with a parameter ray.
- Do not define the coordinate as an abstract field with no mathematical provider.
- Do not edit `ParaPuzzleConnectivity.lean` or delete the frontier axiom yet.
- Do not resume the basin overlap/monodromy implementation in this task.
- Do not edit unrelated modules.
- Do not commit.

## Verification

For Outcome A, run:

```bash
lake build
lake env lean check_axioms.lean
```

The axiom frontier must remain unchanged. For Outcome B, compile every temporary
probe used for the audit and report the exact command/result.

## Result report

Write:

`plan/GPT54_RESULT_41_BUILD_PARAMETER_EXTERNAL_COORDINATE_FOUNDATION.md`

The report must state:

- whether Outcome A or Outcome B was selected;
- the exact checked declarations used;
- the exact missing bridge if blocked;
- how the result advances the moving-parameter replacement route;
- the next smallest worker task.
