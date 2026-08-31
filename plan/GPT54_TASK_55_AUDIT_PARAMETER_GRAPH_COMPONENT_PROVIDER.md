# TASK 55 — Audit the finite parameter-graph/component provider

## Global context

The target remains:

```lean
MLC.green_sublevel_translate_inter_mandelbrot_connected_straddling
```

The recommended route is dependency removal through genuine moving parameter
pieces:

```text
parameter graph
→ open complement component
→ relative Mandelbrot connectedness
→ generic local-connectivity consumer
→ remove frozen straddling axiom
```

Result 54 established only a weak ambient window:

```lean
finiteMovingParameterWindow F = F.parameterSet
```

This is not a finite parapuzzle window. A genuine next object must come from
parameter-plane graph geometry or a checked proper/unfolded/equipped family
theorem.

## Deliverable

Audit the repository and local sources for a concrete provider of:

```lean
parameterGraph n : Set ℂ
parameterOpenPiece n base : Set ℂ
```

The intended mathematical shape is:

```text
finite parameter rays/equipotentials/landing data
→ finite graph
→ open complement
→ connected component containing a base parameter
```

Alternatively, accept a source-defined proper unfolded equipped quadratic-like
family only if its parameter domain is already a checked intended finite
window, not merely an abstract open set.

Choose one outcome.

### Outcome A — Minimal concrete graph/component implementation

If checked definitions support it, implement the smallest actual graph and
component objects and prove only elementary topology:

- graph/complement definitions;
- complement openness where available;
- component basepoint membership;
- component connectedness/preconnectedness.

### Outcome B — Exact blocker

If the repository lacks a parameter-plane external coordinate, parameter rays,
landing data, or a concrete proper-family window, do not add a shell. Report:

- the exact first missing declaration/theorem;
- why fixed-parameter dynamical Böttcher objects do not suffice;
- the smallest next foundation task.

## Constraints

- Do not use `green_function c (c' - c)` as the new graph/piece definition.
- Do not identify dynamical rays with parameter rays.
- Do not claim source theorems are formalized when they are only in PDFs.
- No `sorry`, `admit`, or new axiom.
- Preserve the Result 53 window/locus API.
- Do not edit unrelated files or commit.

## Verification

For Outcome A, run focused Lean checks, then:

```bash
lake build
lake env lean check_axioms.lean
```

For Outcome B, compile all probes used in the audit and report their exact
commands/results.

## Result report

Write:

`plan/GPT54_RESULT_55_AUDIT_PARAMETER_GRAPH_COMPONENT_PROVIDER.md`

State the concrete graph/provider or the precise blocker and next task.
