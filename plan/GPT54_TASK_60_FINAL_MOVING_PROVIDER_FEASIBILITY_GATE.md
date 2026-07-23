# TASK 60 — Final moving-provider feasibility gate

## Purpose

The project has already separated the generic moving-window consumer path from
the frozen para-puzzle source. The remaining question is whether an honest
provider is already derivable from existing checked code.

The target is:

```lean
FiniteMovingWindowProviderData :=
  ∀ c hc hfin, ∃ W K,
    ConnectednessWindowParameterPieceData c W K
```

where `W` is genuinely an ambient moving parameter-window family and includes
openness, basepoint membership, basis/shrinkage, and connectedness of
`W n ∩ MandelbrotSet`.

## Audit scope

Search the full imported project for existing sources of all four requirements:

1. open parameter windows;
2. membership and basis/shrinkage;
3. relative Mandelbrot connectedness;
4. genuine moving/parapuzzle meaning.

Inspect Yoccoz finite-side declarations, boundary-motion modules, BMol family
definitions, analytic family core, and any parameter graph/ray/component code.

Reject as providers:

- `ParaPuzzlePieceAt` under a new name;
- transport data whose connectedness comes from the frontier axiom;
- a family `parameterSet` without topology/shrinkage;
- dynamical-plane Böttcher data without a parameter-plane phase–parameter bridge;
- an abstract structure with fields merely restating the target.

## Decision

If all requirements are available without the frontier axiom, implement the
smallest provider theorem and route the actual root through the new moving-window
main route. Preserve the residual molecule axiom and verify the new frontier.

Otherwise, do not edit source code. Produce a hard-stop report identifying the
first missing theorem and why the remaining code cannot derive it.

## Constraints

- No new axiom, `sorry`, or `admit`.
- No fabricated geometry or renamed frozen provider.
- Do not resume local Böttcher scaffolding.
- Do not commit.

## Result

Write:

`plan/GPT54_RESULT_60_FINAL_MOVING_PROVIDER_FEASIBILITY_GATE.md`

State whether the frontier axiom can be deleted at this point and give the
shortest mathematically honest next route if it cannot.
