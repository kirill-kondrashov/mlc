# TASK 61 — Formalize a sourced finite-level parapuzzle provider

## Objective

The generic moving-window route is now complete, but the source theorem it
expects is missing. This task begins the only credible mathematical route:
formalize a genuine finite-level parapuzzle provider from a precise classical
theorem.

Target:

```lean
FiniteMovingWindowProviderData :=
  ∀ (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet)
    (_h : FinitelyRenormalizable c),
    ∃ (W K : ℕ → Set ℂ),
      ConnectednessWindowParameterPieceData c W K
```

## Required stages

### Stage A — Select and state the source theorem

Choose a precise public classical theorem about finite-level quadratic
parapuzzle pieces near finitely renormalizable parameters. Record:

- citation/link or bibliographic identity;
- exact mathematical statement;
- which hypotheses correspond to the Lean target;
- whether it supplies relative connectedness, openness, nesting, and
  phase–parameter correspondence directly or through separate results.

### Stage B — Repository prerequisite audit

Inspect:

- `DynamicalPuzzlePiece`;
- `PuzzleBoundaryMotion`;
- external-ray, equipotential, and landing declarations;
- `BMolParameterFamily`;
- `AnalyticQuadraticLikeFamilyCore`;
- parameter graph/component structures.

Classify each as a usable prerequisite, a frozen wrapper, or an absent
theorem. Do not count abstract target structures as source theorems.

### Stage C — Focused formalization

If prerequisites genuinely exist, implement a new finite-level moving parapuzzle
object with:

1. ambient open windows `W n`;
2. basepoint membership;
3. nestedness or a neighborhood-basis/shrinkage theorem;
4. connectedness of `W n ∩ MandelbrotSet`;
5. a phase–parameter/combinatorial bridge.

Then add the smallest adapter to
`ConnectednessWindowParameterPieceData`.

Use existing naming and namespace conventions. Keep the frozen
`ParaPuzzlePieceAt` route intact for compatibility.

### Stage D — Hard stop if prerequisites are absent

If any decisive theorem is missing, make no speculative source edits. Report:

- the first missing formal theorem;
- why existing declarations do not prove it;
- the smallest prerequisite module and theorem statements required;
- whether the remaining work is mathematical formalization rather than Lean
  bookkeeping.

## Prohibited shortcuts

- No aliasing or relabelling of `ParaPuzzlePieceAt`.
- No use of the frontier axiom.
- No `parameterSet`-only provider.
- No principal-`cpow` Böttcher coordinate.
- No new axiom, `sorry`, `admit`, or opaque restatement of the target.
- No further Böttcher mesh/monodromy scaffolding.
- Do not modify the root theorem or delete the frontier axiom unless the
  provider is fully proved.

## Validation

For source changes, run:

```bash
lake build
lake env lean check_axioms.lean
```

Do not commit.

## Result report

Write:

`plan/GPT54_RESULT_61_FORMALIZE_SOURCED_FINITE_PARAPUZZLE_PROVIDER.md`

The report must distinguish sourced mathematics, proved Lean code, and missing
prerequisites.
