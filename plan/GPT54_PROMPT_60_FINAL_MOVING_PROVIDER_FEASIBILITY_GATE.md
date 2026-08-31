Perform the final feasibility gate in
`plan/GPT54_TASK_60_FINAL_MOVING_PROVIDER_FEASIBILITY_GATE.md`.

Results 57–59 have completed the downstream migration:

- generic connected-window LC consumers exist;
- finite-side endpoints consume them;
- an axiom-free moving-window main/direct route exists;
- the actual root `MLC.mlc_conjecture` still uses
  `para_puzzle_connectivity_data_proved`;
- no concrete theorem currently instantiates `FiniteMovingWindowProviderData`.

Do not add another generic wrapper. Determine whether the current repository
contains any honest, already-proved ingredients from which the following
provider can be constructed for every finitely renormalizable
`c ∈ MandelbrotSet`:

```lean
FiniteMovingWindowProviderData :=
  ∀ c hc hfin, ∃ W K,
    ConnectednessWindowParameterPieceData c W K
```

## Audit

Search all imported project modules for a theorem or structure supplying, without
the frozen Green-translate axiom:

1. an ambient open parameter window family;
2. basepoint membership and a neighborhood-basis/shrinkage theorem;
3. connectedness of each `W n ∩ MandelbrotSet`;
4. a genuine moving/parapuzzle interpretation rather than an alias or
   repackaging of `ParaPuzzlePieceAt`.

Check especially:

- Yoccoz finite-renormalization/shrinkage declarations;
- `PuzzleBoundaryMotion` and `PuzzleLemmas2`;
- `BMolParameterFamily` and `AnalyticQuadraticLikeFamilyCore`;
- all parameter-graph, ray, equipotential, and component declarations.

For each candidate, classify it as:

- a valid provider ingredient;
- only a frozen para-puzzle wrapper;
- only dynamical/fiber data;
- missing a decisive topology or phase–parameter theorem.

## Action

- If a complete honest provider is already derivable, implement the smallest
  proof of `FiniteMovingWindowProviderData`, route `MLC.mlc_conjecture` through
  `mlc_conjecture_of_finiteMovingWindowProviderData_irClassifyBridgeData` (or
  an equivalent existing route), and remove only the now-unused
  `green_sublevel_translate_inter_mandelbrot_connected_straddling` dependency.
  Do not remove the residual molecule axiom.
- If any decisive ingredient is missing, make **no speculative source edits**.
  Do not add an axiom, `sorry`, `admit`, fake provider, or renamed frozen
  wrapper. Report the exact missing theorem and stop.

The expected outcome is likely a hard-stop report, not code. Do not continue
Böttcher monodromy or parameter-ray construction unless an existing checked
ingredient makes it immediately justified.

Run any necessary targeted checks; if source changes are made, run:

```bash
lake build
lake env lean check_axioms.lean
```

Write:

`plan/GPT54_RESULT_60_FINAL_MOVING_PROVIDER_FEASIBILITY_GATE.md`

Include a complete candidate table, the exact dependency status of
`MLC.mlc_conjecture`, and a quantitative statement of whether the frontier can
be deleted now. Do not commit.
