Work on the recommended next route in
`plan/GPT54_TASK_61_FORMALIZE_SOURCED_FINITE_PARAPUZZLE_PROVIDER.md`.

The repository has completed the generic consumer migration, but no genuine
moving-window provider exists. Do not add more interface-only plumbing.

The target is the first real source-side theorem needed to instantiate:

```lean
FiniteMovingWindowProviderData :=
  ∀ (c : ℂ) (hc : c ∈ MandelbrotSet) (_h : FinitelyRenormalizable c),
    ∃ (W K : ℕ → Set ℂ),
      ConnectednessWindowParameterPieceData c W K
```

## Source-driven task

1. Select one precise classical finite-level parapuzzle theorem for quadratic
   polynomials, preferably a Yoccoz/parapuzzle statement for finitely
   renormalizable parameters. Record the exact public source, theorem
   formulation, and hypotheses in the result report.

2. Map that theorem to the repository’s required data:

   - a genuine moving parameter window `W n`, not
     `ParaPuzzlePieceAt c n` under another name;
   - ambient openness;
   - basepoint membership;
   - nested/basis or equivalent shrinkage at `c`;
   - connectedness of `W n ∩ MandelbrotSet`;
   - an honest phase–parameter/combinatorial correspondence explaining why
     `W n` is the relevant parameter object.

3. Audit the existing code for usable prerequisites:

   - `DynamicalPuzzlePiece`;
   - `PuzzleBoundaryMotion`;
   - external-ray/equipotential/landing declarations;
   - `BMolParameterFamily`;
   - `AnalyticQuadraticLikeFamilyCore`;
   - any parameter graph/component structures.

4. Implement only genuinely justified pieces:

   - definitions of the new finite parapuzzle object;
   - elementary topology/set lemmas;
   - adapters into `ConnectednessWindowParameterPieceData`;
   - a provider theorem only if every field is proved from existing checked
     mathematics or the explicitly formalized sourced theorem.

## Hard honesty gate

Do not:

- identify `ParaPuzzlePieceAt` with the new moving window;
- use `green_sublevel_translate_inter_mandelbrot_connected_straddling`;
- use `parameterSet` alone as a parapuzzle window;
- add an axiom, `sorry`, `admit`, or an opaque hypothesis that merely restates
  `FiniteMovingWindowProviderData`;
- claim a phase–parameter theorem from definitions or comments;
- continue Böttcher monodromy work.

If the repository lacks the prerequisites for the selected classical theorem,
make no speculative source edits. Instead, report the first missing formal
theorem and the smallest prerequisite module that must be built before the
provider can be instantiated.

If a real provider is constructed, route a test theorem through
`mlc_strategy_of_movingWindowData`, but do not change the root theorem or delete
the frontier axiom unless the provider is fully proved.

Run targeted Lean checks for any edits. If source changes are made, also run:

```bash
lake build
lake env lean check_axioms.lean
```

Do not commit.

Write the result to:

`plan/GPT54_RESULT_61_FORMALIZE_SOURCED_FINITE_PARAPUZZLE_PROVIDER.md`
