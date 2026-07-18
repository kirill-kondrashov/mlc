Continue the frontier-dependency migration in
`plan/GPT54_TASK_58_MIGRATE_FINITE_SIDE_TO_MOVING_WINDOW_INTERFACE.md`.

Result 57 added and compiled the first honest seam:

```lean
connectednessWindowData_of_paraPuzzleTransportData
lc_at_of_shrink_of_transport_data
```

This only repackages frozen para-puzzle transport data. The live frontier axiom
is still unchanged and no genuine moving-window source exists yet.

Now migrate the next theorem-facing layer without inventing geometry:

1. In `Mlc/InfinitelyRenormalizable.lean`, add a generic finite-side endpoint
   theorem accepting `ParameterPieceLcAtData` or, preferably,
   `ConnectednessWindowParameterPieceData` directly. It should use the existing
   `lc_at_of_shrink_of_family_data` /
   `lc_at_of_connectednessWindow_family_data` consumer and retain the existing
   finitely-renormalizable hypotheses only where they are mathematically
   required.

2. Preserve all existing para-puzzle theorem names as compatibility wrappers,
   proving them through the new generic theorem rather than duplicating the
   old specialized path.

3. Audit `Mlc/DirectRoute.lean`, `Mlc/MainConjecture.lean`,
   `Mlc/MoleculeConjectureBridge.lean`, and
   `Mlc/MoleculeToParameterShrink.lean` for theorem-facing uses that only need
   “each parameter window intersects MandelbrotSet in a connected set”.
   Where a safe generic wrapper is possible, add it and route the old wrapper
   through it. Do not change the mathematical hypotheses or introduce a fake
   moving family.

4. Clearly separate:
   - generic consumer theorems that no longer need the frozen source;
   - source/provider declarations that still depend on
     `green_sublevel_translate_inter_mandelbrot_connected`;
   - shrinkage or phase–parameter declarations that still mention
     `ParaPuzzlePieceAt` essentially.

Do not attempt another Böttcher construction, parameter-ray construction, or
proof of the frozen straddling theorem. Do not delete the frontier axiom. Do
not add `sorry`, `admit`, or any new axiom. Avoid broad refactors and preserve
all old APIs.

Run:

```bash
lake build
lake env lean check_axioms.lean
```

Write the complete report, including a dependency table and the exact remaining
provider package, to:

`plan/GPT54_RESULT_58_MIGRATE_FINITE_SIDE_TO_MOVING_WINDOW_INTERFACE.md`

Do not commit.
