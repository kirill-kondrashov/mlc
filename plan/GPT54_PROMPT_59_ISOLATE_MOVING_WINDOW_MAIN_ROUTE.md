Continue the frontier migration in
`plan/GPT54_TASK_59_ISOLATE_MOVING_WINDOW_MAIN_ROUTE.md`.

Result 58 successfully generalized the finite-side endpoint, but
`Mlc/DirectRoute.lean` and the main theorem-facing payloads still encode the
finite branch as `ParaPuzzlePieceInterMandelbrotConnectedData`. The actual
frontier axiom remains unchanged.

Isolate the remaining source requirement by adding an axiom-free,
theorem-facing moving-window main route.

## Required implementation

1. In `Mlc/MainConjecture.lean` or a small directly related module, add a
   conditional strategy theorem whose finite branch is supplied by a genuine
   moving-window provider, for example:

   ```lean
   ∀ (c : ℂ) (hc : c ∈ MandelbrotSet) (_h : FinitelyRenormalizable c),
     ∃ (W K : ℕ → Set ℂ),
       ConnectednessWindowParameterPieceData c W K
   ```

   The exact provider shape may be improved if needed, but it must include the
   basis/shrinking information required by
   `ConnectednessWindowParameterPieceData`, not merely openness or connectedness.

   Derive finite-side local connectivity via the generic theorem from Result 58,
   then feed it into the existing strategy decomposition. Keep the existing IR
   classification and molecule-bridge hypotheses unchanged.

2. In `Mlc/DirectRoute.lean`, add a parallel payload structure for this generic
   finite branch, such as `DirectMovingWindowMLCData`, and a theorem deriving
   `LocallyConnectedSpace mandelbrotSet` from it. The payload must not mention
   `ParaPuzzlePieceAt`, `ParaPuzzlePieceInterMandelbrotConnectedData`, or the
   frozen Green-translate theorem in its new fields.

3. Preserve all existing direct-route structures and theorem names. Do not
   replace or weaken them. If an old payload can be converted to the new
   conditional route without adding false data, add only the safe adapter.

4. Audit `Mlc/MoleculeConjectureBridge.lean` only for how its satellite local
   connectivity output fits the new route. Do not attempt to replace its
   principal-nest shrinkage theorem yet; record that as a separate provider
   dependency if it remains frozen.

## Mathematical honesty constraints

- This is an interface/isolation task, not a proof of the provider.
- Do not define the provider using `ParaPuzzlePieceAt` merely under a new name.
- Do not use the old frontier axiom to construct the new payload.
- Do not add `sorry`, `admit`, or any project axiom.
- Do not delete the frontier axiom.
- Do not resume Böttcher or parameter-ray construction.
- Preserve the current public APIs and avoid broad refactors.

## Verification

Run:

```bash
lake build
lake env lean check_axioms.lean
```

The axiom frontier must remain unchanged; the new conditional route should add
no project axioms.

## Report

Write:

`plan/GPT54_RESULT_59_ISOLATE_MOVING_WINDOW_MAIN_ROUTE.md`

Include:

- the new structures/theorems;
- the exact provider contract;
- whether an old-route adapter is logically safe;
- a dependency table distinguishing the isolated generic route from the still
  frozen satellite/shrinkage and source-provider layers;
- the smallest concrete theorem package still needed to delete the frontier
  axiom.

Do not commit.
