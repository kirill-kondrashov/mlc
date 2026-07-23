# GPT-54 Result 59 — Isolate Moving-Window Main Route

## Summary

Implemented the theorem-facing moving-window main route requested by Prompt 59 without changing the live frontier axiom and without smuggling frozen para-puzzle data into the new interface.

## Code changes

### `Mlc/MainConjecture.lean`

Added an honest finite-side provider contract:

- `FiniteMovingWindowProviderData : Prop`
  - contract: for each finitely renormalizable `c ∈ MandelbrotSet`, provide
    `∃ W K, ConnectednessWindowParameterPieceData c W K`

Added the generic finite-branch consumer:

- `finite_lc_provider_of_movingWindowData`
  - converts the provider contract into finite-side local connectivity via
    `mlc_finitely_renormalizable_of_connectednessWindowData`

Added the theorem-facing main route:

- `mlc_strategy_of_movingWindowData`
  - reuses the existing strategy decomposition with the finite branch supplied by
    the new moving-window provider contract

Added packaged seam payloads parallel to the old para-puzzle packaging:

- `MLCMovingWindowClassifyBridgeSeamData`
- `mlcMovingWindowClassifyBridgeSeamData_iff`
- `mlcMovingWindowClassifyBridgeSeamData_of_finiteMovingWindowProviderData_irClassifyBridgeData`
- `mlc_conjecture_of_MLCMovingWindowClassifyBridgeSeamData`
- `mlc_conjecture_of_finiteMovingWindowProviderData_irClassifyBridgeData`

### `Mlc/DirectRoute.lean`

Added direct-route packaging for the new moving-window theorem surface:

- `DirectMovingWindowMLCPackagedData : Prop := MLCMovingWindowClassifyBridgeSeamData`
- `DirectMovingWindowMLCData`
- `directMovingWindowMLCData_iff`
- `irClassifyBridgeData_of_directMovingWindowMLCData`
- `directMovingWindowMLCPackagedData_of_directMovingWindowMLCData`
- `directMovingWindowMLCPackagedData_iff_directMovingWindowMLCData`
- `mlc_conjecture_of_directMovingWindowMLCPackagedData`
- `mlc_conjecture_of_directMovingWindowMLCData`

## What this accomplishes

The finite branch of the main MLC route is now isolated behind an honest theorem-facing contract that no longer mentions:

- `ParaPuzzlePieceAt`
- `ParaPuzzlePieceInterMandelbrotConnectedData`
- `ParaPuzzleInterMandelbrotTransportData`
- `ParaPuzzleInterMandelbrotTransportExistsData`

This means the remaining finite-side dependency is now exactly the existence of a genuine moving-window provider theorem producing `ConnectednessWindowParameterPieceData` for finitely renormalizable parameters.

## What was intentionally not changed

I did **not** add any adapter that manufactures the new provider from the old para-puzzle interface. That would defeat the purpose of Prompt 59 by hiding the frozen source contract behind a renamed wrapper.

I also did **not** modify the satellite bridge layer:

- `MoleculeConjectureBridge.lean`
- `MoleculeToParameterShrink.lean`

Those files still package literal para-puzzle/principal-nest shrinkage on the satellite side, and Prompt 59 only asked to isolate the moving-window main route, not to replace the satellite source package.

## Safety / honesty assessment

### Safe adapters

Safe:
- wrapping the new provider contract into theorem-facing MLC assembly structures
- using `mlc_finitely_renormalizable_of_connectednessWindowData` as the sole finite-side consumer
- reusing existing `IRClassifyBridgeData`

Unsafe / intentionally avoided:
- defining `FiniteMovingWindowProviderData` from para-puzzle connectedness by relabelling old frozen objects
- claiming the direct moving-window payload is equivalent to the old para-puzzle payload

## Remaining minimal concrete theorem package

After this refactor, deleting the finite-side frozen frontier from the **main route** would require a theorem of the form:

- for every finitely renormalizable `c ∈ MandelbrotSet`, there exist `W K` with
  `ConnectednessWindowParameterPieceData c W K`

The satellite side still separately depends on frozen shrinkage packaging, so the full frontier is not yet eliminated.

## Dependency split after this change

### Generic theorem-facing route now available

- `FiniteMovingWindowProviderData`
- `finite_lc_provider_of_movingWindowData`
- `mlc_strategy_of_movingWindowData`
- `MLCMovingWindowClassifyBridgeSeamData`
- `DirectMovingWindowMLCData`

### Remaining frozen/provider-dependent layers

Finite-source provider still missing:
- concrete theorem building `ConnectednessWindowParameterPieceData` for finitely renormalizable parameters

Satellite/provider-frozen:
- `MoleculeConjectureBridge.lean`
- `MoleculeToParameterShrink.lean`
- principal-nest / literal `ParaPuzzlePieceAt` shrinkage targets

## Validation

Passed:
- `lake build Mlc.MainConjecture Mlc.DirectRoute`
- `lake build`
- `lake env lean check_axioms.lean`
