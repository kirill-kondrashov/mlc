# GPT-54 Result 58 — Migrate finite side to moving-window interface

## Verdict

A second honest migration seam was implemented.

This task did **not** construct a genuine moving parameter family and did **not**
change the frontier axiom. Instead, it moved the next theorem-facing finite-side
endpoint from para-puzzle-specific provider bundles to the generic moving-window
consumer layer already present in `Mlc/LcAtOfShrink.lean`.

Concretely:

- `Mlc/InfinitelyRenormalizable.lean` now exposes generic finite-side endpoint
  theorems consuming:
  - `ConnectednessWindowParameterPieceData`, and
  - `ParameterPieceLcAtData`.
- The old para-puzzle finite-side entrypoints remain unchanged in name and are now
  proved through the new generic endpoint(s).
- The transport-data compatibility wrapper is now routed through the generic
  moving-window interface rather than through the older para-puzzle-only LC path.

This is a real dependency migration, but it is still downstream-only.

---

## Source changes

### 1. New generic finite-side endpoints in `Mlc/InfinitelyRenormalizable.lean`

Added:

```lean
mlc_finitely_renormalizable_of_connectednessWindowData
mlc_finitely_renormalizable_of_parameterPieceData
```

These theorems package the finite-side local-connectivity endpoint in a source-free
form:

- `mlc_finitely_renormalizable_of_connectednessWindowData` consumes
  `ConnectednessWindowParameterPieceData c W K` directly and concludes local
  connectivity at `c`.
- `mlc_finitely_renormalizable_of_parameterPieceData` consumes the even more basic
  `ParameterPieceLcAtData c P` route.

The finitely-renormalizable hypothesis remains in the signatures only as a
compatibility/theorem-facing parameter; it is not used by the topological LC
consumer itself. That is mathematically honest and mirrors the existing state of
this development: the real work for this endpoint is in the shrinkage/window data,
not in the finiteness marker once that data is already given.

### 2. Existing para-puzzle finite-side endpoints preserved as wrappers

The following old theorems keep their names and APIs:

```lean
mlc_finitely_renormalizable_of_paraPuzzleConnectedData
mlc_finitely_renormalizable_of_paraPuzzleMandelbrotSubsetData
mlc_finitely_renormalizable_of_paraPuzzleTransportData
mlc_finitely_renormalizable_of_paraPuzzleTransportExistsData
mlc_finitely_renormalizable
```

But now the key route is:

- `mlc_finitely_renormalizable_of_paraPuzzleConnectedData`
  → `mlc_finitely_renormalizable_of_parameterPieceData`
- `mlc_finitely_renormalizable_of_paraPuzzleTransportData`
  → `mlc_finitely_renormalizable_of_connectednessWindowData`
  via `connectednessWindowData_of_paraPuzzleTransportData`

So the old para-puzzle API surface now sits on top of the generic window consumer
layer.

---

## Dependency audit table

| Area | Declaration shape | Current status | Notes |
| --- | --- | --- | --- |
| Generic LC consumer | `ParameterPieceLcAtData`, `ConnectednessWindowParameterPieceData`, `lc_at_of_shrink_of_family_data`, `lc_at_of_connectednessWindow_family_data` | **Generic** | No intrinsic dependence on frozen Green-translate source. |
| Local wrapper layer | `connectednessWindowData_of_paraPuzzleTransportData`, `lc_at_of_shrink_of_transport_data` | **Migrated in Result 57** | Repackages para-puzzle transport data into generic moving-window form. |
| Finite-side endpoint | `mlc_finitely_renormalizable_of_connectednessWindowData`, `mlc_finitely_renormalizable_of_parameterPieceData` | **Migrated in this task** | First finite-branch theorem-facing endpoint now generic. |
| Finite-side compatibility wrappers | `mlc_finitely_renormalizable_of_paraPuzzle*`, `mlc_finitely_renormalizable` | **Still old API, now downstream wrappers** | Names preserved; routed through generic consumers. |
| Main route packaging | `MainConjecture.lean`, `DirectRoute.lean` packaged payloads | **Still frozen-facing** | These still quantify over `ParaPuzzlePieceInterMandelbrotConnectedData`. |
| Satellite shrinkage bridge | `MoleculeToParameterShrink.lean`, `MoleculeConjectureBridge.lean` | **Essentially para-puzzle shrinkage based** | Still use `(⋂ n, ParaPuzzlePieceAt c n) = {c}` and `lc_at_of_shrink`. |
| Frontier source/provider | `ParaPuzzleConnectivity.lean` and `PuzzleLemmas2.lean` connectivity data | **Unchanged frontier** | Still ultimately sourced from `green_sublevel_translate_inter_mandelbrot_connected_straddling`. |

---

## Requested file audit

### `Mlc/InfinitelyRenormalizable.lean`

This file was the correct next seam.

Before this task:

- the finite-side endpoint was still phrased through para-puzzle-specific data.

After this task:

- a generic finite-side endpoint exists;
- para-puzzle-specific theorems are wrappers.

### `Mlc/DirectRoute.lean`

Audited only; no source changes made.

This file still packages the finite branch as:

```lean
ParaPuzzlePieceInterMandelbrotConnectedData
```

through `PuzzleBoundaryMotionHyp` equivalences and direct-route payload structures.
That packaging is still theorem-facing and therefore still frozen-facing, but no safe
minimal change was available here without altering the public payload structure of the
existing direct-route API. Since the prompt required preserving old APIs and avoiding
broad refactors, I left it unchanged.

### `Mlc/MainConjecture.lean`

Audited only; no source changes made.

This file still uses packaged finite-branch assumptions in terms of
`Quadratic.ParaPuzzlePieceInterMandelbrotConnectedData` and related transport-data
wrappers. The safe generic seam here would require introducing parallel packaged data
structures for the generic window interface and then adding compatibility conversions.
That is plausible, but it is a larger public-API migration than this prompt required.

### `Mlc/MoleculeConjectureBridge.lean`

Audited only; no source changes made.

This layer still uses parameter shrinkage theorems of the literal form:

```lean
(⋂ n, ParaPuzzlePieceAt c n) = {c}
```

and then applies `lc_at_of_shrink`. This is more than a theorem-facing wrapper: the
current bridge is still genuinely formulated around para-puzzle shrinkage. Without a
new shrinkage theorem for a genuine moving family, no honest generic replacement is
available here.

### `Mlc/MoleculeToParameterShrink.lean`

Audited only; no source changes made.

This file is still essentially para-puzzle based. Its targets are principal-nest /
annulus arguments proving shrinkage specifically for `ParaPuzzlePieceAt`. This is not a
mere wrapper layer, so it should remain frozen until an actual moving-window shrinkage
statement exists.

---

## Exact separation after this task

### A. Generic consumer theorems no longer needing the frozen source

These are now fully generic consumer-side declarations:

- `ParameterPieceLcAtData`
- `ConnectednessWindowParameterPieceData`
- `ConnectednessLocusWindowFamilyData`
- `lc_at_of_shrink_of_family_data`
- `lc_at_of_connectednessWindow_family_data`
- `lc_at_of_connectednessLocus_family_data`
- `connectednessWindowData_of_paraPuzzleTransportData`
- `mlc_finitely_renormalizable_of_connectednessWindowData`
- `mlc_finitely_renormalizable_of_parameterPieceData`

### B. Source/provider declarations still tied to the frozen frontier

These remain sourced from the old route and therefore from the surviving frontier axiom:

- `green_sublevel_translate_inter_mandelbrot_connected_straddling`
- `green_sublevel_translate_inter_mandelbrot_connected`
- `para_puzzle_piece_inter_mandelbrot_connected_proved`
- `para_puzzle_connectivity_data_proved`
- the provider bundles in `PuzzleLemmas2.lean`
- the default boundary-motion/transport witness wrappers built from them

### C. Declarations still essentially mentioning `ParaPuzzlePieceAt`

These are not merely wrappers; they still encode the current shrinkage model:

- `ParaPuzzlePieceAt`
- `para_puzzle_piece_basis`
- `(⋂ n, ParaPuzzlePieceAt c n) = {c}` shrinkage lemmas
- `MoleculeToParameterShrink.lean` shrinkage targets
- satellite bridge theorems in `MoleculeConjectureBridge.lean`
- primitive and satellite principal-nest shrinkage routes

---

## Remaining provider package

The exact remaining package is unchanged from Result 57, but now the next migration
boundary is sharper:

> We still need a **concrete theorem producing generic connected shrinking windows**
> near a Mandelbrot parameter — i.e. a source-side provider of
> `ConnectednessWindowParameterPieceData` or `ConnectednessLocusWindowFamilyData`
> for a genuine moving family, together with the replacement shrinkage/basis data
> currently encoded using `ParaPuzzlePieceAt`.

In other words, what is still missing is **not another generic LC consumer**.
Those now exist and are threaded through the finite-side endpoint. What is missing is:

1. a real moving-window provider theorem with connected relative Mandelbrot slices;
2. if the satellite/primitive bridge is to migrate fully, a corresponding moving-family
   shrinkage statement replacing the current literal `ParaPuzzlePieceAt` intersection
   theorems.

Until that provider exists, the frontier axiom cannot be deleted honestly.

---

## Validation

Ran successfully:

```bash
lake build Mlc.InfinitelyRenormalizable
lake build
lake env lean check_axioms.lean
```

The axiom frontier remains unchanged.
