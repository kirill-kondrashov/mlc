# GPT-54 Result 57 — Audit and Begin Frontier Dependency Migration

## Verdict

A **small, safe migration seam was implemented**.

I did **not** remove the frontier axiom or claim it is now removable. Instead, I:

- audited the dependency chain from the frozen straddling axiom to the MLC route;
- identified which consumers are genuinely frozen and which are already generic;
- added a theorem-facing adapter from existing para-puzzle transport data into the
  newer generic moving-window interface in `LcAtOfShrink.lean`.

This migration is real but limited: it reduces coupling of local-connectivity
consumers to the old `ParaPuzzlePieceInterMandelbrotConnectedData` packaging,
while leaving the upstream source of connectivity data unchanged.

---

## What was audited

The requested declarations were traced:

- `green_sublevel_translate_inter_mandelbrot_connected_straddling`
- `green_sublevel_translate_inter_mandelbrot_connected`
- `ParaPuzzlePieceAt`
- `para_puzzle_piece_inter_mandelbrot_connected`

### 1. Direct straddling/frontier uses

The live frontier axiom appears in:

- `Mlc/ParaPuzzleConnectivity.lean`
  - as the residual axiom itself;
  - used only to derive
    `green_sublevel_translate_inter_mandelbrot_connected`, then
    `para_puzzle_piece_inter_mandelbrot_connected_proved`, then
    `para_puzzle_connectivity_data_proved`.
- commentary/audit files such as `ParaPuzzleCarvingReduction.lean`,
  `Bottcher/LambdaLemma.lean`, `Bottcher/AhlforsSchwarz.lean` reference it as the
  current frontier, but do not widen the proof dependency materially.
- `check_axioms.lean` records the axiom in the frontier list.

### 2. Frozen para-puzzle connectivity consumers

The old frozen route is still centered on:

- `Mlc/Quadratic/Complex/PuzzleLemmas2.lean`
  - axiom `para_puzzle_piece_inter_mandelbrot_connected`
  - provider bundles:
    - `ParaPuzzlePieceInterMandelbrotConnectedData`
    - `ParaPuzzleInterMandelbrotTransportData`
    - `ParaPuzzleInterMandelbrotTransportExistsData`
- `Mlc/Quadratic/Complex/PuzzleBoundaryMotion.lean`
  - default witness package `para_puzzle_transport_exists_data_of_motion_default`
  - still sourced from the axiom-backed para-puzzle witness route.
- `Mlc/LcAtOfShrink.lean`
  - old route `lc_at_of_shrink_of_data`
  - wrappers specialized to `ParaPuzzlePieceAt c n`
- `Mlc/InfinitelyRenormalizable.lean`
  - finite-side endpoint theorem still accepts the old para-puzzle packages.

### 3. Generic topology already available

`Mlc/LcAtOfShrink.lean` already contained the corrected generic consumer layer:

- `ParameterPieceLcAtData`
- `ConnectednessWindowParameterPieceData`
- `ConnectednessLocusWindowFamilyData`
- `lc_at_of_shrink_of_family_data`
- `lc_at_of_connectednessWindow_family_data`
- `lc_at_of_connectednessLocus_family_data`

These are **not intrinsically tied** to:

- frozen Green-translate equalities,
- `ParaPuzzlePieceAt` specifically,
- or the straddling axiom.

They only require:

- open windows,
- basepoint membership,
- a neighborhood basis,
- connectedness of `window ∩ MandelbrotSet`.

So this is the correct migration target.

### 4. Definitions still encoding the frozen surrogate

The actual frozen surrogate remains:

- `Mlc/Quadratic/Complex/ParaPuzzle.lean`
  - `ParaPuzzlePieceAt (c : ℂ) (n : ℕ) := {c' | c' - c ∈ DynamicalPuzzlePiece c n 0}`

and many shrinkage/principal-nest theorems still use this family literally. That is
fine for now; the current task was to begin dependency migration, not replace the
entire parameter-piece notion.

---

## Exact consumer classification

### Class 1 — genuinely tied to the frozen Green-translate equality

These still depend on the current para-puzzle identification with translated
Green sublevels:

- `ParaPuzzleConnectivity.lean`
  - `paraPuzzlePieceAt_eq_green_translate`
  - `para_puzzle_piece_inter_mandelbrot_connected_proved`
  - `para_puzzle_connectivity_data_proved`
- anything trying to source connectedness from
  `green_sublevel_translate_inter_mandelbrot_connected`

This is the true frontier area.

### Class 2 — generic topology that can consume moving windows

These are already generic and no longer mathematically depend on the frozen route:

- `parameter_piece_induced_connected`
- `parameter_piece_basis_induced`
- `lc_at_of_shrink_of_family_data`
- `lc_at_of_connectednessWindow_family_data`
- `lc_at_of_connectednessLocus_family_data`
- the structures `ParameterPieceLcAtData`,
  `ConnectednessWindowParameterPieceData`,
  `ConnectednessLocusWindowFamilyData`

### Class 3 — theorem-facing wrappers generalizable without changing content

These packages are representational wrappers rather than mathematical commitments:

- `ParaPuzzlePieceInterMandelbrotConnectedData`
- `ParaPuzzleInterMandelbrotTransportData`
- `ParaPuzzleInterMandelbrotTransportExistsData`
- local wrappers in `LcAtOfShrink.lean`
- finite-side wrappers in `InfinitelyRenormalizable.lean`

This class is where safe migration can start.

---

## Implemented migration seam

I added:

- `connectednessWindowData_of_paraPuzzleTransportData`
  in `Mlc/LcAtOfShrink.lean`

This theorem repackages existing para-puzzle transport data as:

```lean
ConnectednessWindowParameterPieceData c
  (fun n => ParaPuzzlePieceAt c n)
  (fun n => htr.transportSet c n)
```

using:

- window openness from `para_puzzle_piece_open`;
- base membership and basis from para-puzzle shrinkage;
- window/locus inclusion from `htr.eq_inter`;
- relative Mandelbrot connectedness from the existing transport-data provider.

Then I rewired:

- `lc_at_of_shrink_of_transport_data`

so it now goes through the **generic moving-window route**
`lc_at_of_connectednessWindow_family_data` instead of directly through the older
specialized para-puzzle connectedness package.

This is exactly the kind of theorem-facing migration Prompt 57 requested:

- old frozen APIs remain intact;
- no fake moving family was introduced;
- no new axiom was added;
- an existing downstream LC consumer is now fed through the new generic window interface.

---

## What this does and does not accomplish

### Accomplished

- It proves that the generic moving-window layer is not dead code.
- It gives a concrete adapter from existing transport data into the corrected LC
  consumer interface.
- It begins unplugging downstream local-connectivity consumers from the old
  `ParaPuzzlePieceInterMandelbrotConnectedData` shape.

### Not accomplished

- It does **not** remove the straddling axiom.
- It does **not** replace `ParaPuzzlePieceAt` by a genuine moving-window family.
- It does **not** supply a new concrete source of connected windows.
- It does **not** alter the current proof path of `mlc_conjecture` at the frontier source.

So the frontier remains unchanged, as required.

---

## Minimal future package still required

The next honest deletion target is **not** another local-topology wrapper. The
minimal remaining package is:

> a concrete theorem producing `ConnectednessWindowParameterPieceData` (or the
> BMol-family specialization `ConnectednessLocusWindowFamilyData`) from an actual
> moving-window family near a Mandelbrot parameter, with connected relative
> Mandelbrot slices and a basis property.

Concretely, once a genuine moving family exists, the following declarations are the
right migration targets:

1. finite-side local connectivity endpoint(s) in `InfinitelyRenormalizable.lean`
   should accept `ConnectednessWindowParameterPieceData` directly;
2. bridge layers presently phrased in terms of para-puzzle transport data should be
   duplicated or generalized to the moving-window interface;
3. only after all such consumers are migrated can the old para-puzzle connectedness
   witness packages stop mattering to the derivation;
4. only then can the frontier axiom be meaningfully deleted.

At present, that concrete moving-window theorem is still missing.

---

## Files changed

- `Mlc/LcAtOfShrink.lean`
  - added `connectednessWindowData_of_paraPuzzleTransportData`
  - rerouted `lc_at_of_shrink_of_transport_data` through the generic moving-window API

No other source files were changed.
