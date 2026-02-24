# MLC Formalization Status (CP5 focus)

[![build](https://github.com/kirill-kondrashov/mlc/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/kirill-kondrashov/mlc/actions/workflows/lean_action_ci.yml)

[Live dependency graph (rooted at `MLC.mlc_conjecture`)](https://kirill-kondrashov.github.io/mlc/mlc_conjecture/)

This repository is a Lean formalization scaffold centered on `MLC.mlc_conjecture`.
The code compiles and the remaining work is now concentrated in one final
constructive gap.

## The missing piece (what still blocks closure)

For the current CP5 track, only the `c = 2` case is needed:

- target endpoint: `Quadratic.ExternalRayMapData (2 : ℂ)`
- current placeholder:
  `external_ray_map_exists_two_constructive := Quadratic.external_ray_map_exists (2 : ℂ)`
- blocker: constructively prove a direct witness of
  `IsProperMap (bottcher_map_outside_open_to_exterior (2 : ℂ)) ∧ IsLocalHomeomorph (...)`
  (packaged as `DirectProperLocalWitnessTwo`)

Once that witness is proved, the final placeholder can be rewired through the
already-built constructive bridge stack in `Mlc/MainConjecture.lean`.

## Alternative route (if the `c = 2` witness lane stalls)

There is a second path, but it is broader and more expensive:
re-root `MLC.mlc_conjecture` so it does not pass through
`ExternalRayMapData (2 : ℂ)`.

That requires constructive reformalization of the current seam inputs and
removal of contradiction-seeded routing:

- `PuzzleBoundaryMotionHyp`
- `IRClassificationData`
- `MoleculeConformalModulusLowerBoundData`
- replacement of `False.elim` seam instantiations with direct constructive
  bridges

So the current route is a single hard local theorem; the alternative is an
architecture rewrite across multiple branches.

## What `Quadratic.external_ray_map_exists` means

`Quadratic.external_ray_map_exists c` postulates existence of a map
`f : ℂ → ℂ` that is inverse to the Böttcher map on exterior domains:

- for `‖w‖ > 1`: `bottcher_map c (f w) = w`
- for `‖z‖ > ‖c‖ + 2`: `f (bottcher_map c z) = z`

In this repo it is currently an `axiom` (see
`Mlc/Quadratic/Complex/Bottcher/BottcherAxioms.lean`).

## Where to work

- Main CP5 constructive route:
  `Mlc/MainConjecture.lean`
  - `DirectProperLocalWitnessTwo`
  - `DynamicalBottcherConformalIdentificationTwo`
  - `RemainingConstructiveIngressTwo`
  - `external_ray_map_exists_two_constructive` (final replacement point)
- Axiom declaration/data package:
  `Mlc/Quadratic/Complex/Bottcher/BottcherAxioms.lean`
- Active plan:
  `plan/PLAN_dudko_2512_conformal_identification_formalization.md`

## Verification

```bash
make build
make check
```

`make check` should continue to report only:

- `Quot.sound`
- `propext`
- `Classical.choice`
- `MLC.Quadratic.external_ray_map_exists`

Success criterion for this track: remove
`MLC.Quadratic.external_ray_map_exists` from that output by replacing the
`c = 2` endpoint with a constructive proof.
