# RESULT 34 — Reduce conjugacy to holomorphicity plus basin preconnectedness

Task 34 is complete.

## What landed

Added, in `Mlc/Quadratic/Complex/Bottcher/ConstructiveBasinModulus.lean`:

- `coherentBasinCoordinate_conj_of_holo_of_preconnected`

This is the planner-specified identity-theorem reduction showing that for the
coherent basin coordinate coming from `EscapeTimeIndependentPullbackDataFor c`,
conjugacy is no longer an independent hypothesis: if

- `DifferentiableOn ℂ (coherentBasinCoordinate d) (basin_of_infinity c)`, and
- `IsPreconnected (basin_of_infinity c)`,

then on the whole basin one has

- `coherentBasinCoordinate d (quadratic_map c z) = (coherentBasinCoordinate d z)^2`.

## Proof mechanism

The proof follows exactly the intended route.

Let `s := basin_of_infinity c`.

- `coherentBasinCoordinate d` is analytic on neighborhoods of `s`, coming from
  `DifferentiableOn` on the open basin.
- `quadratic_map c` is analytic on `s` and maps `s` to itself by forward
  invariance of the basin.
- Therefore both analytic sides
  - `z ↦ coherentBasinCoordinate d (quadratic_map c z)` and
  - `z ↦ (coherentBasinCoordinate d z)^2`
  are `AnalyticOnNhd` on `s`.
- At the exterior base point `w₀ = (‖c‖ + 3 : ℝ)`, a neighborhood lies inside
  the region where both `z` and `quadratic_map c z` are outside the escape disk.
- On that collar, `coherentBasinCoordinate_extends_near` identifies the coherent
  coordinate with `logSeriesBottcherApprox`, and the outside-open local Böttcher
  conjugacy gives equality there.
- `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq` then propagates the
  equality to all of the preconnected basin.

## Resulting seam

After this task, the genuine-coordinate seam is now exactly:

- `holo_on_basin`
- `IsPreconnected (basin_of_infinity c)`

So `conj_on_basin` is no longer an independent residual.

These two remaining inputs are both classical Douady–Hubbard-depth facts:
- the basin is preconnected / connected, and
- the coherent branch is holomorphic.

## Validation

Passed:

- `lake build Mlc.Quadratic.Complex.Bottcher.ConstructiveBasinModulus`
- `lake build`
- `lake env lean check_axioms.lean`

## `sorry` / `axiom` status

No new declaration-level `sorry` or `axiom` was introduced.

The axiom check still exits successfully, so the frontier remains unchanged:
exactly the two project axioms (plus the already-allowed standard logical /
classical axioms used by `check_axioms.lean`).

## Scope discipline

As requested:
- no new file was created in `Mlc/...`;
- `ConstructiveBasinCoordinate.lean` was not edited;
- `basinLogSeriesExtensionCandidate` was untouched;
- `holo` and `IsPreconnected` were not bundled away or stubbed.
