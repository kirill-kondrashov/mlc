# RESULT 35 — Reduce basin preconnectedness to orbit-norm superlevel connectivity

Task 35 is complete.

## What landed

Created a new leaf file:

- `Mlc/BasinConnected.lean`

and registered it from:

- `Mlc.lean`

The new theorem is:

- `basin_preconnected_of_forall_superlevel_preconnected`

It proves, for arbitrary `c : ℂ`, that

- `(∀ n, IsPreconnected {z : ℂ | R c < ‖orbit c z n‖})`

implies

- `IsPreconnected (basin_of_infinity c)`.

## Proof content

The theorem packages the basin as the increasing union

- `basin_of_infinity c = ⋃ n, {z : ℂ | R c < ‖orbit c z n‖}`

and then applies `isPreconnected_iUnion`.

The proof script establishes exactly the expected ingredients:

- **Monotonicity:** once an orbit iterate has norm `> R c`, the next one also
  has norm `> R c`, via `norm_orbit_ge_of_norm_ge_R`.
- **Union equality:** a point is in the basin iff some orbit iterate crosses the
  escape radius, using the basin `Tendsto` definition and `escape_lemma`.
- **Common core:** all superlevel sets contain the explicit far-exterior point
  `((R c + 1 : ℝ) : ℂ)`.
- **Assembly:** `isPreconnected_iUnion` reduces basin preconnectedness to the
  per-level preconnectedness hypothesis.

## Resulting residual

After this task, the basin-connectivity residual is reduced to the single crux:

- `∀ n, IsPreconnected {z : ℂ | R c < ‖orbit c z n‖}`.

So the remaining content is exactly the per-level statement that each orbit-norm
superlevel set is connected / preconnected.

This is the honest unresolved mathematical step: a maximum-modulus /
no-bounded-complementary-components argument for the polynomial
`z ↦ orbit c z n`. It is **not** discharged in this task.

## Validation

Passed:

- `lake build`
- `lake env lean check_axioms.lean`

## `sorry` / `axiom` status

No new declaration-level `sorry` or `axiom` was introduced.

The axiom check still exits successfully, so the frontier remains unchanged:
exactly the two project axioms (plus the already-allowed standard logical /
classical axioms tracked by `check_axioms.lean`).

## Scope discipline

As requested:

- `ConstructiveBasinCoordinate.lean` was untouched;
- `ConstructiveBasinModulus.lean` was untouched;
- no attempt was made to prove or stub the per-level crux;
- no commit was made.
