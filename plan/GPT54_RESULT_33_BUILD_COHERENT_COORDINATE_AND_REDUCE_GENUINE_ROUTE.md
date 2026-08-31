# RESULT 33 — Build the coherent basin coordinate and reduce the genuine route

Implemented all requested Task 33 declarations in
`Mlc/Quadratic/Complex/Bottcher/ConstructiveBasinModulus.lean` without touching
`ConstructiveBasinCoordinate.lean`.

## What landed

### 1. Keystone modulus theorem
Added:

- `escapeTimeIndependent_value_modulus`

This proves that for any `EscapeTimeIndependentPullbackDataFor c`, its coherent
value satisfies the genuine Böttcher modulus identity on the basin:

- `‖d.value z hz‖ = exp (green_function c z)`.

The proof uses:
- the root equation from
  `compatible_with_every_escape_time`,
- norming both sides,
- the outside-open log-series modulus formula,
- Green orbit scaling, and
- `Real.pow_rpow_inv_natCast` to extract the `2^N`-th root.

### 2. Total coherent coordinate
Added:

- `coherentBasinCoordinate`
- `coherentBasinCoordinate_on_basin`
- `coherentBasinCoordinate_extends_near`
- `coherentBasinCoordinate_modulus`

Definition:
- on the basin: `coherentBasinCoordinate d z = d.value z hz`
- off the basin: `0`

So this is the total-function wrapper for the branch-coherent escape-time-
independent value, analogous in shape to the earlier principal-pullback wrapper
but now built from the correct coherent datum.

### 3. Genuine route reduced to exactly `conj` + `holo`
Added:

- `genuineBottcherCoordinateData_of_escapeTimeIndependent_of_conj_of_holo`

This theorem constructs:

- `GenuineBottcherCoordinateDataFor c (coherentBasinCoordinate d)`

from exactly two explicit hypotheses:

- `hconj` on the basin,
- `hholo` on the basin.

The other fields are now automatic and proven in-repo:
- norm `> 1` on the basin,
- reverse basin characterization from norm `> 1`,
- Green modulus identity,
- continuity on the basin away from `0`,
- normalization `φ(z)/z → 1` at infinity.

## Honest residual seam

After this task, the genuine coherent-coordinate target is reduced to exactly:

- `conj_on_basin`
- `holo_on_basin`

for the coherent value coming from `EscapeTimeIndependentPullbackDataFor c`.

These are the honest remaining analytic obligations.

In particular, this task does **not** revisit the principal-branch candidate
`basinLogSeriesExtensionCandidate`; that candidate remains intentionally
non-holomorphic on the full basin, so it is not the genuine route.

## Natural future reductions

Not attempted here, but the next believable reductions are:

1. `conj_on_basin` should follow from `holo_on_basin` plus agreement near
   infinity by an identity-theorem argument on the connected/preconnected basin.
2. `holo_on_basin` is the real content of the monodromy-coherent route and
   should come from the existing monodromy framework:
   - `MonodromyTrivialPullbackDataFor`
   - concrete basin-loop monodromy data
   - local branch gluing / single-valued continuation
   - ultimately a simple-connectivity input for the basin in the connected-
     Julia/Mandelbrot regime.

I searched for an existing in-repo lemma asserting preconnectedness or
connectedness of `basin_of_infinity c` in the exact needed form and found no
matching declaration by grep.

## Validation

Passed:

- `lake build Mlc.Quadratic.Complex.Bottcher.ConstructiveBasinModulus`
- `lake build`
- `lake env lean check_axioms.lean`

The repository remains green after the Task 33 changes.

## `sorry` / `axiom` status

No new declaration-level `sorry` or `axiom` was introduced.

`check_axioms.lean` still returned success, so the frontier remains the same as
before: exactly the two project axioms together with the standard logical /
classical axioms already allowed there.

## Net state after Task 33

The proof route no longer depends on the impossible hypothesis that the
principal-branch pullback is holomorphic. Instead, the downstream theorem-facing
genuine route is now focused on the correct coherent object and reduced to the
true remaining seam: holomorphicity and conjugacy of the branch-coherent basin
coordinate.
