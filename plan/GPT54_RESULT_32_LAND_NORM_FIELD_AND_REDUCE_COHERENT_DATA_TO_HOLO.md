# Result 32 — Land norm field and reduce coherent data to `holo_on_basin`

## Outcome

This task succeeded.

I:
- revised the off-basin totality branch of `basinLogSeriesExtensionCandidate` from `MLC.logSeriesBottcherApprox c z` to `0`,
- added the reverse norm-field theorem
  `basinLogSeriesExtensionCandidate_basin_of_norm_gt_one`,
- added the constructor
  `principalPullbackCoherentData_of_holo`, reducing the full target
  `PrincipalPullbackCoherentDataFor c` to the single explicit hypothesis
  `holo_on_basin`,
- verified targeted and full builds, and
- checked that the axiom frontier did not expand.

## Source changes

### 1. Revised the off-basin branch of the candidate

Edited:
- `Mlc/Quadratic/Complex/Bottcher/ConstructiveBasinCoordinate.lean`

Changed:

```lean
noncomputable def basinLogSeriesExtensionCandidate (c z : ℂ) : ℂ :=
  by
    classical
    exact
      if hz : z ∈ basin_of_infinity c then
        principalPullbackLogSeriesBottcher c z hz
      else
        0
```

instead of the previous off-basin branch `MLC.logSeriesBottcherApprox c z`.

Rationale: the coherent-data field

```lean
∀ z : ℂ, 1 < ‖basinLogSeriesExtensionCandidate c z‖ → z ∈ basin_of_infinity c
```

is not credible with the old totality convention, but becomes immediate with the
new off-basin value `0`.

This did not disturb the already-landed on-basin theorems or
`basinLogSeriesExtensionCandidate_extends_near`, since those use the `dif_pos`
branch and the outside-open region lies in the basin.

### 2. Added the sixth field theorem

Edited:
- `Mlc/Quadratic/Complex/Bottcher/ConstructiveBasinModulus.lean`

Added:

```lean
theorem basinLogSeriesExtensionCandidate_basin_of_norm_gt_one (c : ℂ) :
    ∀ z : ℂ, 1 < ‖basinLogSeriesExtensionCandidate c z‖ →
      z ∈ basin_of_infinity c := by
  intro z hz
  by_contra hnb
  rw [basinLogSeriesExtensionCandidate, dif_neg hnb, norm_zero] at hz
  linarith
```

This honestly lands the sixth coherent-data field.

### 3. Reduced the whole target to `holo_on_basin`

In the same file I added:

```lean
theorem principalPullbackCoherentData_of_holo (c : ℂ)
    (holo : DifferentiableOn ℂ (basinLogSeriesExtensionCandidate c)
      (basin_of_infinity c)) :
    PrincipalPullbackCoherentDataFor c where
  extends_near := fun z hz => basinLogSeriesExtensionCandidate_extends_near c z hz
  norm_on_basin := fun z hz => basinLogSeriesExtensionCandidate_norm_gt_one_on_basin c z hz
  basin_of_norm_gt_one := basinLogSeriesExtensionCandidate_basin_of_norm_gt_one c
  conj_on_basin := fun z hz => basinLogSeriesExtensionCandidate_conj_on_basin c z hz
  holo_on_basin := holo
  modulus_on_basin := fun z hz => basinLogSeriesExtensionCandidate_modulus_on_basin c z hz
  tendsto_div_atInfinity := basinLogSeriesExtensionCandidate_tendsto_div_atInfinity c
```

So the entire `PrincipalPullbackCoherentDataFor c` target is now reduced to one
explicit analytic hypothesis, exactly as requested.

## Build / validation

### Targeted module build

Succeeded:

```text
✔ [7890/7890] Built Mlc.Quadratic.Complex.Bottcher.ConstructiveBasinModulus (4.6s)
Build completed successfully (7890 jobs).
```

### Full build

Succeeded:

```text
✔ [7979/7981] Built Mlc.DirectRoute (3.2s)
✔ [7980/7981] Built Mlc (2.0s)
Build completed successfully (7981 jobs).
```

## `sorry` / `axiom` status

No new declaration-level `sorry` or `axiom` was introduced.

A grep hit for `axiom` in `ConstructiveBasinCoordinate.lean` is only the word
appearing in existing doc text, not a declaration. The same grep also reports
`sorry` strings inside `check_axioms.lean` user-facing output, again not a proof
artifact.

## Axiom frontier check

I ran:

```text
lake env lean check_axioms.lean
```

and it exited successfully.

`check_axioms.lean` is configured to allow exactly the expected frontier:
- `Quot.sound`
- `propext`
- `Classical.choice`
- `MLC.green_sublevel_translate_inter_mandelbrot_connected_straddling`
- `MLC.residualOpenVirtualNearMoleculeAxiom`

Since the command returned exit code `0`, this task did not add any new axiom to
`MLC.mlc_conjecture`, and the frontier remains exactly the expected two project
axioms together with the standard logical/classical ones already listed there.

## Exact coherent-data status after this task

For `PrincipalPullbackCoherentDataFor c`:

Landed in-repo:
- `extends_near`
- `norm_on_basin`
- `basin_of_norm_gt_one`
- `conj_on_basin`
- `modulus_on_basin`
- `tendsto_div_atInfinity`

Reduced to the single remaining explicit hypothesis:
- `holo_on_basin`

This is the intended reduction: the coherent-data target is now exactly one named
holomorphicity seam.

## Honest `holo_on_basin` investigation

### Why the principal candidate is not holomorphic

The principal-pullback candidate is built from principal `Complex.cpow`. On an
escape band of level `N`, the relevant expression is of the form

```lean
(MLC.logSeriesBottcherApprox c ((MLC.quadratic_map c)^[N] z)) ^ (((2 : ℂ) ^ N)⁻¹)
```

Mathlib’s `cpow_const` differentiability lemmas require the base to lie in
`Complex.slitPlane`, i.e. to avoid `ℝ≤0`.

But `MLC.logSeriesBottcherApprox c w / w → 1` at infinity, so on the exterior the
map takes values with all large arguments, including negative real values. Thus
its image genuinely crosses `ℝ<0`. Across those crossings, the principal branch
of `cpow` picks up the expected jump factor `exp(2π i / 2^N)`. Therefore the
principal candidate is not merely hard to prove holomorphic: it has genuine jump
behavior, so `DifferentiableOn` on the whole basin is the wrong statement for
this particular single-valued principal-branch definition.

### Genuine route instead

The correct route is the monodromy-coherent construction already scaffolded in
this repository, not the principal branch candidate.

Relevant existing structures in
`Mlc/Quadratic/Complex/Bottcher/ConstructiveBasinCoordinate.lean`:
- `PullbackRootMonodromyRepresentation`
- `EscapeTimeIndependentPullbackDataFor`
- `MonodromyTrivialPullbackDataFor`
- `BasinLoopPullbackRootMonodromyData`
- conversions from loop/log comparison data to
  `MonodromyTrivialPullbackDataFor`

This is the right framework: the issue is not local differentiability of the
principal branch, but global single-valued holomorphicity after trivializing the
root monodromy. Conceptually, this should reduce to simple-connectivity of
`basin_of_infinity c` in the connected-filled-Julia case (`c ∈ M`).

### Minimal next lemma direction

The next honest lemma is not a `cpow_const` bandwise differentiability lemma for
`basinLogSeriesExtensionCandidate`. Instead it should assert that trivial root
monodromy upgrades escape-time-independent pullback data to a genuine
single-valued holomorphic basin coordinate.

In other words, the next worker should target the monodromy-trivial side of the
pipeline, not further properties of the principal-branch candidate.

## Next discharge item

Immediate next discharge item: **monodromy-trivial holomorphic basin coordinate
construction** (the actual `holo_on_basin` replacement route), which then feeds
the Böttcher local-parameter-family package and the straddling-axiom closure
chain.
