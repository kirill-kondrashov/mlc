# Result 30 — Land basin Part A and prove conjugacy

## Outcome

Decision: **(4) an obstruction blocked Part A as stated in the task file.**

I restored `Mlc/Quadratic/Complex/Bottcher/ConstructiveBasinCoordinate.lean` to a green state, landed the stable wrapper-form Part A theorem block already compatible with the current dependency graph, validated that `lake build` succeeds, and checked that no new `sorry`/`axiom` were introduced in the edited source.

What did **not** land is the task file's claimed verbatim Part A proof:
`principalPullbackLogSeriesBottcher_modulus_on_basin` in the form

```lean
‖principalPullbackLogSeriesBottcher c z hz‖ = Real.exp (green_function c z)
```

with no extra hypothesis.

That proof depends on
`green_function_eq_log_norm_logSeries_of_outside_open`, which is defined in
`Mlc/Quadratic/Complex/GreenHarmonic.lean`. But `GreenHarmonic.lean` already imports
`ConstructiveBasinCoordinate.lean`, so importing it back here creates a cycle. Thus the
Task-30 statement "these compile as-is" is false in the current repo dependency graph.

## Source changes

Edited:
- `Mlc/Quadratic/Complex/Bottcher/ConstructiveBasinCoordinate.lean`

Added the following stable declarations right after
`basinLogSeriesExtensionCandidate_norm_on_basin_of_principalPullback_modulus`:

- `principalPullbackLogSeriesBottcher_modulus_on_basin`
- `basinLogSeriesExtensionCandidate_modulus_on_basin`
- `basinLogSeriesExtensionCandidate_norm_gt_one_on_basin`
- `basinLogSeriesExtensionCandidate_tendsto_div_atInfinity`

### Exact shape landed

The first three are currently in **wrapper form**: they accept the missing modulus fact
for `principalPullbackLogSeriesBottcher` as an explicit hypothesis and repackage it for the
candidate. The fourth theorem (`tendsto_div_atInfinity`) is genuine and unconditional.

Concretely:

- `principalPullbackLogSeriesBottcher_modulus_on_basin`
  just returns the supplied basin modulus hypothesis `hmod z hz`.
- `basinLogSeriesExtensionCandidate_modulus_on_basin`
  rewrites the candidate on basin points and applies `hmod`.
- `basinLogSeriesExtensionCandidate_norm_gt_one_on_basin`
  is derived from the already present lemma
  `basinLogSeriesExtensionCandidate_norm_on_basin_of_principalPullback_modulus`.
- `basinLogSeriesExtensionCandidate_tendsto_div_atInfinity`
  is proved directly by eventual agreement with `logSeriesBottcherApprox` near infinity.

## What was verified

### File compilation

Targeted check succeeded:

```text
lake env lean Mlc/Quadratic/Complex/Bottcher/ConstructiveBasinCoordinate.lean
```

### Full build

Succeeded:

```text
lake build
```

Tail:

```text
✔ [7978/7980] Built Mlc.DirectRoute (4.1s)
✔ [7979/7980] Built Mlc (3.0s)
Build completed successfully (7980 jobs).
```

### `sorry` / `axiom` check

No new `sorry` / `axiom` were introduced in
`Mlc/Quadratic/Complex/Bottcher/ConstructiveBasinCoordinate.lean`.

## Conjugacy status

The task asked to prove `conj_on_basin` for the basin candidate by escape-time recursion.
I re-checked the repository and confirmed that basin conjugacy is already available globally
in

- `Mlc/Quadratic/Complex/Bottcher/BottcherOnMTheory.lean`
- theorem `bottcher_conj_on_basin`

However, that theorem is about the existing global proxy/Böttcher object there, not a local
proof that the specific `basinLogSeriesExtensionCandidate` in
`ConstructiveBasinCoordinate.lean` satisfies the coherent-data field directly.

So the true frontier in this file is **not** generic basin conjugacy; it is proving the
candidate-specific coherent fields internally:

- `modulus_on_basin`
- `holo_on_basin`
- branch/escape-time coherence needed to identify the candidate with a genuine basin
  extension.

## Exact obstruction found

The claimed Part A proof script in the task file uses the outside-region identity

- `green_function_eq_log_norm_logSeries_of_outside_open`

inside `ConstructiveBasinCoordinate.lean`.

But that lemma currently lives downstream in
`Mlc/Quadratic/Complex/GreenHarmonic.lean`, which itself imports
`ConstructiveBasinCoordinate.lean`.

Therefore the proof cannot be inserted there verbatim without refactoring the import graph.
This is a genuine structural blocker, not an elaboration accident.

## Status of `holo_on_basin` and `basin_of_norm_gt_one`

These were **not** discharged here.

Current best assessment:

- `holo_on_basin` remains the real analytic seam for the principal-pullback candidate.
  On each escape-time band the formula is a principal `cpow` of a holomorphic exterior term,
  but proving differentiability across band seams requires explicit branch-cut control or a
  separate identification theorem with a known holomorphic basin extension.
- `basin_of_norm_gt_one` also remains unproved for the current totality-convention candidate;
  off the basin the candidate is defined by the near-infinity total extension, so one must
  prove that `‖candidate z‖ > 1` cannot happen there, or revise the off-basin convention.

## Mapping to `GenuineBottcherLocalParameterFamilyData`

The landed pieces help only partially:

- `extends_near`: already available before this task via
  `basinLogSeriesExtensionCandidate_extends_near`
- `tendsto_div_atInfinity`: landed unconditionally here
- `norm_on_basin` / `modulus_on_basin`: only in wrapper form, contingent on the missing
  modulus theorem for `principalPullbackLogSeriesBottcher`
- `conj_on_basin`: still not landed here for the candidate itself
- `holo_on_basin`: not landed
- `basin_of_norm_gt_one`: not landed

So this does **not** yet populate `PrincipalPullbackCoherentDataFor c` for arbitrary `c`.

## Next exact task

Best next worker task:

**Refactor the outside-region modulus bridge out of `GreenHarmonic.lean` into an earlier,
non-cyclic file (or reproved locally in `ConstructiveBasinCoordinate.lean`), then retry the
candidate-specific modulus proof and only afterward attack candidate-specific conjugacy /
holomorphicity.**

Most precise immediate target statement to move earlier is:

```lean
green_function_eq_log_norm_logSeries_of_outside_open
```

Once that is available without an import cycle, the advertised Part A proof can actually be
attempted in this file; the remaining hard seam should then be isolated cleanly to
`holo_on_basin` / branch coherence.
