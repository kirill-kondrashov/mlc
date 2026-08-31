# Result 31 — Land basin coherent fields

## Outcome

Decision: **(3) six fields landed, `holo_on_basin` remains a genuine open seam, build green with no new `sorry`.**

This task corrected the Task 30 placement mistake. The basin modulus / norm / tendsto / conjugacy theorems do compile, but **not** inside `ConstructiveBasinCoordinate.lean`; they belong in a downstream file importing `GreenHarmonic.lean`.

## What changed

### 1. Removed the forbidden wrapper stubs

Deleted from `Mlc/Quadratic/Complex/Bottcher/ConstructiveBasinCoordinate.lean`:

- `principalPullbackLogSeriesBottcher_modulus_on_basin`
- `basinLogSeriesExtensionCandidate_modulus_on_basin`
- `basinLogSeriesExtensionCandidate_norm_gt_one_on_basin`
- `basinLogSeriesExtensionCandidate_tendsto_div_atInfinity`

The pre-existing reduction lemma
`basinLogSeriesExtensionCandidate_norm_on_basin_of_principalPullback_modulus`
was kept.

### 2. Added and registered the downstream file

Created:

- `Mlc/Quadratic/Complex/Bottcher/ConstructiveBasinModulus.lean`

Registered in:

- `Mlc.lean`

with:

```lean
import Mlc.Quadratic.Complex.Bottcher.ConstructiveBasinModulus
```

placed after `import Mlc.Quadratic.Complex.GreenHarmonic`.

### 3. Landed the verified theorem block downstream

The new file contains these theorem names:

- `principalPullbackLogSeriesBottcher_modulus_on_basin`
- `basinLogSeriesExtensionCandidate_modulus_on_basin`
- `basinLogSeriesExtensionCandidate_norm_gt_one_on_basin`
- `basinLogSeriesExtensionCandidate_tendsto_div_atInfinity`
- `basinEscapeTime_map_of_pos`
- `cpow_two_eq`
- `basinLogSeriesExtensionCandidate_conj_on_basin`

These now live in the correct dependency position and build successfully.

## Exact status of the coherent fields

For `PrincipalPullbackCoherentDataFor c`:

### Landed / available

- `extends_near`
  - already present as `basinLogSeriesExtensionCandidate_extends_near`
- `norm_on_basin`
  - available from `basinLogSeriesExtensionCandidate_norm_gt_one_on_basin`
    together with the earlier reduction path on basin points
- `conj_on_basin`
  - landed as `basinLogSeriesExtensionCandidate_conj_on_basin`
- `modulus_on_basin`
  - landed as `basinLogSeriesExtensionCandidate_modulus_on_basin`
- `tendsto_div_atInfinity`
  - landed as `basinLogSeriesExtensionCandidate_tendsto_div_atInfinity`

### Status of `basin_of_norm_gt_one`

There are **two different statements** here:

1. **On-basin positivity**
   - landed: `basinLogSeriesExtensionCandidate_norm_gt_one_on_basin`
   - statement: if `z ∈ basin_of_infinity c`, then `1 < ‖candidate z‖`

2. **Reverse implication required by the coherent-data field**
   - still open: `1 < ‖candidate z‖ → z ∈ basin_of_infinity c`

I did **not** revise the definition of
`basinLogSeriesExtensionCandidate` in `ConstructiveBasinCoordinate.lean`.
Its current off-basin branch is still `MLC.logSeriesBottcherApprox c z`.
Task 31’s warning appears correct: with this totality convention, the reverse implication is not presently justified and is likely the wrong theorem for the current `def`.

So the exact status is:

- no off-basin branch revision was made,
- no downstream breakage from such a revision was tested,
- the coherent-data field `basin_of_norm_gt_one` is **not discharged**.

### Status of `holo_on_basin`

`holo_on_basin` is still the genuine analytic seam.

On each escape-time band, the candidate is represented by a principal pullback expression of the form

```lean
(L ∘ (quadratic_map c)^[N]) ^ ((2^N : ℂ)⁻¹)
```

where `L` is the near-infinity logarithmic-series Böttcher coordinate. The obstruction is the principal-branch `Complex.cpow`: proving differentiability on the whole basin requires a branch-coherent argument showing the pullback never crosses the forbidden cut in a way that breaks holomorphy, or replacing the presentation with a branch-free holomorphic identification theorem.

I found no existing in-repo theorem that closes this directly.

## Minimal missing lemma / sharp strategy

The sharp next reduction is to prove a branch-coherence lemma for the principal pullback on each escape-time stratum, then derive differentiability by `DifferentiableOn.cpow_const` plus stratum glueing.

Concretely, the next worker should target a named lemma of the following shape in the basin-coordinate file family:

```lean
lemma principalPullbackLogSeriesBottcher_differentiableOn_escapeBand
    (c : ℂ) (N : ℕ) :
    DifferentiableOn ℂ
      (fun z =>
        (MLC.logSeriesBottcherApprox c ((MLC.quadratic_map c)^[N] z)) ^
          (((2 : ℂ) ^ N)⁻¹))
      {z : ℂ |
        z ∈ basin_of_infinity c ∧
        basinEscapeTime c z (by aesop) = N}
```

That statement is not ready to paste verbatim because the set-level dependency on the witness for
`z ∈ basin_of_infinity c` needs a hygienic local wrapper, but this is the exact mathematical seam:
**holomorphicity of the principal-`cpow` pullback on a fixed escape-time band**.

Sharp strategy:

1. define the open escape-time band as a standalone set, avoiding dependent witness noise;
2. prove the iterate lands in the outside-open region on that band;
3. prove the composed exterior coordinate avoids `0` and stays in a principal-log compatible sector / slit-plane neighborhood on the band;
4. apply `DifferentiableOn.cpow_const` to the bandwise expression;
5. identify the bandwise expression with `basinLogSeriesExtensionCandidate` on that band;
6. assemble `DifferentiableOn` over the basin by the partition into escape-time bands.

## Build / validation

Full build succeeded:

```text
✔ [7979/7981] Built Mlc.DirectRoute (3.3s)
✔ [7980/7981] Built Mlc (3.0s)
Build completed successfully (7981 jobs).
```

Targeted module build also succeeded earlier for:

```text
lake build Mlc.Quadratic.Complex.Bottcher.ConstructiveBasinModulus
```

## `sorry` / `axiom` status

No new declaration-level `sorry` or `axiom` was introduced by this task.

A grep hit for `axiom` in `ConstructiveBasinCoordinate.lean` is only the word appearing inside existing documentation text, not a new axiom declaration.

## Mapping to `GenuineBottcherLocalParameterFamilyData`

Current field correspondence from the landed basin work is:

- `extends_near`
  - `basinLogSeriesExtensionCandidate_extends_near`
- `norm_on_basin`
  - `basinLogSeriesExtensionCandidate_norm_gt_one_on_basin` / basin modulus route
- `conj_on_basin`
  - `basinLogSeriesExtensionCandidate_conj_on_basin`
- `modulus_on_basin`
  - `basinLogSeriesExtensionCandidate_modulus_on_basin`
- `tendsto_div_atInfinity`
  - `basinLogSeriesExtensionCandidate_tendsto_div_atInfinity`
- missing for a full theorem-facing package:
  - `basin_of_norm_gt_one` (reverse implication)
  - `holo_on_basin`

So this task materially strengthens the basin package, but it does **not** yet construct `PrincipalPullbackCoherentDataFor c` directly.

## Next discharge item unblocked

Next concrete discharge item: **`Φ_c⁻¹` / puzzle-boundary motion remains downstream, but the immediate local blocker is `holo_on_basin` for the principal-pullback candidate.**

Exact next worker task:

> Define the escape-time bands as explicit open sets, prove bandwise branch coherence for the principal pullback `(logSeriesBottcherApprox ∘ f^N) ^ ((2^N)⁻¹)`, and use that to land `basinLogSeriesExtensionCandidate` differentiable on each band and hence `holo_on_basin`; separately decide whether the off-basin branch of `basinLogSeriesExtensionCandidate` should be revised (e.g. to `0`) so the reverse field `1 < ‖φ z‖ → z ∈ basin_of_infinity c` becomes true.
