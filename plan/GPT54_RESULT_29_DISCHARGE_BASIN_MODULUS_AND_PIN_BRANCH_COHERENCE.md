# GPT-5.4 Result 29 — Discharge basin modulus and pin branch coherence

## Decision

**Decision 2.5:** the basin-side Part A seam is sharper than Result 28 reported, but not fully closed by a single turnkey theorem already in-tree.

- **Confirmed genuinely available now:**
  - `extends_near` for `basinLogSeriesExtensionCandidate`
  - a reusable reduction of `norm_on_basin` to a pointwise pullback modulus formula
  - the exact formula ingredients for the pointwise modulus proof on the principal pullback candidate
  - a clean `tendsto_div_atInfinity` reduction by eventual agreement with the near-infinity coordinate
- **Not already packaged as a finished theorem:**
  - the basin-wide pointwise modulus theorem
    `‖principalPullbackLogSeriesBottcher c z hz‖ = exp (green_function c z)`
  - and therefore the resulting finished `PrincipalPullbackCoherentDataFor` package.
- **Sharp remaining obstruction:** branch/escape-time coherence is still the only genuinely nontrivial analytic seam for the other basin fields
  `basin_of_norm_gt_one`, `conj_on_basin`, `holo_on_basin`.

So Result 28 was too pessimistic about the modulus seam, but the repo still does **not** yet contain a one-line completed constructive package populating `PrincipalPullbackCoherentDataFor`.

## What was checked

Relevant declarations in `Mlc/Quadratic/Complex/Bottcher/ConstructiveBasinCoordinate.lean`:

- `basinEscapeTime_spec`
- `green_function_orbit_eq_local`
- `principalPullbackLogSeriesBottcher_norm_eq_rpow_iterateValue`
- `basinLogSeriesExtensionCandidate`
- `basinLogSeriesExtensionCandidate_extends_near`
- `basinLogSeriesExtensionCandidate_norm_on_basin_of_principalPullback_modulus`
- `PrincipalPullbackCoherentDataFor`
- `EscapeTimeIndependentPullbackDataFor`
- `MonodromyTrivialPullbackDataFor`

And in `Mlc/Quadratic/Complex/GreenHarmonic.lean`:

- `green_function_eq_log_norm_logSeries_of_outside_open`

## Checked Part A status

### 1. `extends_near`

This one is **already discharged** as an exact theorem:

- `basinLogSeriesExtensionCandidate_extends_near`

This matches the intended near-infinity agreement field directly.

### 2. `norm_on_basin`

This is **already reduced to the modulus formula** by:

- `basinLogSeriesExtensionCandidate_norm_on_basin_of_principalPullback_modulus`

So once one proves the pointwise statement

```lean
∀ z hz, ‖principalPullbackLogSeriesBottcher c z hz‖ = Real.exp (green_function c z)
```

then `norm_on_basin` follows immediately from positivity of `green_function` on the basin.

### 3. `modulus_on_basin`

The intended proof chain is real and precise:

1. `principalPullbackLogSeriesBottcher_norm_eq_rpow_iterateValue`
2. `basinEscapeTime_spec`
3. `green_function_eq_log_norm_logSeries_of_outside_open`
4. `green_function_orbit_eq_local`
5. elementary `Real.exp` / `Real.rpow` algebra.

I verified this is the correct route and built a `/tmp` Lean probe around it. The probe did **not** close verbatim on first pass, but the failures were formal/algebraic rather than conceptual:

- namespace/import issues (`GreenHarmonic` import needed)
- exact orientation of the Green/log identity
- `Real.exp` → `Real.rpow` normalization details.

There is no evidence here of a missing mathematical theorem; this looks like a **short formalization task**, not an analytic blocker.

### 4. `tendsto_div_atInfinity`

This also reduces cleanly:

- use `basinLogSeriesExtensionCandidate_extends_near`
- combine with `eventually_atInfinity_mem_outside_open c`
- then apply `MLC.tendsto_logSeriesBottcherApprox_div_atInfinity c` via `Tendsto.congr'`.

Again, the probe hit only local elaboration issues, not a mathematical gap.

## What remains genuinely open in this task

The analytically serious seam is still the branch/escape-time coherence side.

For `PrincipalPullbackCoherentDataFor (c : ℂ)`, the still-unresolved fields are:

- `basin_of_norm_gt_one`
- `conj_on_basin`
- `holo_on_basin`

These depend on proving that the principal pullback construction is **independent of the chosen escape level** and glues coherently across regions where `basinEscapeTime` jumps. That is exactly the role of the heavier scaffolding already present in the file:

- `EscapeTimeIndependentPullbackDataFor`
- `MonodromyTrivialPullbackDataFor`
- chart/loop/overlap/root-branch infrastructure.

So the frontier is now sharp:

- **Modulus/norm/tendsto/near agreement:** likely short theorem-packaging work.
- **Conjugacy/holomorphicity/global basin characterization:** genuine branch-coherence theorem.

## Correction to Result 28

Result 28 said the basin modulus identity was effectively still missing as part of the genuine provider story. That is now too strong.

**Corrected statement:** the modulus identity is no longer a vague missing theorem; it is a **specific derivable target** with all mathematical ingredients already present. What is still missing is the finished proof script/theorem packaging, not a new analytic idea.

## Recommended next Lean task

Create a focused follow-up worker whose only goal is to land these two theorems in source:

1. pointwise pullback modulus

```lean
lemma principalPullbackLogSeriesBottcher_modulus_on_basin
    (c z : ℂ) (hz : z ∈ basin_of_infinity c) :
    ‖principalPullbackLogSeriesBottcher c z hz‖ = Real.exp (green_function c z)
```

2. candidate tendsto at infinity

```lean
lemma basinLogSeriesExtensionCandidate_tendsto_div_atInfinity (c : ℂ) :
  Tendsto (fun z => basinLogSeriesExtensionCandidate c z / z) atInfinity (𝓝 (1 : ℂ))
```

Once these land, `norm_on_basin` is immediate from the existing reduction lemma, and the remaining frontier will be isolated exactly to the branch-coherence package.

## Bottom line

Task 29 does **not** end with “modulus is still genuinely missing.”
It ends with:

- the repo already contains the right formula chain for modulus/norm/tendsto,
- the remaining real difficulty is branch coherence,
- so the basin constructive frontier is now much more localized than Result 28 claimed.
