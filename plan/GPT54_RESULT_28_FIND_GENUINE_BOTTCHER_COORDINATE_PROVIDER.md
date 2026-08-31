# GPT-5.4 Result 28 — genuine Böttcher coordinate provider audit

## Scope and constraints followed

I treated this as a read-only audit except for writing this result artifact. I did **not** edit Lean sources, prior plan artifacts, or dependencies, and I did **not** commit. I excluded `polar_green_map` and `proxy_bottcher_map` as coordinate providers, per task contract.

## Decision

**Decision 2.** A genuine axiom-clean **near-infinity** Böttcher provider exists, but one explicit continuation/evaluation theorem is still missing before the parameter external coordinate `Φ_M(c)=B_c(c)` is honestly available for arbitrary `c ∉ MandelbrotSet`.

---

## 1. Genuine candidate found

The strongest genuine candidate currently present in the repository is:

- `MLC.logSeriesBottcherApprox (c z : ℂ) : ℂ`

This is the explicit log/product Böttcher construction, not the proxy/polar Green map.

### Checked declarations (compile-verified)

From a `/tmp` Lean probe:

```lean
#check MLC.logSeriesBottcherApprox
#check Quadratic.genuineBottcherNearInfinityDataFor_logSeriesBottcherApprox
#check MLC.one_lt_norm_logSeriesBottcherApprox_of_outside_open
#check MLC.logSeriesBottcherApprox_conj_of_large_radius
#check MLC.logSeriesBottcherApprox_differentiableOn_large_radius
#check MLC.tendsto_logSeriesBottcherApprox_div_atInfinity
#check MLC.Quadratic.GenuineBottcherNearInfinityParameterFamilyData
#check MLC.Quadratic.logSeriesNearInfinityParameterFamily
#check MLC.exists_param_holo_bottcher_inverse
#check MLC.Quadratic.EscapeTimeIndependentPullbackDataFor
#check MLC.Quadratic.MonodromyTrivialPullbackDataFor
#check MLC.Quadratic.basinLogSeriesExtensionCandidate
#check MLC.Quadratic.GenuineBottcherLocalParameterFamilyData.toNearInfinityParameterExtensionData
```

Output:

- `MLC.logSeriesBottcherApprox (c z : ℂ) : ℂ`
- `MLC.Quadratic.genuineBottcherNearInfinityDataFor_logSeriesBottcherApprox (c : ℂ) : GenuineBottcherNearInfinityDataFor c (logSeriesBottcherApprox c)`
- `MLC.one_lt_norm_logSeriesBottcherApprox_of_outside_open ...`
- `MLC.logSeriesBottcherApprox_conj_of_large_radius ...`
- `MLC.logSeriesBottcherApprox_differentiableOn_large_radius ...`
- `MLC.tendsto_logSeriesBottcherApprox_div_atInfinity (c : ℂ) : Tendsto ... atInfinity (𝓝 1)`
- `MLC.Quadratic.logSeriesNearInfinityParameterFamily ... : GenuineBottcherNearInfinityParameterFamilyData c₀`
- `MLC.exists_param_holo_bottcher_inverse ...`
- `MLC.Quadratic.EscapeTimeIndependentPullbackDataFor (c : ℂ) : Type`
- `MLC.Quadratic.MonodromyTrivialPullbackDataFor (c : ℂ) : Type 1`
- `MLC.Quadratic.basinLogSeriesExtensionCandidate (c z : ℂ) : ℂ`

This probe compiled successfully.

---

## 2. Acceptance-criteria audit

The task required five criteria.

### Criterion 1 — holomorphicity / conformality / nonzero derivative

**Satisfied near infinity.**

Evidence:

- `MLC.logSeriesBottcherApprox_differentiableOn_large_radius`
- parameter holomorphy/joint continuity package in `BottcherParamHolo.lean`
- local inverse near infinity in `BottcherInverse.lean`
- parameter inverse near infinity in `BottcherParamInverse.lean`

In particular:

- near-infinity fiber differentiability is checked;
- a parameter family exists:
  `MLC.Quadratic.logSeriesNearInfinityParameterFamily`
- a local parameter-holomorphic inverse exists:
  `MLC.exists_param_holo_bottcher_inverse`

So the repository does contain a genuine analytic coordinate **on a specified exterior domain**.

### Criterion 2 — functional equation `B_c(f_c z) = (B_c z)^2`

**Satisfied near infinity.**

Evidence:

- `MLC.logSeriesBottcherApprox_conj_of_large_radius`
- iterate packaging in `ConstructiveBasinCoordinate.lean`, including
  `logSeriesBottcherApprox_iterate_succ_eq_sq`

This is the genuine Böttcher conjugacy on the large-radius/exterior region.

### Criterion 3 — normalization `B_c(z)/z → 1` at infinity

**Satisfied.**

Evidence:

- `MLC.tendsto_logSeriesBottcherApprox_div_atInfinity`

This gives the standard uniqueness normalization.

### Criterion 4 — codomain outside the unit disk

**Satisfied on the exterior domain.**

Evidence:

- `MLC.one_lt_norm_logSeriesBottcherApprox_of_outside_open`

So the image is in the outside of the unit disk where the map is already constructed.

### Criterion 5 — enough uniqueness to rule out arbitrary angle choices

**Satisfied near infinity, but not yet globally on the full basin.**

Near infinity, uniqueness is controlled by the normalization and local inverse theory. But I did **not** find a proved theorem that extends this uniquely and branch-independently to arbitrary escaping points in the whole basin, especially to the critical value `z = c` for every `c ∉ MandelbrotSet`.

This is exactly where the global provider remains incomplete.

---

## 3. Near infinity versus full basin

### Exact domain currently available

The concrete theorems I verified work on a fixed exterior region of the form

- `{z : ℂ | R < ‖z‖}` with `‖c‖ + 2 ≤ R`, or concretely
- `{z : ℂ | ‖z‖ > ‖c‖ + 2}` in the simplest outside-open statements.

This is enough for a genuine near-infinity coordinate.

### Why this is not enough for `Φ_M(c)=B_c(c)`

For a general escaping parameter `c ∉ MandelbrotSet`, the critical value to evaluate is `z = c`. There is no reason that `c` itself lies in a fixed near-infinity region such as `‖z‖ > ‖c‖ + 2`; indeed it generally does not.

So the current proved near-infinity provider does **not** directly define `B_c(c)`.

What is needed is the standard pullback/continuation step: choose `N` so that
`(f_c^[N]) c` lands in the exterior region, define a root pullback of the exterior Böttcher value there, and prove the result is independent of:

1. the chosen sufficiently large escape time `N`, and
2. the analytic branch / continuation choice.

---

## 4. What exists for the extension problem

The repository already contains substantial constructive scaffolding for exactly this missing step.

### Verified extension-related declarations

Compiled/located declarations include:

- `MLC.Quadratic.EscapeTimeIndependentPullbackDataFor (c : ℂ) : Type`
- `MLC.Quadratic.MonodromyTrivialPullbackDataFor (c : ℂ) : Type 1`
- `MLC.Quadratic.basinLogSeriesExtensionCandidate (c z : ℂ) : ℂ`
- `MLC.Quadratic.GenuineBottcherLocalParameterFamilyData.toNearInfinityParameterExtensionData`

And `BottcherMotion.lean` exposes the intended theorem surfaces:

- `GenuineBottcherLocalFamilyData`
- `GenuineBottcherLocalParameterFamilyData`
- `GenuineBottcherNearInfinityParameterFamilyData`
- `GenuineBottcherNearInfinityParameterExtensionData`

This shows the repository has already isolated the correct obstruction: not constructing a new exterior coordinate, but proving that the pullback from the exterior to the whole basin is well-defined and branch-independent.

---

## 5. Earliest missing theorem

The earliest missing theorem is a genuine **escape-time-independent pullback extension** from `logSeriesBottcherApprox` on the exterior to arbitrary escaping basin points.

A concrete statement should look like:

> For fixed `c` and any `z ∈ basin_of_infinity c`, define `φ_c(z)` by choosing `N` with
> `f_c^[N](z)` in the exterior domain and pulling back
> `logSeriesBottcherApprox c (f_c^[N] z)` through the functional equation.
> Then the resulting value is independent of the sufficiently large escape time `N`
> and of all admissible root/continuation branch choices.

Operationally, this is the theorem needed to justify

- `B_c(z) := root_{2^N}(logSeriesBottcherApprox c ((quadratic_map c)^[N] z))`

as a well-defined value on the basin.

Once that is proved, evaluation at the critical value `z = c` becomes honest for `c ∉ MandelbrotSet`.

### Why this is the first missing theorem, not something earlier

Because the repository already has:

- a genuine normalized near-infinity coordinate;
- near-infinity conjugacy;
- exterior image outside the unit disk;
- near-infinity parameter holomorphy;
- a local parameter-holomorphic inverse near infinity;
- explicit extension candidate/scaffolding names for escape-time independence and monodromy triviality.

So the bottleneck is no longer “find any Böttcher map.” It is precisely “prove the extension/evaluation is independent of escape time and branch.”

---

## 6. Dependency / axiom audit

### Genuine near-infinity route

The near-infinity `logSeriesBottcherApprox` route appears axiom-clean from the files audited:

- `Mlc/Quadratic/Complex/Bottcher/BottcherOutsidePlan.lean`
- `Mlc/Quadratic/Complex/Bottcher/ConstructiveBasinCoordinate.lean`
- `Mlc/Quadratic/Complex/Bottcher/BottcherParamHolo.lean`
- `Mlc/Quadratic/Complex/Bottcher/BottcherInverse.lean`
- `Mlc/Quadratic/Complex/Bottcher/BottcherParamInverse.lean`

### Explicit negative references

I re-confirmed that older “global” Böttcher files still contain explicit axioms and therefore cannot certify a genuine full provider:

- `Mlc/Quadratic/Complex/Bottcher/BottcherAxioms.lean`
  - includes axioms such as `external_ray_map_exists`, `bottcher_seq_converges`,
    `extended_ray_map_free_continuous`
- `Mlc/Quadratic/Complex/Bottcher/BottcherOnMTheory.lean`
  - includes explicit axiom-backed/global placeholders such as
    `bottcher_outside_axiom`, `proxy_bottcher_map_inj_on_K`

Therefore the full-provider conclusion cannot honestly be based on those files.

### MainConjecture bridge status

I also checked the theorem-facing bridge declarations in `Mlc/MainConjecture.lean`:

- `def GenuineBottcherLocalParameterExtensionBridgeTwo : Prop :=
    ∀ h_route : Quadratic.GenuineBottcherRouteFor (2 : ℂ),
      Nonempty (Quadratic.GenuineBottcherLocalParameterFamilyData (2 : ℂ))`
- `def GenuineBottcherNearInfinityParameterExtensionBridgeTwo : Prop :=
    ∀ h_route : Quadratic.GenuineBottcherRouteFor (2 : ℂ),
      Nonempty (Quadratic.GenuineBottcherNearInfinityParameterExtensionData (2 : ℂ))`

This matches the audit outcome: the theorem-facing frontier still asks for a nonempty local/full extension package, not merely the exterior family.

---

## 7. Why proxy/polar maps were rejected

Per task contract, I excluded:

- `polar_green_map`
- `proxy_bottcher_map`

as coordinate providers.

Reason: these may encode Green-radius information, but they do **not** serve as the genuine holomorphic Böttcher coordinate implementing the conjugacy with controlled angle/branch behavior. The repository’s genuine route is the log-series coordinate, not the proxy.

---

## 8. Final status

### What is genuinely present now

- explicit near-infinity Böttcher coordinate `logSeriesBottcherApprox`;
- checked conjugacy near infinity;
- checked normalization at infinity;
- checked exterior image outside the unit disk;
- checked fiber differentiability near infinity;
- checked near-infinity parameter family;
- checked local parameter-holomorphic inverse near infinity;
- explicit scaffolding for escape-time-independent/monodromy-trivial extension.

### What is still missing

- a theorem proving that the pullback construction from the exterior defines a unique, branch-independent value on all of `basin_of_infinity c`;
- in particular, enough to evaluate at the critical value `z = c` for every `c ∉ MandelbrotSet`.

Hence parameter external coordinate evaluation is **not yet ready**.

---

## 9. Exact next worker task

Next worker task:

> Prove the escape-time-independent pullback extension theorem for
> `logSeriesBottcherApprox`: for `z ∈ basin_of_infinity c`, the pullback value
> obtained from `logSeriesBottcherApprox c ((quadratic_map c)^[N] z)` is
> independent of sufficiently large escape time `N` and of admissible root/branch
> choices, yielding a well-defined basin coordinate and therefore a genuine
> evaluation at `z = c` for `c ∉ MandelbrotSet`.

This should be done by using the existing scaffolding around:

- `EscapeTimeIndependentPullbackDataFor`
- `MonodromyTrivialPullbackDataFor`
- `basinLogSeriesExtensionCandidate`

and by proving the relevant branch/monodromy triviality theorem rather than introducing another abstract property bundle.

---

## 10. Temporary Lean probe

I used `/tmp/task28_probe.lean` only, with `lake env lean /tmp/task28_probe.lean`, and it compiled successfully.

## 11. Repository modifications

Only this result artifact was written:

- `plan/GPT54_RESULT_28_FIND_GENUINE_BOTTCHER_COORDINATE_PROVIDER.md`

No Lean source files were edited. No commit was made.
