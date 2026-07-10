# GPT-5.4 Result 41 — parameter external-coordinate foundation

## Decision

**Outcome B — exact blocker.**

I did verify that the repository supports a **minimal proxy-valued function** on
`{c : ℂ // c ∉ MandelbrotSet}` with theorem `1 < ‖·‖`, but that function is

```lean
c ↦ Quadratic.proxy_bottcher_map c c
```

and therefore is **not** the honest parameter external coordinate
`Φ_M(c) = B_c(c)` requested by the task contract. Since Task 41 explicitly forbids
relabeling fixed-parameter dynamical/proxy objects as the parameter-plane
uniformization, the correct outcome is a blocker report rather than a source edit.

---

## What was compile-verified

I compiled the following temporary probe:

```bash
cd /home/kir/pers/mlc && lake env lean /tmp/task41_probe.lean
```

using:

```lean
import Mlc.ParaPuzzleContainment
import Mlc.GreenSublevelJoinedToKc
import Mlc.Quadratic.Complex.Bottcher.ConstructiveBasinCoordinate

open MLC Quadratic Complex Set Filter Metric Real

namespace Task41Probe

noncomputable def parameterExternalCoord (c : {c : ℂ // c ∉ MandelbrotSet}) : ℂ :=
  Quadratic.proxy_bottcher_map c.1 c.1

lemma critical_value_not_mem_K (c : {c : ℂ // c ∉ MandelbrotSet}) :
    c.1 ∉ Quadratic.K c.1 := by
  intro hcK
  have hbd : MLC.Quadratic.boundedOrbit c.1 c.1 := by
    change MLC.Quadratic.boundedOrbit c.1 c.1 at hcK
    exact hcK
  obtain ⟨B, hB⟩ := hbd
  have hM : c.1 ∈ MandelbrotSet := by
    refine ⟨max B ‖c.1‖, ?_⟩
    intro n
    cases' n with n
    · simpa using (le_max_right B ‖c.1‖)
    · have hstep : orbit c.1 0 (n + 1) = orbit c.1 c.1 n := by
        rw [← MLC.Quadratic.orbit_param_eq_orbit_zero_succ c.1 n]
      rw [hstep]
      exact le_trans (hB n) (le_max_left B ‖c.1‖)
  exact c.2 hM

lemma critical_value_in_basin (c : {c : ℂ // c ∉ MandelbrotSet}) :
    c.1 ∈ Quadratic.basin_of_infinity c.1 :=
  z_in_basin_of_not_mem_K c.1 c.1 (critical_value_not_mem_K c)

lemma one_lt_norm_parameterExternalCoord (c : {c : ℂ // c ∉ MandelbrotSet}) :
    1 < ‖parameterExternalCoord c‖ := by
  have hbasin : c.1 ∈ Quadratic.basin_of_infinity c.1 := critical_value_in_basin c
  simpa [parameterExternalCoord, Quadratic.proxy_bottcher_map]
    using Quadratic.one_lt_norm_polar_green_map_of_mem_basin c.1 c.1 hbasin

#check parameterExternalCoord
#check one_lt_norm_parameterExternalCoord

end Task41Probe
```

Result:
- compile succeeded;
- only warning was an unnecessary-`simpa` linter note.

This proves the **domain bridge** is available:

```text
c ∉ MandelbrotSet
→ c ∉ K(c)
→ c ∈ basin_of_infinity c
→ 1 < ‖proxy_bottcher_map c c‖.
```

---

## Exact checked declarations used in the audit

### Critical-value escape bridge

From `Mlc/ParaPuzzleContainment.lean`:

- `MLC.Quadratic.orbit_param_eq_orbit_zero_succ`

From `Mlc/GreenSublevelJoinedToKc.lean`:

- `z_in_basin_of_not_mem_K`

From the existing quadratic definitions:

- `MandelbrotSet`
- `MLC.Quadratic.K`
- `MLC.Quadratic.boundedOrbit`

### Proxy outside-unit theorem

From `Mlc/Quadratic/Complex/Bottcher/ConstructiveBasinCoordinate.lean`:

- `Quadratic.one_lt_norm_polar_green_map_of_mem_basin`

plus the definitional identity:

- `Quadratic.proxy_bottcher_map = Quadratic.polar_green_map`

### Genuine near-infinity provider infrastructure already present

Audited earlier and still relevant:

- `MLC.logSeriesBottcherApprox`
- `MLC.one_lt_norm_logSeriesBottcherApprox_of_outside_open`
- `MLC.logSeriesBottcherApprox_conj_of_large_radius`
- `MLC.tendsto_logSeriesBottcherApprox_div_atInfinity`
- `MLC.Quadratic.logSeriesNearInfinityParameterFamily`
- `MLC.exists_param_holo_bottcher_inverse`
- `MLC.Quadratic.basinLogSeriesExtensionCandidate`
- `MLC.Quadratic.EscapeTimeIndependentPullbackDataFor`
- `MLC.Quadratic.MonodromyTrivialPullbackDataFor`

---

## Why Outcome A is still not honest

The minimal compiled function above does **not** use a genuine holomorphic Böttcher
coordinate on the basin. It uses the proxy/polar-Green map. Task 41 explicitly forbids
using that route as the parameter external coordinate.

The genuine provider that does exist,

```lean
MLC.logSeriesBottcherApprox c z
```

is only packaged with checked theorems on a **near-infinity exterior region**. For
arbitrary escaping parameters `c ∉ MandelbrotSet`, the evaluation point `z = c` is not
in that exterior region in general, so the current theorems do not directly define
`B_c(c)`.

The local parameter-holomorphic inverse theorems also do not solve this by themselves:

- they are local near an exterior basepoint;
- they do not package a global whole-basin evaluation theorem at arbitrary escaping
  points;
- they do not by themselves prove escape-time-independent pullback or branch coherence
  for `z = c`.

So the repo currently supports:

```text
honest near-infinity Böttcher coordinate
+ local param-holomorphic inverse near infinity
```

but not yet the global statement

```text
for every c ∉ MandelbrotSet, the value B_c(c) is canonically defined.
```

---

## First missing bridge

The first missing theorem/data package is an **escape-time-independent genuine basin
extension/evaluation theorem** for the near-infinity log-series coordinate.

Concretely, the missing statement is of the form:

> For fixed `c` and any `z ∈ basin_of_infinity c`, choose `N` so that
> `(quadratic_map c)^[N] z` lies in the near-infinity domain of
> `logSeriesBottcherApprox c`. Pull back
> `logSeriesBottcherApprox c ((quadratic_map c)^[N] z)` through the functional equation.
> Then the resulting value is independent of sufficiently large `N` and of all admissible
> root / continuation choices, giving a canonical value `B_c(z)` on the full basin.

For Task 41, the needed specialization is `z = c`, yielding the honest parameter
external coordinate

```lean
Φ_M(c) = B_c(c).
```

The repository already contains the correct scaffolding names for this missing bridge:

- `MLC.Quadratic.basinLogSeriesExtensionCandidate`
- `MLC.Quadratic.EscapeTimeIndependentPullbackDataFor`
- `MLC.Quadratic.MonodromyTrivialPullbackDataFor`

This confirms the obstruction is well-localized: the unresolved step is no longer the
construction of a near-infinity coordinate, but the proof that its pullback/evaluation is
well-defined on all escaping basin points, especially at the critical value.

---

## How this advances the moving-parameter route

This audit narrows the moving-parameter replacement route to a precise technical gate:

```text
near-infinity genuine Böttcher family  [already checked]
→ whole-basin escape-time/branch-independent extension at escaping points  [missing]
→ define Φ_M(c)=B_c(c) on ℂ \ MandelbrotSet
→ parameter equipotentials / finite parameter graph
→ parapuzzle components
```

So Task 41 does clarify the plan: the next worker should not search for another
near-infinity provider and should not revive the proxy route. The repo already has the
right near-infinity object; it needs the basin-extension correctness theorem.

---

## Smallest next worker task

**Next task:** prove or block the genuine whole-basin extension theorem for
`logSeriesBottcherApprox`.

A tightly scoped worker contract would be:

1. audit `ConstructiveBasinCoordinate.lean` for the exact status of
   `basinLogSeriesExtensionCandidate`, `EscapeTimeIndependentPullbackDataFor`, and
   `MonodromyTrivialPullbackDataFor`;
2. determine whether escape-time independence can already be proved for arbitrary
   `z ∈ basin_of_infinity c` from existing finite-level root coherence lemmas landed in
   Tasks 37–40;
3. if yes, implement the canonical basin coordinate and specialize to `z = c`;
4. if not, identify the first still-missing coherence lemma (escape-time independence,
   monodromy triviality, or branch compatibility) with a minimal theorem statement.

That is the smallest honest next step toward the parameter-plane external coordinate.
