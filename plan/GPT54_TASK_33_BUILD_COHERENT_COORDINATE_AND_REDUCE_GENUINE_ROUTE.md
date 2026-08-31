# TASK 33 — Build the coherent basin coordinate and reduce the genuine Böttcher
# coordinate route to exactly `conj` + `holo`

## Global context

`mlc_conjecture` rests on exactly two axioms (`check_axioms.lean`):
`green_sublevel_translate_inter_mandelbrot_connected_straddling` and
`residualOpenVirtualNearMoleculeAxiom`. The Böttcher route to discharging the
straddling axiom needs a genuine holomorphic conjugating coordinate on
`basin_of_infinity c` (this feeds `GenuineBottcherRouteFor c` →
the local-parameter-family closure in `Mlc/MainConjecture.lean`).

### Why the previous candidate cannot carry `holo` (do not revisit it)

Iteration 32 reduced the target to a single `holo_on_basin` hypothesis on
`basinLogSeriesExtensionCandidate`. But that candidate's on-basin value is the
**principal-branch** pullback
`principalPullbackLogSeriesBottcher c z hz = (logSeriesBottcherApprox c (f^[N] z))^((2^N)⁻¹)`
with `N = basinEscapeTime`. Since `logSeriesBottcherApprox c` is asymptotic to the
identity and has real coefficients, it takes values in `ℝ<0` at negative-real
first-entry points, where principal `Complex.cpow` jumps by `exp(2πi/2^N) ≠ 1`.
So `basinLogSeriesExtensionCandidate` has genuine jump discontinuities inside the
basin: `holo_on_basin` is **false** for it, and iteration 32's
`principalPullbackCoherentData_of_holo` — though a valid conditional theorem —
has an unsatisfiable hypothesis. **Leave `basinLogSeriesExtensionCandidate`
untouched; do not try to prove it holomorphic.**

### This task: switch to the coherent coordinate

The correct coordinate is the escape-time-independent (branch-coherent) value
already scaffolded as `EscapeTimeIndependentPullbackDataFor c`
(in `ConstructiveBasinCoordinate.lean`), whose `value` is a common `2^N`-th root
of `logSeriesBottcherApprox c (f^[N] z)` for every escaping level `N`. For this
coordinate, `holo` is achievable (it is the honest single-valued branch), and —
crucially — the Böttcher **modulus** is automatic from the root equation.

This task builds the coherent coordinate as a total function, proves that its
modulus is `exp(green)` and four more `GenuineBottcherCoordinateDataFor` fields
automatically, and lands a constructor reducing that whole target to exactly two
explicit analytic facts about the coherent value: `conj_on_basin` and
`holo_on_basin`.

**Every script below is planner-verified to compile** (targeted `lake env lean`
probe, `PROBE_EXIT_0`) when placed in `ConstructiveBasinModulus.lean`.

## Placement

All declarations go in
`Mlc/Quadratic/Complex/Bottcher/ConstructiveBasinModulus.lean`
(inside its existing `namespace MLC.Quadratic`, downstream of `GreenHarmonic`, so
`green_function_eq_log_norm_logSeries_of_outside_open` and
`basin_of_infinity` resolve). Do **not** create a new file. Do **not** edit
`ConstructiveBasinCoordinate.lean`.

Note the scripts below are written with fully-qualified `MLC.Quadratic.basin_of_infinity`
for probing at top level; inside the file's `namespace MLC.Quadratic` you may use
the unqualified `basin_of_infinity`. Either form compiles.

## Step 1 — Keystone: escape-time-independent value has Böttcher modulus

```lean
theorem escapeTimeIndependent_value_modulus (c : ℂ)
    (d : EscapeTimeIndependentPullbackDataFor c)
    (z : ℂ) (hz : z ∈ basin_of_infinity c) :
    ‖d.value z hz‖ = Real.exp (green_function c z) := by
  set N := basinEscapeTime c z hz with hN
  set w := (MLC.quadratic_map c)^[N] z with hw
  have hspec : ‖w‖ > ‖c‖ + 2 := basinEscapeTime_spec c z hz
  have hroot : (d.value z hz) ^ (2 ^ N) = MLC.logSeriesBottcherApprox c w :=
    d.compatible_with_every_escape_time z hz N hspec
  have hLpos : (0 : ℝ) < ‖MLC.logSeriesBottcherApprox c w‖ := by
    have := MLC.one_lt_norm_logSeriesBottcherApprox_of_outside_open c hspec
    linarith
  have hnorm : ‖d.value z hz‖ ^ (2 ^ N) = ‖MLC.logSeriesBottcherApprox c w‖ := by
    rw [← norm_pow, hroot]
  have hgw : green_function c w = Real.log ‖MLC.logSeriesBottcherApprox c w‖ :=
    green_function_eq_log_norm_logSeries_of_outside_open c hspec
  have hLexp : ‖MLC.logSeriesBottcherApprox c w‖ = Real.exp (green_function c w) := by
    rw [hgw, Real.exp_log hLpos]
  have horbit : green_function c w = (2:ℝ) ^ N * green_function c z := by
    simpa [hw] using green_function_orbit_eq_local c z N
  have hpow : ‖d.value z hz‖ ^ (2 ^ N)
      = (Real.exp (green_function c z)) ^ (2 ^ N) := by
    rw [hnorm, hLexp, horbit, ← Real.exp_nat_mul]
    congr 1
    push_cast; ring
  have h2 : (2 ^ N : ℕ) ≠ 0 := pow_ne_zero N (by norm_num)
  calc ‖d.value z hz‖
      = (‖d.value z hz‖ ^ (2 ^ N)) ^ (((2 ^ N : ℕ) : ℝ)⁻¹) :=
        (Real.pow_rpow_inv_natCast (norm_nonneg _) h2).symm
    _ = ((Real.exp (green_function c z)) ^ (2 ^ N)) ^ (((2 ^ N : ℕ) : ℝ)⁻¹) := by rw [hpow]
    _ = Real.exp (green_function c z) :=
        Real.pow_rpow_inv_natCast (Real.exp_pos _).le h2
```

## Step 2 — The coherent basin coordinate (total function) and its basic identities

```lean
noncomputable def coherentBasinCoordinate {c : ℂ}
    (d : EscapeTimeIndependentPullbackDataFor c) (z : ℂ) : ℂ := by
  classical
  exact if hz : z ∈ basin_of_infinity c then d.value z hz else 0

theorem coherentBasinCoordinate_on_basin {c : ℂ}
    (d : EscapeTimeIndependentPullbackDataFor c) (z : ℂ)
    (hz : z ∈ basin_of_infinity c) :
    coherentBasinCoordinate d z = d.value z hz := by
  simp [coherentBasinCoordinate, hz]

theorem coherentBasinCoordinate_extends_near {c : ℂ}
    (d : EscapeTimeIndependentPullbackDataFor c) (z : ℂ) (hz : ‖z‖ > ‖c‖ + 2) :
    coherentBasinCoordinate d z = MLC.logSeriesBottcherApprox c z := by
  have hbasin : z ∈ basin_of_infinity c :=
    outside_disk_subset_quadratic_basin c (outside_open_subset_outside_disk c hz)
  rw [coherentBasinCoordinate_on_basin d z hbasin]
  exact d.agrees_near_infinity z hbasin hz

theorem coherentBasinCoordinate_modulus {c : ℂ}
    (d : EscapeTimeIndependentPullbackDataFor c) (z : ℂ)
    (hz : z ∈ basin_of_infinity c) :
    ‖coherentBasinCoordinate d z‖ = Real.exp (green_function c z) := by
  rw [coherentBasinCoordinate_on_basin d z hz]
  exact escapeTimeIndependent_value_modulus c d z hz
```

## Step 3 — Reduce the genuine coordinate data to `conj` + `holo`

```lean
/-- The genuine Böttcher coordinate-data target for the coherent basin
coordinate reduces to exactly two explicit analytic facts about the
escape-time-independent value: functional-equation `conj` and holomorphicity
`holo`. The remaining five conjuncts (norm, basin characterization, modulus,
continuity, normalization at infinity) are automatic. -/
theorem genuineBottcherCoordinateData_of_escapeTimeIndependent_of_conj_of_holo
    {c : ℂ} (d : EscapeTimeIndependentPullbackDataFor c)
    (hconj : ∀ z : ℂ, z ∈ basin_of_infinity c →
      coherentBasinCoordinate d (MLC.quadratic_map c z)
        = (coherentBasinCoordinate d z) ^ 2)
    (hholo : DifferentiableOn ℂ (coherentBasinCoordinate d)
      (basin_of_infinity c)) :
    GenuineBottcherCoordinateDataFor c (coherentBasinCoordinate d) := by
  refine ⟨?_, ?_, hconj, ?_, hholo, ?_, ?_⟩
  · intro z hz
    rw [coherentBasinCoordinate_modulus d z hz]
    exact Real.one_lt_exp_iff.mpr (green_function_pos_of_basin c z hz)
  · intro z hz
    by_contra hnb
    rw [coherentBasinCoordinate, dif_neg hnb, norm_zero] at hz
    linarith
  · intro z hz
    exact coherentBasinCoordinate_modulus d z hz
  · intro z hz _
    exact (hholo.differentiableAt
      ((basin_of_infinity_isOpen c).mem_nhds hz)).continuousAt
  · refine (Filter.tendsto_congr' ?_).2 (MLC.tendsto_logSeriesBottcherApprox_div_atInfinity c)
    filter_upwards [eventually_atInfinity_norm_gt (‖c‖ + 2)] with z hz
    rw [coherentBasinCoordinate_extends_near d z hz]
```

## Step 4 — Build and validate

- `lake build`; confirm success and **no** new `sorry`/`axiom`.
- Run the axiom check (`lake env lean check_axioms.lean`) and confirm the
  frontier is still exactly the two project axioms.

## Step 5 — Report

In the RESULT file, state clearly:
- the coherent coordinate is now defined and the genuine coordinate-data target
  is reduced to exactly `conj_on_basin` + `holo_on_basin` of the coherent value;
- these two are the honest residual analytic seam;
- note the natural next reductions (for a FUTURE task, do NOT attempt here):
  (a) `conj_on_basin` should follow from `holo` + agreement near infinity by the
  identity theorem on the connected basin (needs an `IsPreconnected
  (basin_of_infinity c)` lemma — report whether one exists in-repo);
  (b) `holo_on_basin` is the genuine deep content, to be supplied via the
  monodromy-coherence machinery (`MonodromyTrivialPullbackDataFor` +
  local-branch gluing), reducing ultimately to simple-connectivity of the basin
  for `c ∈ M`.

## Constraints

- Do NOT introduce `sorry`/`axiom`.
- Do NOT edit `ConstructiveBasinCoordinate.lean`; do NOT touch
  `basinLogSeriesExtensionCandidate`.
- Do NOT attempt to prove `basinLogSeriesExtensionCandidate` holomorphic.
- Do NOT close `conj`/`holo` with stubs or property-bundle adapters; leaving them
  as the two explicit arguments of the constructor is the intended honest state.
- Do NOT commit.
- Stop once the build is green and the report is written.

## Deliverable

`plan/GPT54_RESULT_33_BUILD_COHERENT_COORDINATE_AND_REDUCE_GENUINE_ROUTE.md`
