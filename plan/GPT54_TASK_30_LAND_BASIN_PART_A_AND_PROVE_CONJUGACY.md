# GPT-5.4 Worker Task 30: Land basin Part A + prove conjugacy; pin holomorphicity

**Repository:** `/home/kir/pers/mlc`
**Mode:** IMPLEMENTATION. Edit Lean sources, build, and axiom-check. Commit is
still **not** required and must not be done unless explicitly asked — leave the
working tree with the new code and a green build.
**Result file:** `plan/GPT54_RESULT_30_LAND_BASIN_PART_A_AND_PROVE_CONJUGACY.md`

## Mode change

Tasks 27–29 were read-only audits to pin the frontier. The frontier is now
pinned, so this is an implementation task. You **may and must** edit
`Mlc/Quadratic/Complex/Bottcher/ConstructiveBasinCoordinate.lean` (and only that
file unless a genuine dependency forces otherwise — if so, justify it). Run
`lake build` on the affected target and confirm no new `sorry`/`axiom`.

Do not edit unrelated plan artifacts. Do not commit. `polar_green_map` and
`proxy_bottcher_map` remain excluded as coordinate providers.

## Global objective (unchanged)

`MLC.mlc_conjecture` rests on exactly two frontier axioms; this program discharges
`green_sublevel_translate_inter_mandelbrot_connected_straddling` via the Böttcher
route. Downstream consumer: `GenuineBottcherLocalParameterFamilyData c₀`
(`BottcherMotion.lean`). This task advances discharge item 1 (the full-basin
monodromy-coherent coordinate) by populating
`MLC.Quadratic.PrincipalPullbackCoherentDataFor c` for **arbitrary** `c`, with no
bundle-to-bundle shortcut.

## Corrected baseline: Part A is proved

Contrary to Result 29, all of Part A compiles as-is (verified with
`lake env lean`). Land these four theorems verbatim in
`ConstructiveBasinCoordinate.lean` (they sit naturally right after
`basinLogSeriesExtensionCandidate_norm_on_basin_of_principalPullback_modulus`,
~line 2665; adjust `open`/namespace — inside `namespace MLC.Quadratic` the names
`basin_of_infinity`, `principalPullbackLogSeriesBottcher`, etc. are unqualified).

```lean
theorem principalPullbackLogSeriesBottcher_modulus_on_basin
    (c z : ℂ) (hz : z ∈ basin_of_infinity c) :
    ‖principalPullbackLogSeriesBottcher c z hz‖ = Real.exp (green_function c z) := by
  set N := basinEscapeTime c z hz with hN
  set w := (MLC.quadratic_map c)^[N] z with hw
  have hwout : ‖w‖ > ‖c‖ + 2 := basinEscapeTime_spec c z hz
  have hnorm := principalPullbackLogSeriesBottcher_norm_eq_rpow_iterateValue c z hz
  simp only at hnorm
  have hlog : green_function c w = Real.log ‖MLC.logSeriesBottcherApprox c w‖ :=
    green_function_eq_log_norm_logSeries_of_outside_open c hwout
  have horbit : green_function c w = (2:ℝ)^N * green_function c z := by
    simpa [hw] using green_function_orbit_eq_local c z N
  have hφpos : 0 < ‖MLC.logSeriesBottcherApprox c w‖ := by
    have := MLC.one_lt_norm_logSeriesBottcherApprox_of_outside_open c hwout
    linarith
  rw [hnorm]
  have hexp : ‖MLC.logSeriesBottcherApprox c w‖ = Real.exp (green_function c w) := by
    rw [hlog, Real.exp_log hφpos]
  rw [hexp, horbit, ← Real.exp_mul]
  have h2 : ((2:ℝ)^N) ≠ 0 := by positivity
  congr 1
  field_simp
  ring

theorem basinLogSeriesExtensionCandidate_modulus_on_basin
    (c z : ℂ) (hz : z ∈ basin_of_infinity c) :
    ‖basinLogSeriesExtensionCandidate c z‖ = Real.exp (green_function c z) := by
  classical
  rw [basinLogSeriesExtensionCandidate]
  simp only [hz, dif_pos]
  exact principalPullbackLogSeriesBottcher_modulus_on_basin c z hz

theorem basinLogSeriesExtensionCandidate_norm_gt_one_on_basin
    (c z : ℂ) (hz : z ∈ basin_of_infinity c) :
    1 < ‖basinLogSeriesExtensionCandidate c z‖ :=
  basinLogSeriesExtensionCandidate_norm_on_basin_of_principalPullback_modulus
    (fun z hz => principalPullbackLogSeriesBottcher_modulus_on_basin c z hz) z hz

theorem basinLogSeriesExtensionCandidate_tendsto_div_atInfinity (c : ℂ) :
    Tendsto (fun z => basinLogSeriesExtensionCandidate c z / z) atInfinity (𝓝 (1 : ℂ)) := by
  refine (Filter.tendsto_congr' ?_).2 (MLC.tendsto_logSeriesBottcherApprox_div_atInfinity c)
  filter_upwards [eventually_atInfinity_norm_gt (‖c‖ + 2)] with z hz
  rw [basinLogSeriesExtensionCandidate_extends_near c z hz]
```

These discharge the coherent-data fields `modulus_on_basin`, `norm_on_basin`
(with `green_function_pos_of_basin`), `tendsto_div_atInfinity`; `extends_near` is
already `basinLogSeriesExtensionCandidate_extends_near`.

## Part B: prove `conj_on_basin` (this is NOT the monodromy problem)

`conj_on_basin` for `basinLogSeriesExtensionCandidate` reduces to escape-time
bookkeeping plus a trivial `cpow` identity — no branch/monodromy theory:

1. **Escape-time recursion.** Prove, for `z ∈ basin_of_infinity c` with
   `N := basinEscapeTime c z hz`:
   - if `N ≥ 1`, then `basinEscapeTime c (quadratic_map c z) hfz = N - 1` and
     `(quadratic_map c)^[N-1] (quadratic_map c z) = (quadratic_map c)^[N] z`;
   - if `N = 0` (so `‖z‖ > ‖c‖ + 2`), then `‖quadratic_map c z‖ > ‖c‖ + 2` (use
     the outside-region forward invariance already used via
     `quadratic_basin_forward_invariant` / `escaping_set_contains_large_ball`;
     for the strict `> ‖c‖+2` bound use `‖z²+c‖ ≥ ‖z‖² − ‖c‖ > ‖z‖`), giving
     `basinEscapeTime c (quadratic_map c z) hfz = 0`.
   This is `Nat.find` reasoning against `exists_iterate_mem_outside_open_of_mem_basin`.
2. **`cpow` squaring.** For `x ≠ 0` and `w : ℂ`, `(x ^ w) ^ 2 = x ^ (2 * w)`
   (`Complex.cpow` is `exp (log x * w)`; squaring doubles the exponent). Hence
   `(L(fᴺ z) ^ ((2^N)⁻¹)) ^ 2 = L(fᴺ z) ^ ((2^(N-1))⁻¹)` for `N ≥ 1`.
3. Combine (1)+(2) for `N ≥ 1`; for `N = 0` use the exterior functional equation
   `logSeriesBottcherApprox_conj_of_large_radius`. Conclude
   `basinLogSeriesExtensionCandidate c (quadratic_map c z) =
    (basinLogSeriesExtensionCandidate c z)^2` on the basin.

Prove this as a genuine theorem. Do **not** discharge it by an adapter between
property-bundle structures.

## Part C: the genuine crux — `holo_on_basin` and `basin_of_norm_gt_one`

1. **`holo_on_basin`** (`DifferentiableOn ℂ (basinLogSeriesExtensionCandidate c)
   (basin_of_infinity c)`). On each open level band `{z | basinEscapeTime c z = N}`
   the candidate is `(L ∘ fᴺ) ^ ((2^N)⁻¹)`, holomorphic **except** where the
   principal `cpow` branch cut of `L(fᴺ z)` is crossed (`L(fᴺ z) ∈ ℝ≤0`). Analyze
   precisely:
   - is `basinEscapeTime` locally constant on the open basin (band interiors
     open)? Prove or identify the gap.
   - does `L(fᴺ z)` avoid the principal branch cut on each band, or must
     differentiability be obtained band-by-band and glued via `conj_on_basin` and
     an identity/uniqueness argument across seams?
   Either prove `holo_on_basin`, or state the exact minimal missing lemma
   (verbatim Lean statement) and the sharpest proof strategy. Do not fake it with
   a hypothesis field.
2. **`basin_of_norm_gt_one`** (`1 < ‖candidate‖ → z ∈ basin_of_infinity c`).
   Off the basin the candidate is the near-infinity formula by the totality
   convention; determine whether `1 < ‖candidate‖ → z ∈ basin` actually holds for
   the current `def` or needs the off-basin branch reconsidered. Report precisely.

## Part D: assemble and verify

- If Parts A–C all close, construct
  `MLC.Quadratic.PrincipalPullbackCoherentDataFor c` (for arbitrary `c`) directly
  from the proved theorems (no `X.toY` bundle shortcut) and land it.
- Run `lake build` on the target; paste the tail of the successful output.
- Confirm no new `sorry`/`axiom` were introduced (grep the file; optionally run a
  `#print axioms` probe on the new coherent-data term).

## Decision

Choose exactly one and state the next discharge item unblocked
(`Φ_c⁻¹` inverse / puzzle-boundary motion / parameter↔dynamical correspondence):

1. `PrincipalPullbackCoherentDataFor c` fully landed for arbitrary `c`, build green;
2. Parts A+B landed; `holo_on_basin` reduced to one named lemma (state it), build green;
3. Parts A+B landed; `holo_on_basin` is a genuine open analytic seam — exact
   statement + strategy given, build green with the open fields clearly isolated
   (no `sorry`);
4. an obstruction blocked Part A or B (identify exactly).

Give the exact next worker task but do not create its file.

## Report contract

Include: the exact source diffs/decls added; `lake build` result; the escape-time
recursion and `cpow` lemmas as proved; the precise status of `holo_on_basin` and
`basin_of_norm_gt_one`; confirmation of no new `sorry`/`axiom`; and the mapping of
each landed field onto `GenuineBottcherLocalParameterFamilyData`.
