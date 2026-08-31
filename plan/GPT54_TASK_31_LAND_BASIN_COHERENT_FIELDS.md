# GPT-5.4 Worker Task 31: Land basin Part A + conjugacy in a non-cyclic file; pin holomorphicity

**Repository:** `/home/kir/pers/mlc`
**Mode:** IMPLEMENTATION. Edit sources, build, axiom-check. Do not commit.
**Result file:** `plan/GPT54_RESULT_31_LAND_BASIN_COHERENT_FIELDS.md`

## Correction to Task 30 (placement error, now fixed)

Task 30 told you to put the Part A proofs *inside*
`ConstructiveBasinCoordinate.lean`. That was wrong: the proofs use
`green_function_eq_log_norm_logSeries_of_outside_open`, which lives in
`GreenHarmonic.lean`, and `GreenHarmonic.lean` imports
`ConstructiveBasinCoordinate.lean` — so they must live **downstream** of
`GreenHarmonic`, not inside it. Your import-cycle finding was correct.

The resolution is placement, not new mathematics. **All seven theorems below
compile cleanly** when placed in a file that imports `GreenHarmonic` (verified
with `lake env lean`). Your Result 30 claim that the Part A proof "is false in
the current dependency graph" is wrong — it is true in the correct file.

Also: your Result 30 landed **hypothesis-taking wrapper stubs** for the four
Part A names in `ConstructiveBasinCoordinate.lean`. Those are exactly the
property-bundle anti-pattern the tasks forbid. **Remove them** (see Step 1).

## Step 1 — remove the wrapper stubs

Delete the four declarations you added to
`ConstructiveBasinCoordinate.lean` in Task 30:

- `principalPullbackLogSeriesBottcher_modulus_on_basin`
- `basinLogSeriesExtensionCandidate_modulus_on_basin`
- `basinLogSeriesExtensionCandidate_norm_gt_one_on_basin`
- `basinLogSeriesExtensionCandidate_tendsto_div_atInfinity`

Keep the pre-existing reduction lemma
`basinLogSeriesExtensionCandidate_norm_on_basin_of_principalPullback_modulus`
(it is used below). Rebuild to confirm the file is green after deletion.

## Step 2 — create the new downstream file

Create `Mlc/Quadratic/Complex/Bottcher/ConstructiveBasinModulus.lean` and
register it in `Mlc.lean` (add
`import Mlc.Quadratic.Complex.Bottcher.ConstructiveBasinModulus`, e.g. right
after the `GreenHarmonic` import line).

Paste the following **verified** content verbatim (it compiled clean, no
`sorry`/`axiom`, no warnings). These discharge five of the seven
`PrincipalPullbackCoherentDataFor` fields (`modulus_on_basin`, `norm_on_basin`,
`tendsto_div_atInfinity`, `conj_on_basin`; `extends_near` is the pre-existing
`basinLogSeriesExtensionCandidate_extends_near`).

```lean
import Mlc.Quadratic.Complex.GreenHarmonic

open MLC MLC.Quadratic Complex Filter Topology

namespace MLC.Quadratic

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

theorem basinEscapeTime_map_of_pos
    (c z : ℂ) (hz : z ∈ basin_of_infinity c)
    (hfz : MLC.quadratic_map c z ∈ basin_of_infinity c)
    (hN : basinEscapeTime c z hz ≠ 0) :
    basinEscapeTime c (MLC.quadratic_map c z) hfz = basinEscapeTime c z hz - 1 := by
  set N := basinEscapeTime c z hz with hNdef
  have hspecP : ‖(MLC.quadratic_map c)^[N] z‖ > ‖c‖ + 2 := basinEscapeTime_spec c z hz
  have hminP : ∀ m < N, ¬ (‖(MLC.quadratic_map c)^[m] z‖ > ‖c‖ + 2) := by
    intro m hm; exact Nat.find_min _ hm
  rw [basinEscapeTime, Nat.find_eq_iff]
  refine ⟨?_, ?_⟩
  · have h : (MLC.quadratic_map c)^[N - 1] (MLC.quadratic_map c z)
        = (MLC.quadratic_map c)^[N] z := by
      rw [← Function.iterate_succ_apply]; congr 1; omega
    rw [h]; exact hspecP
  · intro k hk
    have hstep : (MLC.quadratic_map c)^[k] (MLC.quadratic_map c z)
        = (MLC.quadratic_map c)^[k+1] z := by
      rw [← Function.iterate_succ_apply]
    rw [hstep]; exact hminP (k+1) (by omega)

theorem cpow_two_eq (x w : ℂ) (hx : x ≠ 0) : (x ^ w) ^ (2:ℕ) = x ^ ((2:ℂ) * w) := by
  rw [pow_two, ← Complex.cpow_add _ _ hx]; ring_nf

theorem basinLogSeriesExtensionCandidate_conj_on_basin
    (c z : ℂ) (hz : z ∈ basin_of_infinity c) :
    basinLogSeriesExtensionCandidate c (MLC.quadratic_map c z)
      = (basinLogSeriesExtensionCandidate c z) ^ 2 := by
  have hfz : MLC.quadratic_map c z ∈ basin_of_infinity c :=
    basin_of_infinity_forward_invariant c hz
  classical
  rw [basinLogSeriesExtensionCandidate]; simp only [hfz, dif_pos]
  rw [basinLogSeriesExtensionCandidate]; simp only [hz, dif_pos]
  rw [principalPullbackLogSeriesBottcher, principalPullbackLogSeriesBottcher]
  by_cases hN0 : basinEscapeTime c z hz = 0
  · have hzout : ‖z‖ > ‖c‖ + 2 := by
      have := basinEscapeTime_spec c z hz; rw [hN0] at this; simpa using this
    have hfzout : ‖MLC.quadratic_map c z‖ > ‖c‖ + 2 := quadratic_map_maps_outside_open c hzout
    have hM0 : basinEscapeTime c (MLC.quadratic_map c z) hfz = 0 := by
      rw [basinEscapeTime, Nat.find_eq_iff]
      exact ⟨by simpa using hfzout, by intro k hk; omega⟩
    rw [hN0, hM0]
    simp only [Function.iterate_zero, id_eq, pow_zero, inv_one, Complex.cpow_one]
    exact logSeriesBottcherApprox_conj_of_large_radius c (le_refl _) hzout
  · set N := basinEscapeTime c z hz with hNdef
    have hM : basinEscapeTime c (MLC.quadratic_map c z) hfz = N - 1 :=
      basinEscapeTime_map_of_pos c z hz hfz hN0
    rw [hM]
    have hiter : (MLC.quadratic_map c)^[N - 1] (MLC.quadratic_map c z)
        = (MLC.quadratic_map c)^[N] z := by
      rw [← Function.iterate_succ_apply]; congr 1; omega
    rw [hiter]
    have hxne : MLC.logSeriesBottcherApprox c ((MLC.quadratic_map c)^[N] z) ≠ 0 := by
      have := principalPullbackLogSeriesBottcher_iterate_ne_zero c z hz
      rwa [← hNdef] at this
    rw [cpow_two_eq _ _ hxne]
    congr 1
    have h2 : ((2:ℂ)) ^ N = 2 * (2:ℂ) ^ (N - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [h2]
    have hne : ((2:ℂ) ^ (N-1)) ≠ 0 := pow_ne_zero _ (by norm_num)
    field_simp

end MLC.Quadratic
```

If any line fails, it means a name drifted since verification — fix the name, do
**not** weaken a statement or add a hypothesis. Run
`lake env lean Mlc/Quadratic/Complex/Bottcher/ConstructiveBasinModulus.lean`.

## Step 3 — the two genuinely open fields

Work in the new file.

1. **`basin_of_norm_gt_one`** (`1 < ‖candidate‖ → z ∈ basin`). This is likely
   **false for the current `def`**: off the basin,
   `basinLogSeriesExtensionCandidate` equals `logSeriesBottcherApprox c z`, whose
   norm is not bounded by `1` on `K(c)`. Resolve it honestly by one of:
   - revise the off-basin totality branch of `basinLogSeriesExtensionCandidate`
     (in `ConstructiveBasinCoordinate.lean`) to a value with norm `≤ 1`
     (e.g. `0`), then prove the field; **or**
   - prove `‖logSeriesBottcherApprox c z‖ ≤ 1` for `z ∉ basin` if that actually
     holds; **or**
   - report precisely why neither works.
   If you revise the `def`, rebuild the whole library and confirm no downstream
   breakage (the on-basin branch and `extends_near` must be unaffected).
2. **`holo_on_basin`** (`DifferentiableOn ℂ (basinLogSeriesExtensionCandidate c)
   (basin_of_infinity c)`). This is the real analytic crux. On each open
   escape-time band the candidate is `(L ∘ fᴺ) ^ ((2^N)⁻¹)` — holomorphic except
   across the principal-`cpow` branch cut of `L(fᴺ z)`. Either prove it, or state
   the exact minimal missing lemma (verbatim Lean statement) and the sharpest
   strategy. Do not fake it with a hypothesis field or a bundle adapter.

## Step 4 — assemble and verify

- If both open fields close: construct
  `MLC.Quadratic.PrincipalPullbackCoherentDataFor c` for arbitrary `c` directly
  from the proved theorems (no `X.toY` bundle shortcut) in the new file.
- If only `holo_on_basin` remains: land the six proved fields and isolate
  `holo_on_basin` as one named lemma statement (no `sorry`).
- Run `lake build`; paste the tail. Confirm no new `sorry`/`axiom`
  (grep + optionally `#print axioms` on the coherent-data term).

## Decision

Choose one and name the next discharge item unblocked
(`Φ_c⁻¹` / puzzle-boundary motion / parameter↔dynamical correspondence):

1. full `PrincipalPullbackCoherentDataFor c` landed, build green;
2. six fields landed, `holo_on_basin` reduced to one named lemma, build green;
3. six fields landed, `holo_on_basin` a genuine open seam (exact statement +
   strategy), build green with no `sorry`;
4. an obstruction blocked Steps 1–2 (identify exactly).

Give the exact next worker task but do not create its file.

## Report contract

Include: confirmation the wrapper stubs were removed; the new file registered in
`Mlc.lean`; `lake build` tail; the exact status of `basin_of_norm_gt_one`
(including any `def` revision and downstream-breakage check) and `holo_on_basin`;
no new `sorry`/`axiom`; and the field-to-`GenuineBottcherLocalParameterFamilyData`
mapping.
