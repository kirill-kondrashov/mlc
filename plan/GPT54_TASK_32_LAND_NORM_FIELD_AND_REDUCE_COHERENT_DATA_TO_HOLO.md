# TASK 32 — Land the `basin_of_norm_gt_one` field and reduce the whole
# `PrincipalPullbackCoherentDataFor` target to the single `holo_on_basin` hypothesis

## Global context (why this task)

`mlc_conjecture` currently rests on exactly two axioms (`check_axioms.lean`):
`MLC.green_sublevel_translate_inter_mandelbrot_connected_straddling` and
`MLC.residualOpenVirtualNearMoleculeAxiom`. The Böttcher route to discharging the
straddling axiom flows through
`Quadratic.PrincipalPullbackCoherentDataFor c` (7 fields, defined in
`Mlc/Quadratic/Complex/Bottcher/ConstructiveBasinCoordinate.lean` ~line 2730),
which feeds `GenuineBottcherLocalParameterFamilyData` in
`Mlc/.../Bottcher/BottcherMotion.lean` and the closure theorems in
`Mlc/MainConjecture.lean` (`mlc_conjecture_of_principalPullbackCoherentData_two`).

After iteration 31, five of the seven fields are honestly proven in
`Mlc/Quadratic/Complex/Bottcher/ConstructiveBasinModulus.lean`
(`extends_near`, `norm_on_basin`, `conj_on_basin`, `modulus_on_basin`,
`tendsto_div_atInfinity`). Two fields remain:

- `basin_of_norm_gt_one` — a totality-convention issue, **fully solvable now**.
- `holo_on_basin` — the genuine analytic seam.

This task lands `basin_of_norm_gt_one` and, critically, adds a constructor that
reduces the ENTIRE 7-field target to the single `holo_on_basin` hypothesis, so
the coherent-data goal for the straddling-axiom route becomes exactly one named
holomorphicity lemma. **All scripts below are planner-verified to compile.**

## IMPORTANT — do NOT chase the bandwise-`cpow` route for `holo_on_basin`

Your Result 31 proposed proving `holo_on_basin` by defining escape-time bands and
applying `DifferentiableOn.cpow_const` bandwise (your step 3: "stays in a
principal-log compatible sector / slit-plane neighborhood on the band"). **That
step is provably impossible for the current candidate**, so do not spend effort
on it:

- Every Mathlib `cpow_const` differentiability lemma
  (`DifferentiableAt.cpow_const`, `DifferentiableWithinAt.cpow_const`,
  `DifferentiableOn.cpow_const`, `HasDerivAt.cpow_const`, all in
  `Mathlib/Analysis/SpecialFunctions/Pow/Deriv.lean`) requires the base
  `∈ Complex.slitPlane`, i.e. the base must avoid `ℝ≤0`.
- On each band N≥1 the base is `logSeriesBottcherApprox c ((quadratic_map c)^[N] z)`.
  Since `logSeriesBottcherApprox c w / w → 1` as `w → ∞`, the map `L := logSeriesBottcherApprox c`
  takes values of every argument on the exterior — in particular it hits `ℝ<0`.
  So the base genuinely leaves `slitPlane`, the principal `cpow` picks up a
  `exp(2πi / 2^N)` jump across `{L∘f^N ∈ ℝ<0}`, and
  `basinLogSeriesExtensionCandidate` has real jump discontinuities inside the
  basin. Because `basin_of_infinity c` is open, `DifferentiableOn` requires
  pointwise differentiability at each such point, which fails.

Conclusion: `holo_on_basin` is **not attainable for the principal-pullback
`def` as written**. A genuinely holomorphic coordinate needs the
branch-coherent / monodromy-trivial construction already scaffolded in the repo
(`EscapeTimeIndependentPullbackDataFor`, `MonodromyTrivialPullbackDataFor`,
`PullbackRootMonodromyRepresentation`), whose single-valuedness reduces to
simple-connectivity of the basin (Douady–Hubbard depth). Do NOT stub, axiomatize,
or fake this field. Leave it as an explicit hypothesis (Step 3 below).

## Step 1 — Revise the off-basin totality branch of the candidate

In `Mlc/Quadratic/Complex/Bottcher/ConstructiveBasinCoordinate.lean`, the def
(~line 2634) currently reads:

```lean
noncomputable def basinLogSeriesExtensionCandidate (c z : ℂ) : ℂ :=
  by
    classical
    exact
      if hz : z ∈ basin_of_infinity c then
        principalPullbackLogSeriesBottcher c z hz
      else
        MLC.logSeriesBottcherApprox c z
```

Change the off-basin branch from `MLC.logSeriesBottcherApprox c z` to `0`:

```lean
      else
        0
```

Rationale: the field `basin_of_norm_gt_one` requires
`1 < ‖candidate z‖ → z ∈ basin`. With the old off-basin branch the norm is not
bounded, so the implication is false; with `0` the contrapositive is trivial.
This branch is only ever evaluated off-basin, so the five landed on-basin
theorems and `extends_near` (which use the `dif_pos` branch) are unaffected.
**Planner-verified**: after this change, `lake build` of the module stays green
(7890 jobs) — no landed proof breaks.

## Step 2 — Land `basin_of_norm_gt_one` (verified script)

Add to `Mlc/Quadratic/Complex/Bottcher/ConstructiveBasinModulus.lean` (inside its
`namespace MLC.Quadratic`, so `basin_of_infinity` resolves unqualified):

```lean
theorem basinLogSeriesExtensionCandidate_basin_of_norm_gt_one (c : ℂ) :
    ∀ z : ℂ, 1 < ‖basinLogSeriesExtensionCandidate c z‖ →
      z ∈ basin_of_infinity c := by
  intro z hz
  by_contra hnb
  rw [basinLogSeriesExtensionCandidate, dif_neg hnb, norm_zero] at hz
  linarith
```

## Step 3 — Reduce the entire coherent-data target to `holo_on_basin` (verified script)

Add, after Step 2's theorem in the same file:

```lean
/-- The principal-pullback coherent-data target reduces to a single explicit
analytic hypothesis: given only holomorphicity of the candidate on the basin,
all seven `PrincipalPullbackCoherentDataFor` fields are discharged. The six
non-holo fields are proven in-repo; `holo_on_basin` is the sole remaining
analytic seam (branch-coherent / monodromy-trivial construction). -/
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

Note the exponent field `extends_near` in the structure quantifies over
`‖z‖ > ‖c‖ + 2`; `basinLogSeriesExtensionCandidate_extends_near` has exactly that
signature. **Planner-verified**: this whole `where`-block elaborates once Step 1
+ Step 2 are in place.

## Step 4 — Build and validate

- `lake build` the whole project. Confirm it succeeds with no new
  `sorry`/`axiom`.
- Run the axiom check (`lake env lean check_axioms.lean` or the project's
  standard command) and confirm the frontier is still exactly the two expected
  axioms — **no new axiom** may appear.

## Step 5 — Report (honest investigation, NOT a fake proof)

In the RESULT file, include a short, precise section on `holo_on_basin`:
- restate the slit-plane obstruction above (base leaves `slitPlane`, jump of
  `exp(2πi/2^N)`), i.e. why the principal candidate is genuinely non-holomorphic;
- identify the genuine route: the monodromy-coherent construction
  (`EscapeTimeIndependentPullbackDataFor` / `MonodromyTrivialPullbackDataFor` /
  `PullbackRootMonodromyRepresentation`) and its reduction to simple-connectivity
  of `basin_of_infinity c` (for `c ∈ M`, i.e. `K(c)` connected);
- report which of those scaffolding structures already exist in-repo and what a
  minimal next lemma toward single-valued holomorphicity would be. Do not attempt
  to prove it in this task.

## Constraints

- Do NOT introduce `sorry` or `axiom`.
- Do NOT stub `holo_on_basin` or bundle it away with a hypothesis-taking adapter;
  leaving it as the explicit argument of `principalPullbackCoherentData_of_holo`
  is the intended, honest treatment.
- Do NOT chase the bandwise-`cpow` route (Step "IMPORTANT" above).
- Do NOT commit.
- Stop once the build is green and the report is written.

## Deliverable

Write `plan/GPT54_RESULT_32_LAND_NORM_FIELD_AND_REDUCE_COHERENT_DATA_TO_HOLO.md`
covering: the def revision, the two new theorems, the full build result, the
axiom-frontier check, and the honest `holo_on_basin` investigation section.
