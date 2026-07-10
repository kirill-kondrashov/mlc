# GPT-5.4 Worker Task 29: Discharge the basin modulus/norm facts and pin the branch-coherence seam

**Repository:** `/home/kir/pers/mlc`
**Mode:** read-only audit plus `/tmp` Lean proofs; no source edits, no commit
**Result file:** `plan/GPT54_RESULT_29_DISCHARGE_BASIN_MODULUS_AND_PIN_BRANCH_COHERENCE.md`

## Safety and hard exclusion

Write only the result report, via atomic rename. Do not edit Lean sources,
dependencies, plans, or prior artifacts; do not commit. Prove everything in
`/tmp` probes with `lake env lean`.

`polar_green_map` and `proxy_bottcher_map` remain excluded as coordinate
providers. Their norm identities may be reused only as Green-radius facts. Stay
on the genuine `logSeriesBottcherApprox` / `principalPullbackLogSeriesBottcher`
route. Do not return to renormalization, tubes, frozen Green pieces, or abstract
connectivity packages.

## Global objective (keep this in view)

`MLC.mlc_conjecture` is proved modulo **exactly two** frontier axioms
(`check_axioms.lean`):

- `MLC.green_sublevel_translate_inter_mandelbrot_connected_straddling`
- `MLC.residualOpenVirtualNearMoleculeAxiom`

The full theorem `green_sublevel_translate_inter_mandelbrot_connected` is already
*derived*, not axiomatized: the subset/superset strata are discharged
unconditionally, and only the **straddling** stratum still invokes the axiom
above (see `Mlc/ParaPuzzleConnectivity.lean`). This whole Böttcher program exists
to discharge that one straddling axiom via **route (C)**: parametrize the moving
equipotential boundaries by `z = Φ_c⁻¹(ω)` and get residual continuity for free
through the λ-lemma (`LambdaLemma.isConnected_image_of_differentiableOn`).

The **actual downstream consumer** on that route is the *parameter* family
`MLC.Quadratic.GenuineBottcherLocalParameterFamilyData c₀` in
`Mlc/Quadratic/Complex/Bottcher/BottcherMotion.lean`. Its fields are exactly the
single-fiber `PrincipalPullbackCoherentDataFor` facts, but required uniformly for
all `c ∈ ball c₀ r`, plus three extra clauses: `param_holo`,
`continuous_on_basin_ne_zero`, and `puzzle_boundary_eq_equipotential`.

The four remaining pieces for a full straddling-axiom discharge (per the axiom's
own docstring) are, in order:

1. a full-basin monodromy-coherent coordinate (**this task's focus**);
2. the holomorphic inverse `Φ_c⁻¹`;
3. a nontrivial puzzle-boundary `HolomorphicMotion`;
4. the parameter↔dynamical correspondence.

This task advances item 1. Every lemma you prove must be stated so it lifts to
the parameter family: the modulus/norm/conjugacy/differentiability facts below
are already stated for an **arbitrary** `c : ℂ`, so prove them for arbitrary `c`
(do not specialize to `c = 2`), and note explicitly how each maps onto the
corresponding field of `GenuineBottcherLocalParameterFamilyData`.

## Context: correction to Result 28

Result 28 concluded Decision 2 (genuine near-infinity provider present, full
basin extension missing). That is broadly right, but it **under-reported** the
proved content. Contrary to Result 28, the basin modulus identity is **not** a
missing hypothesis. On the whole basin,

```
‖principalPullbackLogSeriesBottcher c z hz‖ = Real.exp (green_function c z)
```

is provable now, unconditionally, from existing lemmas:

- `MLC.Quadratic.principalPullbackLogSeriesBottcher_norm_eq_rpow_iterateValue`
  (`‖ppb‖ = ‖φ (fᴺ z)‖ ^ (1 / 2ᴺ)`, `N = basinEscapeTime c z hz`);
- `MLC.Quadratic.green_function_eq_log_norm_logSeries_of_outside_open`
  (`green c w = log ‖φ w‖` for `‖w‖ > ‖c‖ + 2`, applied at `w = fᴺ z` via
  `basinEscapeTime_spec`);
- `MLC.Quadratic.green_function_orbit_eq_local`
  (`green c (fᴺ z) = 2ᴺ · green c z`).

A ~20-line `/tmp` proof closes it (`Real.exp_log`, `Real.exp_mul`, `field_simp`,
`ring`). Your task begins from this corrected baseline.

## Target structure

The theorem-facing seam is
`MLC.Quadratic.PrincipalPullbackCoherentDataFor (c : ℂ)` in
`Mlc/Quadratic/Complex/Bottcher/ConstructiveBasinCoordinate.lean`, whose seven
fields are (over `basinLogSeriesExtensionCandidate c`, which on the basin equals
`principalPullbackLogSeriesBottcher`):

1. `extends_near`
2. `norm_on_basin`
3. `basin_of_norm_gt_one`
4. `conj_on_basin`
5. `holo_on_basin`
6. `modulus_on_basin`
7. `tendsto_div_atInfinity`

## A. Discharge the now-provable fields (mandatory, in `/tmp`)

Prove as genuine standalone theorems (statements verbatim over
`basinLogSeriesExtensionCandidate c`, or over `principalPullbackLogSeriesBottcher`
plus the on-basin equality), each compiled in a `/tmp` probe:

1. `modulus_on_basin` — `‖·‖ = exp (green_function c z)` on `basin_of_infinity c`
   (use the composition above; note
   `basinLogSeriesExtensionCandidate c z = principalPullbackLogSeriesBottcher c z hz`
   on the basin, by definition).
2. `norm_on_basin` — `1 < ‖·‖` on the basin (from field 1 and
   `green_function_pos_of_basin`; the lemma
   `basinLogSeriesExtensionCandidate_norm_on_basin_of_principalPullback_modulus`
   already reduces this to the modulus hypothesis you just discharged).
3. `extends_near` — already available as
   `basinLogSeriesExtensionCandidate_extends_near`; confirm it type-checks as the
   field.
4. `tendsto_div_atInfinity` — from `tendsto_logSeriesBottcherApprox_div_atInfinity`
   plus the near-infinity agreement; prove it or state the exact remaining gap.

Report, for each, the exact compiled statement and proof, or the precise reason
it does not yet close.

## B. Isolate the genuinely open fields

After Part A, the remaining open fields should be exactly:

- `conj_on_basin` (semiconjugacy `φ (f_c z) = (φ z)^2` on the whole basin);
- `holo_on_basin` (`DifferentiableOn ℂ φ (basin_of_infinity c)`);
- `basin_of_norm_gt_one` (converse characterization).

Confirm this by attempting each and reporting where it fails. Do **not** close
any open field by constructing a new adapter between property-bundle structures
(no `X.toY` whose target fields are the theorems, no supplying the conclusion as
a hypothesis). Only genuine analytic proofs count.

Then map each of the seven `PrincipalPullbackCoherentDataFor` fields onto the
corresponding field of the downstream consumer
`GenuineBottcherLocalParameterFamilyData c₀`
(`norm_on_basin`, `basin_of_norm_gt_one`, `conj_on_basin`, `modulus_on_basin`,
`fiber_holo_on_basin`, `tendsto_div_atInfinity`), and list the three consumer
fields that the single-fiber structure does **not** yet supply — `param_holo`,
`continuous_on_basin_ne_zero`, `puzzle_boundary_eq_equipotential` — noting for
each whether existing infrastructure (`logSeriesNearInfinityParameterFamily`,
`BottcherParamHolo`) already reaches it near infinity and what remains on the
full basin.

## C. Pin the branch-coherence crux

The core obstruction is that `basinEscapeTime c z hz` (a `Nat.find`) jumps
discretely across Green level sets, and `principalPullbackLogSeriesBottcher`
takes a principal `2ᴺ`-th root that depends on `N`. Analyze precisely:

1. **Escape-time independence.** State and, if possible, prove: for
   `z ∈ basin_of_infinity c` and any `M ≥ basinEscapeTime c z hz` with
   `‖fᴹ z‖ > ‖c‖ + 2`, the principal-root pullback at level `M` equals the value
   at level `N = basinEscapeTime`. Identify the exact branch-matching fact
   required (principal square root of `φ (f w)` equals `φ w` on the exterior),
   and whether the repository already proves it (search around
   `logSeriesBottcherApprox_conj_of_large_radius` /
   `..._conj_iterate_outside_open` and any `cpow`/`sqrt` branch lemmas).
2. **Semiconjugacy on the basin.** Reduce `conj_on_basin` to escape-time
   independence plus the exterior functional equation, or identify the exact
   missing branch lemma.
3. **Holomorphicity across level sets.** State precisely why
   `DifferentiableOn ℂ φ (basin_of_infinity c)` is or is not reducible to the
   local exterior differentiability
   (`logSeriesBottcherApprox_differentiableOn_large_radius`) transported by the
   analytic iterate `fᴺ`, and what continuity-across-`basinEscapeTime`-jumps
   theorem is required. Note that on each open level band `basinEscapeTime` is
   locally constant; the real content is agreement of adjacent bands, which is
   exactly the escape-time independence of Part C.1.

## D. Decision

Choose exactly one, and in each case state which of the four straddling-axiom
discharge items (basin coordinate / inverse `Φ_c⁻¹` / puzzle-boundary motion /
parameter↔dynamical correspondence) is unblocked next:

1. all seven fields are now provable (give the full `/tmp` construction of
   `PrincipalPullbackCoherentDataFor c` with no bundle-to-bundle shortcut);
2. Parts A discharged (≥4 fields), and a single named branch lemma (state it
   exactly) reduces the remaining fields to established Mathlib/repo facts;
3. Parts A discharged, but the branch-coherence lemma of Part C.1 is a genuine
   open analytic problem — give its exact statement and the sharpest available
   proof strategy;
4. an earlier obstruction blocks even Part A (identify it exactly).

Give the exact next worker task but do not create its file. Frame it against the
parameter-family consumer `GenuineBottcherLocalParameterFamilyData` and the
straddling-axiom endgame, not as an isolated fiber fact.

## Report contract

Include: every compiled `/tmp` statement and its proof or failure; exact
declaration signatures cited; the corrected field-by-field status of
`PrincipalPullbackCoherentDataFor`; the precise branch-coherence lemma statement;
full status; and confirmation that only the result artifact was written and no
commit was made.
