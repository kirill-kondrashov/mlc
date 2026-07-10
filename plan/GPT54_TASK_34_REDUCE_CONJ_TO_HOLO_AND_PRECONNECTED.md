# TASK 34 — Reduce the Böttcher conjugacy residual to holomorphicity + basin preconnectedness

## Global context

`mlc_conjecture` rests on exactly two axioms (`check_axioms.lean`):
`green_sublevel_translate_inter_mandelbrot_connected_straddling` and
`residualOpenVirtualNearMoleculeAxiom`. The Böttcher route to discharging the
straddling axiom needs a genuine holomorphic conjugating coordinate on
`basin_of_infinity c`, feeding `GenuineBottcherRouteFor c` and the
local-parameter-family closure in `Mlc/MainConjecture.lean`.

Iteration 33 built the coherent basin coordinate `coherentBasinCoordinate d`
(on-basin `d.value`, off-basin `0`) from an
`EscapeTimeIndependentPullbackDataFor c`, proved its Böttcher modulus and four
more `GenuineBottcherCoordinateDataFor` fields automatically, and landed
`genuineBottcherCoordinateData_of_escapeTimeIndependent_of_conj_of_holo`, which
reduces the entire genuine-coordinate target to exactly two residual analytic
facts about the coherent value:

- `conj_on_basin` : the coordinate conjugates `quadratic_map c` to squaring on
  the basin, and
- `holo_on_basin` : the coordinate is holomorphic on the (open) basin.

## This task: discharge `conj` against `holo` + basin preconnectedness

Land ONE theorem, `coherentBasinCoordinate_conj_of_holo_of_preconnected`, proving
that the conjugacy residual is a **consequence** of holomorphicity together with
preconnectedness of the basin. This removes `conj` as an independent residual:
after this task, the whole genuine-coordinate seam collapses to
`{holo_on_basin, IsPreconnected (basin_of_infinity c)}` — both classical
Douady–Hubbard-depth facts.

### Mechanism (identity theorem)

On the open basin `s := basin_of_infinity c`:
- `coherentBasinCoordinate d` is `AnalyticOnNhd` (from `DifferentiableOn` on the
  open set), hence so are `phi . f` (compose with the analytic `quadratic_map c`,
  which maps the basin into itself by `basin_of_infinity_forward_invariant`) and
  `phi ^ 2`.
- On the exterior collar `{‖z‖ > ‖c‖+2}` the coordinate agrees with
  `logSeriesBottcherApprox c` (via `coherentBasinCoordinate_extends_near`), and
  there the local Böttcher functional equation
  `logSeriesBottcherApprox_conj_iterate_outside_open c hz 1` gives
  `L (f z) = (L z) ^ 2`. The collar is an open neighborhood of the real point
  `w0 = up(‖c‖+3)`, so `phi . f` and `phi ^ 2` are eventually equal at `w0`.
- `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq` (with `IsPreconnected s`
  and `w0 in s`) propagates the equality to all of `s`.

## Placement

Add the theorem in
`Mlc/Quadratic/Complex/Bottcher/ConstructiveBasinModulus.lean`, inside its
existing `namespace MLC.Quadratic` (downstream of `GreenHarmonic`, so
`basin_of_infinity`, `coherentBasinCoordinate`, and
`coherentBasinCoordinate_extends_near` all resolve). Do **not** create a new
file. Do **not** edit `ConstructiveBasinCoordinate.lean`.

## The theorem (planner-verified — paste verbatim)

This exact script was inserted into `ConstructiveBasinModulus.lean` and compiled
under a full `lake build` (7890 jobs, green) with the axiom frontier unchanged
(`lake env lean check_axioms.lean`, exit 0). The `Set.MapsTo` / `Set.EqOn`
qualifications are required (the file does not `open Set`). Paste it verbatim:

```lean
theorem coherentBasinCoordinate_conj_of_holo_of_preconnected {c : ℂ}
    (d : EscapeTimeIndependentPullbackDataFor c)
    (hpre : IsPreconnected (MLC.Quadratic.basin_of_infinity c))
    (hholo : DifferentiableOn ℂ (coherentBasinCoordinate d)
      (MLC.Quadratic.basin_of_infinity c)) :
    ∀ z : ℂ, z ∈ MLC.Quadratic.basin_of_infinity c →
      coherentBasinCoordinate d (MLC.quadratic_map c z)
        = (coherentBasinCoordinate d z) ^ 2 := by
  set s := MLC.Quadratic.basin_of_infinity c with hs
  have hsopen : IsOpen s := basin_of_infinity_isOpen c
  -- analyticity of the coordinate
  have hcoord_an : AnalyticOnNhd ℂ (coherentBasinCoordinate d) s :=
    hholo.analyticOnNhd hsopen
  -- analyticity of the quadratic map
  have hfdiff : DifferentiableOn ℂ (MLC.quadratic_map c) s := by
    intro z _
    apply DifferentiableAt.differentiableWithinAt
    show DifferentiableAt ℂ (fun z => z ^ 2 + c) z
    fun_prop
  have hf_an : AnalyticOnNhd ℂ (MLC.quadratic_map c) s := hfdiff.analyticOnNhd hsopen
  have hmaps : Set.MapsTo (MLC.quadratic_map c) s s := basin_of_infinity_forward_invariant c
  -- the two analytic sides
  have hf1_an : AnalyticOnNhd ℂ
      (fun z => coherentBasinCoordinate d (MLC.quadratic_map c z)) s :=
    hcoord_an.comp hf_an hmaps
  have hf2_an : AnalyticOnNhd ℂ
      (fun z => (coherentBasinCoordinate d z) ^ 2) s :=
    hcoord_an.pow 2
  -- base point in the exterior
  set w₀ : ℂ := ((‖c‖ + 3 : ℝ) : ℂ) with hw0
  have hw0n : ‖w₀‖ = ‖c‖ + 3 := by
    rw [hw0, Complex.norm_real]; exact Real.norm_of_nonneg (by positivity)
  have hw0_norm : ‖w₀‖ > ‖c‖ + 2 := by rw [hw0n]; linarith
  have hw0_basin : w₀ ∈ s :=
    outside_disk_subset_quadratic_basin c (outside_open_subset_outside_disk c hw0_norm)
  have hfw0_norm : ‖MLC.quadratic_map c w₀‖ > ‖c‖ + 2 := by
    have hcnn : (0:ℝ) ≤ ‖c‖ := norm_nonneg _
    have hlow : ‖w₀‖ ^ 2 - ‖c‖ ≤ ‖MLC.quadratic_map c w₀‖ := by
      have htri : ‖w₀ ^ 2‖ ≤ ‖MLC.quadratic_map c w₀‖ + ‖c‖ := by
        have : w₀ ^ 2 = MLC.quadratic_map c w₀ + (-c) := by
          simp only [MLC.quadratic_map]; ring
        calc ‖w₀ ^ 2‖ = ‖MLC.quadratic_map c w₀ + (-c)‖ := by rw [this]
          _ ≤ ‖MLC.quadratic_map c w₀‖ + ‖(-c)‖ := norm_add_le _ _
          _ = ‖MLC.quadratic_map c w₀‖ + ‖c‖ := by rw [norm_neg]
      have hsq : ‖w₀ ^ 2‖ = ‖w₀‖ ^ 2 := by rw [norm_pow]
      linarith [htri, hsq.ge, hsq.le]
    rw [hw0n] at hlow
    nlinarith [hlow, hcnn]
  -- eventual equality near w₀
  have hcont : Continuous (fun z : ℂ => ‖MLC.quadratic_map c z‖) := by
    have : Continuous (MLC.quadratic_map c) := by
      show Continuous (fun z => z ^ 2 + c); fun_prop
    exact this.norm
  have hUopen : IsOpen ({z : ℂ | ‖c‖ + 2 < ‖z‖} ∩ {z : ℂ | ‖c‖ + 2 < ‖MLC.quadratic_map c z‖}) :=
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_const hcont)
  have hUmem : w₀ ∈ ({z : ℂ | ‖c‖ + 2 < ‖z‖} ∩ {z : ℂ | ‖c‖ + 2 < ‖MLC.quadratic_map c z‖}) :=
    ⟨hw0_norm, hfw0_norm⟩
  have heq : (fun z => coherentBasinCoordinate d (MLC.quadratic_map c z))
      =ᶠ[𝓝 w₀] (fun z => (coherentBasinCoordinate d z) ^ 2) := by
    refine eventually_of_mem (hUopen.mem_nhds hUmem) ?_
    intro z hz
    obtain ⟨hz1, hz2⟩ := hz
    show coherentBasinCoordinate d (MLC.quadratic_map c z)
        = (coherentBasinCoordinate d z) ^ 2
    have e1 : coherentBasinCoordinate d (MLC.quadratic_map c z)
        = MLC.logSeriesBottcherApprox c (MLC.quadratic_map c z) :=
      coherentBasinCoordinate_extends_near d _ hz2
    have e2 : coherentBasinCoordinate d z = MLC.logSeriesBottcherApprox c z :=
      coherentBasinCoordinate_extends_near d z hz1
    have econj : MLC.logSeriesBottcherApprox c (MLC.quadratic_map c z)
        = (MLC.logSeriesBottcherApprox c z) ^ 2 := by
      have h := logSeriesBottcherApprox_conj_iterate_outside_open c hz1 1
      simpa using h
    rw [e1, e2, econj]
  have hEq : Set.EqOn (fun z => coherentBasinCoordinate d (MLC.quadratic_map c z))
      (fun z => (coherentBasinCoordinate d z) ^ 2) s :=
    hf1_an.eqOn_of_preconnected_of_eventuallyEq hf2_an hpre hw0_basin heq
  intro z hz
  exact hEq hz
```

## Verification checklist

1. `lake build` is fully green; no new `sorry` / `axiom`.
2. `lake env lean check_axioms.lean` exits 0 — the frontier is still exactly the
   two project axioms.
3. `ConstructiveBasinCoordinate.lean` and `basinLogSeriesExtensionCandidate` are
   untouched.

## Report

Write `plan/GPT54_RESULT_34_REDUCE_CONJ_TO_HOLO_AND_PRECONNECTED.md` stating:
- the theorem landed and the build/axiom checks passed;
- the genuine-coordinate seam is now exactly
  `{holo_on_basin, IsPreconnected (basin_of_infinity c)}`, with `conj` no longer
  an independent residual;
- a one-line note that both residuals are classical Douady–Hubbard facts (open
  basin is preconnected; the coherent branch is holomorphic).

Do **not** introduce `sorry`/`axiom`, bundle away `holo` or `IsPreconnected`,
weaken/generalize the hypotheses, or commit.
