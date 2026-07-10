# TASK 37 — Build the local holomorphic root branch (Böttcher route, Stage 1 of `holo_on_basin`)

## Global context

`mlc_conjecture` rests on exactly two project axioms:
`MLC.green_sublevel_translate_inter_mandelbrot_connected_straddling` (parameter
plane) and `MLC.residualOpenVirtualNearMoleculeAxiom`. We are discharging the
first via the **Böttcher route**.

Progress so far on that route:
- Iteration 35–36 discharged the **basin-preconnectedness** residual
  *unconditionally* (`basin_of_infinity_isPreconnected`, in
  `Mlc/BasinConnected.lean`).
- The only remaining Böttcher-route residual for the coherent coordinate is
  `holo_on_basin`: holomorphicity on `basin_of_infinity c` of a coherent
  `2^N`-th-root branch of the near-infinity coordinate.

**Important finding (do not undo):** the *literal* candidate
`basinLogSeriesExtensionCandidate c` (principal `cpow` of the pulled-back
`logSeriesBottcherApprox`) is **discontinuous** — verified concretely at `c = 0`,
where it degenerates to the principal `(z²)^{1/2}`, which jumps across the
imaginary axis. So `holo_on_basin` is FALSE for that candidate. The fix is a
*coherent* redefinition assembled from **local** holomorphic root branches glued
across the basin by killing monodromy. This task delivers the reusable building
block — the local branches — as **Stage 1** of a three-stage program:

- **Stage 1 (THIS TASK):** local holomorphic `2^N`-th-root branches near any
  point whose `N`-th iterate has escaped the trapping disk, packaged as the
  existing `LocalPullbackRootBranchData c N z₀` structure.
- **Stage 2 (later):** a globally coherent value via simple-connectivity /
  monodromy triviality on the basin.
- **Stage 3 (later):** assemble the coherent holomorphic coordinate; discharge
  `holo_on_basin`.

Even completing all three stages closes only `holo_on_basin`; the parameter-plane
axiom additionally defers three more Yoccoz-scale pieces (holomorphic inverse
`Φ_c⁻¹`, puzzle-boundary holomorphic motion, parameter↔dynamical
correspondence). Keep expectations calibrated: this is Stage 1 of 4.

## What to build

Create a NEW leaf file `Mlc/BottcherLocalRootBranch.lean` containing exactly the
three declarations below and register it in `Mlc.lean`. The proof script is
**planner-verified**: it was placed in-repo, a full `lake build` (7983 jobs) ran
green, `lake env lean check_axioms.lean` returned exit 0 (frontier unchanged),
then it was reverted. Paste it **verbatim**.

The payload `localPullbackRootBranchData_of_iterate_outside c N z₀ (hz₀ :
‖f^[N] z₀‖ > ‖c‖ + 2)` produces a `LocalPullbackRootBranchData c N z₀`:
a neighborhood `U` of `z₀`, a holomorphic `branch : ℂ → ℂ` on `U` with
`(branch z)^(2^N) = logSeries c (f^[N] z)` on `U`, and `z₀ ∈ basin`. The branch
is built as `exp((log(F z / F z₀) + log(F z₀)) / 2^N)` where
`F z = logSeriesBottcherApprox c (f^[N] z)`, on the neighborhood where
`F z / F z₀` stays in the right-half-disk `‖· - 1‖ < 1 ⊆ slitPlane`.

## Placement

- Create `Mlc/BottcherLocalRootBranch.lean` with the verbatim content below.
- Add `import Mlc.BottcherLocalRootBranch` in `Mlc.lean` immediately after the
  existing `import Mlc.BasinConnected` line.
- Do **NOT** edit `ConstructiveBasinCoordinate.lean`,
  `ConstructiveBasinModulus.lean`, `BottcherCpowSlit.lean`, or any other existing
  file (other than adding the one import line to `Mlc.lean`).

## Verbatim script (`Mlc/BottcherLocalRootBranch.lean`)

```lean
import Mlc.Quadratic.Complex.Bottcher.ConstructiveBasinCoordinate
import Mlc.Quadratic.Complex.Bottcher.BottcherCpowSlit

open MLC MLC.Quadratic Complex Topology Filter Set

namespace MLC.Quadratic

/-- Differentiability of the fixed-parameter quadratic iterate. -/
lemma differentiable_quadratic_iterate (c : ℂ) (N : ℕ) :
    Differentiable ℂ (fun z => (MLC.quadratic_map c)^[N] z) := by
  induction N with
  | zero =>
      simp only [Function.iterate_zero]
      exact differentiable_id
  | succ n ih =>
      have heq : (fun z => (MLC.quadratic_map c)^[n + 1] z)
          = (fun z => ((MLC.quadratic_map c)^[n] z) ^ 2 + c) := by
        funext z
        rw [Function.iterate_succ_apply']
        simp [MLC.quadratic_map]
      rw [heq]
      exact (ih.pow 2).add (differentiable_const c)

/-- If some iterate of a point has escaped the trapping disk, the point lies in
the basin of infinity. -/
lemma mem_basin_of_iterate_mem_basin (c : ℂ) (N : ℕ) {z : ℂ}
    (h : (MLC.quadratic_map c)^[N] z ∈ basin_of_infinity c) :
    z ∈ basin_of_infinity c := by
  induction N generalizing z with
  | zero => simpa using h
  | succ n ih =>
      have h' : (MLC.quadratic_map c)^[n] (MLC.quadratic_map c z) ∈ basin_of_infinity c := by
        simpa [Function.iterate_succ_apply] using h
      exact basin_of_infinity_preimage_subset c (ih h')

/-- **Stage 1: local holomorphic root branch.** Near any point whose `N`-th
iterate has escaped the trapping disk, there is a holomorphic local branch of the
`2^N`-th root of the near-infinity coordinate pulled back along `f^[N]`, packaged
as `LocalPullbackRootBranchData`. -/
noncomputable def localPullbackRootBranchData_of_iterate_outside
    (c : ℂ) (N : ℕ) (z₀ : ℂ)
    (hz₀ : ‖(MLC.quadratic_map c)^[N] z₀‖ > ‖c‖ + 2) :
    LocalPullbackRootBranchData c N z₀ := by
  classical
  set F : ℂ → ℂ := fun z => MLC.logSeriesBottcherApprox c ((MLC.quadratic_map c)^[N] z)
    with hFdef
  set U₀ : Set ℂ := {z : ℂ | ‖c‖ + 2 < ‖(MLC.quadratic_map c)^[N] z‖} with hU₀def
  have hiter_diff : Differentiable ℂ (fun z => (MLC.quadratic_map c)^[N] z) :=
    differentiable_quadratic_iterate c N
  have hU₀open : IsOpen U₀ := by
    have : IsOpen {z : ℂ | ‖c‖ + 2 < ‖(MLC.quadratic_map c)^[N] z‖} :=
      isOpen_lt continuous_const (hiter_diff.continuous.norm)
    simpa [hU₀def] using this
  have hz₀U₀ : z₀ ∈ U₀ := hz₀
  have hlogdiff : DifferentiableOn ℂ (MLC.logSeriesBottcherApprox c)
      {z : ℂ | ‖c‖ + 2 < ‖z‖} :=
    MLC.logSeriesBottcherApprox_differentiableOn_large_radius c (R := ‖c‖ + 2) le_rfl
  have hFdiff : DifferentiableOn ℂ F U₀ := by
    have hcomp : DifferentiableOn ℂ
        (fun z => MLC.logSeriesBottcherApprox c ((MLC.quadratic_map c)^[N] z)) U₀ := by
      apply hlogdiff.comp hiter_diff.differentiableOn
      intro z hz; exact hz
    simpa [hFdef] using hcomp
  have hFz₀ne : F z₀ ≠ 0 := by
    have : 1 < ‖F z₀‖ :=
      MLC.one_lt_norm_logSeriesBottcherApprox_of_outside_open c hz₀
    intro h; rw [h, norm_zero] at this; linarith
  have hFcontAt : ContinuousAt F z₀ :=
    (hFdiff.differentiableAt (hU₀open.mem_nhds hz₀U₀)).continuousAt
  have hratio_tendsto : Filter.Tendsto (fun z => F z / F z₀) (𝓝 z₀) (𝓝 1) := by
    have : Filter.Tendsto (fun z => F z / F z₀) (𝓝 z₀) (𝓝 (F z₀ / F z₀)) :=
      hFcontAt.tendsto.div_const _
    rwa [div_self hFz₀ne] at this
  have hnear : ∀ᶠ z in 𝓝 z₀, ‖F z / F z₀ - 1‖ < 1 := by
    have := hratio_tendsto (Metric.ball_mem_nhds (1 : ℂ) (by norm_num : (0:ℝ) < 1))
    filter_upwards [this] with z hz
    simpa [Metric.mem_ball, dist_eq_norm] using hz
  have hUmem : U₀ ∈ 𝓝 z₀ := hU₀open.mem_nhds hz₀U₀
  set U : Set ℂ := U₀ ∩ {z : ℂ | ‖F z / F z₀ - 1‖ < 1} with hUdef
  have hUmem_nhds : U ∈ 𝓝 z₀ := Filter.inter_mem hUmem hnear
  have hz₀U : z₀ ∈ U := by
    refine ⟨hz₀U₀, ?_⟩
    simp only [Set.mem_setOf_eq, div_self hFz₀ne, sub_self, norm_zero]
    norm_num
  set g : ℂ → ℂ :=
    fun z => Complex.exp ((Complex.log (F z / F z₀) + Complex.log (F z₀)) / (2 ^ N)) with hgdef
  have hroot : ∀ z ∈ U, (g z) ^ (2 ^ N) = F z := by
    intro z hz
    have hzU₀ : z ∈ U₀ := hz.1
    have hFzne : F z ≠ 0 := by
      have : 1 < ‖F z‖ :=
        MLC.one_lt_norm_logSeriesBottcherApprox_of_outside_open c hzU₀
      intro h; rw [h, norm_zero] at this; linarith
    have hpow : (g z) ^ (2 ^ N)
        = Complex.exp (Complex.log (F z / F z₀) + Complex.log (F z₀)) := by
      rw [hgdef, ← Complex.exp_nat_mul]
      congr 1
      have hne : ((2 : ℂ) ^ N) ≠ 0 := pow_ne_zero _ (by norm_num)
      push_cast; field_simp
    rw [hpow, Complex.exp_add, Complex.exp_log (div_ne_zero hFzne hFz₀ne),
      Complex.exp_log hFz₀ne, div_mul_cancel₀ _ hFz₀ne]
  have hgdiff : DifferentiableOn ℂ g U := by
    intro z hz
    have hzU₀ : z ∈ U₀ := hz.1
    have hslit : F z / F z₀ ∈ slitPlane :=
      mem_slitPlane_of_norm_sub_one_lt_one hz.2
    have hFat : DifferentiableAt ℂ F z :=
      hFdiff.differentiableAt (hU₀open.mem_nhds hzU₀)
    have hratioAt : DifferentiableAt ℂ (fun z => F z / F z₀) z := hFat.div_const _
    have hlogAt : DifferentiableAt ℂ (fun z => Complex.log (F z / F z₀)) z :=
      hratioAt.clog hslit
    have hLAt : DifferentiableAt ℂ g z := by
      rw [hgdef]
      exact ((hlogAt.add_const _).div_const _).cexp
    exact hLAt.differentiableWithinAt
  exact
    { center_mem_basin :=
        mem_basin_of_iterate_mem_basin c N
          (outside_disk_subset_quadratic_basin c (outside_open_subset_outside_disk c hz₀))
      U := U
      U_mem_nhds := hUmem_nhds
      branch := g
      branch_differentiableOn := hgdiff
      root_eq := fun z hz => by
        have := hroot z hz; simpa [hFdef] using this
      center_value_mem_rootSet := by
        have := hroot z₀ hz₀U
        simpa [pullbackRootSet, hFdef] using this }

end MLC.Quadratic
```

## Verification checklist (all must pass)

1. `lake build` completes green (expected ~7983 jobs). No errors.
2. No new `sorry`, no new `axiom` anywhere. (`grep -nE "sorry|admit|axiom"
   Mlc/BottcherLocalRootBranch.lean` returns nothing.)
3. `lake env lean check_axioms.lean` returns exit 0 — the axiom frontier is still
   exactly the two project axioms. This leaf file adds nothing to any existing
   declaration's axiom set.
4. Do NOT commit.

## What to report (`plan/GPT54_RESULT_37_BUILD_LOCAL_ROOT_BRANCH.md`)

- Confirm the file was created, registered in `Mlc.lean`, and the full build +
  `check_axioms.lean` (exit 0) both pass; paste the final build tail and the
  axiom-check exit code.
- State precisely what is now available: `localPullbackRootBranchData_of_iterate_outside`
  populates `LocalPullbackRootBranchData c N z₀` for every `z₀` whose `N`-th
  iterate escapes the trapping disk — i.e. **Stage 1** (local holomorphic root
  branches) is landed.
- State clearly what is NOT yet done: this does NOT repair the discontinuous
  literal candidate and does NOT discharge `holo_on_basin`. Stage 2 (globally
  coherent value via monodromy triviality) and Stage 3 (assembly) remain, and
  even finishing all three closes only `holo_on_basin` — three further
  Yoccoz-scale pieces of the parameter-plane axiom remain beyond that.
- Do NOT introduce `sorry`/`axiom`, do NOT edit `ConstructiveBasinCoordinate.lean`
  or `ConstructiveBasinModulus.lean`, and do NOT commit.
