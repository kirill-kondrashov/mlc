# TASK 35 — Reduce basin preconnectedness to per-level superlevel connectivity

## Global context

`mlc_conjecture` rests on exactly two axioms (`check_axioms.lean`):
`green_sublevel_translate_inter_mandelbrot_connected_straddling` and
`residualOpenVirtualNearMoleculeAxiom`. The Böttcher route to discharging the
straddling axiom builds a genuine holomorphic conjugating coordinate on
`basin_of_infinity c`.

Iteration 33 built `coherentBasinCoordinate d` and reduced the genuine-coordinate
target to `conj_on_basin` + `holo_on_basin`; iteration 34
(`coherentBasinCoordinate_conj_of_holo_of_preconnected`) discharged `conj` against
holomorphicity + basin preconnectedness. The two remaining residuals are:

- `holo_on_basin` : the coherent branch is holomorphic on the basin, and
- `IsPreconnected (basin_of_infinity c)`.

This task attacks the second residual.

## The idea: basin as an increasing union of orbit-norm superlevel sets

`FilledJuliaConnected.lean` proves the *filled* Julia set `K c` connected as a
decreasing intersection of the compact sets `{z | ‖orbit c z n‖ ≤ R c}` (each a
quadratic preimage of a closed disk, connected because the disk contains the
critical value). The basin of infinity is the escaping set — the exact dual:

```
basin_of_infinity c = ⋃ n, {z | R c < ‖orbit c z n‖}
```

Key facts (all handled by the script below):
- **Union equality.** `z` escapes iff some orbit iterate exceeds the escape
  radius `R c` (`escape_lemma` forward; the basin's `Tendsto` definition
  backward, via `orbit_eq_iter_quadratic_map`).
- **Monotonicity.** Once `‖orbit c z k‖ > R c`, the next iterate is no smaller
  (`norm_orbit_ge_of_norm_ge_R`), so the superlevel sets increase in `n`.
- **Common core.** Every superlevel set contains the far-exterior point
  `↑(R c + 1)` (via monotonicity from level 0), so `⋂ n` is nonempty.
- **Assembly.** `isPreconnected_iUnion` turns "nonempty intersection + each piece
  preconnected" into preconnectedness of the union.

This reduces `IsPreconnected (basin_of_infinity c)` to the single hypothesis
`∀ n, IsPreconnected {z | R c < ‖orbit c z n‖}`.

## Placement

Create a NEW leaf file `Mlc/BasinConnected.lean`:

```lean
import Mlc.FilledJuliaConnected
import Mlc.Quadratic.Complex.Bottcher.BottcherCore
open MLC MLC.Quadratic Complex Topology Filter Set

namespace MLC.Quadratic

<THEOREM GOES HERE>

end MLC.Quadratic
```

Both imports are required (`FilledJuliaConnected` for `orbit`, `R`, `escape_lemma`,
`norm_orbit_ge_of_norm_ge_R`, `R_pos`, `orbit_succ`, `orbit_zero`;
`BottcherCore` for `basin_of_infinity`, `orbit_eq_iter_quadratic_map`). This file
is a leaf — nothing imports it yet — so there is no import cycle. Then add
`import Mlc.BasinConnected` to `Mlc.lean`.

Do **not** edit `ConstructiveBasinCoordinate.lean` or `ConstructiveBasinModulus.lean`.

## The theorem (planner-verified — paste verbatim)

This exact script compiled under `lake env lean` (`PROBE_EXIT_0`) with imports
`Mlc.FilledJuliaConnected` and `Mlc.Quadratic.Complex.Bottcher.BottcherCore` and
the `open` line above. Paste it verbatim inside `namespace MLC.Quadratic`:

```lean
theorem basin_preconnected_of_forall_superlevel_preconnected {c : ℂ}
    (hcrit : ∀ n : ℕ, IsPreconnected {z : ℂ | R c < ‖orbit c z n‖}) :
    IsPreconnected (MLC.Quadratic.basin_of_infinity c) := by
  have hstep : ∀ (k : ℕ) (z : ℂ), R c < ‖orbit c z k‖ → R c < ‖orbit c z (k + 1)‖ := by
    intro k z hk
    have hge : ‖orbit c z (k + 1)‖ ≥ ‖orbit c z k‖ := by
      simpa [orbit_succ] using norm_orbit_ge_of_norm_ge_R c (orbit c z k) 1 hk
    linarith
  have hmono : Monotone (fun n : ℕ => {z : ℂ | R c < ‖orbit c z n‖}) := by
    intro m n hmn
    induction hmn with
    | refl => exact le_refl _
    | @step n hle ih =>
        intro z hz
        exact hstep n z (ih hz)
  have hunion : MLC.Quadratic.basin_of_infinity c
      = ⋃ n, {z : ℂ | R c < ‖orbit c z n‖} := by
    ext z
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    constructor
    · intro hz
      have htend : Tendsto (fun n => ‖(MLC.quadratic_map c)^[n] z‖) atTop atTop := by
        simpa [MLC.Quadratic.basin_of_infinity, MLC.basin_of_infinity] using hz
      have htend' : Tendsto (fun k => ‖orbit c z k‖) atTop atTop := by
        simpa [orbit_eq_iter_quadratic_map c z] using htend
      obtain ⟨N, hN⟩ := (Filter.eventually_atTop.1 ((Filter.tendsto_atTop.1 htend') (R c + 1)))
      exact ⟨N, by have := hN N le_rfl; linarith⟩
    · rintro ⟨n, hn⟩
      have hgt : ‖orbit c z n‖ > R c := hn
      have htend' : Tendsto (fun k => ‖orbit c z k‖) atTop atTop := by
        rw [Filter.tendsto_atTop]; intro M
        obtain ⟨Nn, hNn⟩ := (MLC.Quadratic.escape_lemma (c := c) (z := z) n hgt) M
        rw [Filter.eventually_atTop]; exact ⟨Nn, fun m hm => le_of_lt (hNn m hm)⟩
      have htend : Tendsto (fun n => ‖(MLC.quadratic_map c)^[n] z‖) atTop atTop := by
        simpa [orbit_eq_iter_quadratic_map c z] using htend'
      simpa [MLC.Quadratic.basin_of_infinity, MLC.basin_of_infinity] using htend
  have hInterNe : (⋂ n, {z : ℂ | R c < ‖orbit c z n‖}).Nonempty := by
    refine ⟨((R c + 1 : ℝ) : ℂ), ?_⟩
    rw [Set.mem_iInter]
    intro n
    have hRpos : (0 : ℝ) < R c := R_pos c
    have hbase : ((R c + 1 : ℝ) : ℂ) ∈ {z : ℂ | R c < ‖orbit c z 0‖} := by
      simp only [Set.mem_setOf_eq, orbit_zero, Complex.norm_real]
      rw [Real.norm_of_nonneg (by linarith)]
      linarith
    exact hmono (Nat.zero_le n) hbase
  rw [hunion]
  exact isPreconnected_iUnion hInterNe hcrit
```

## Verification checklist

1. `lake build` is fully green; no new `sorry` / `axiom`.
2. `lake env lean check_axioms.lean` exits 0 — the frontier is still exactly the
   two project axioms.
3. `ConstructiveBasinCoordinate.lean` and `ConstructiveBasinModulus.lean` are
   untouched; only `Mlc/BasinConnected.lean` (new) and `Mlc.lean` (one import
   line) change.

## Report

Write `plan/GPT54_RESULT_35_REDUCE_BASIN_PRECONNECTED_TO_SUPERLEVEL.md` stating:
- the theorem landed and the build/axiom checks passed;
- basin preconnectedness is now reduced to the single crux
  `∀ n, IsPreconnected {z | R c < ‖orbit c z n‖}` (each orbit-norm superlevel set
  is connected);
- a one-line note that this crux is the genuine remaining content — a
  maximum-modulus / no-bounded-complementary-components argument on the polynomial
  `z ↦ orbit c z n` — and is NOT yet discharged.

Do **not** introduce `sorry`/`axiom`, attempt or stub the per-level crux (leave it
as the hypothesis), or commit.
