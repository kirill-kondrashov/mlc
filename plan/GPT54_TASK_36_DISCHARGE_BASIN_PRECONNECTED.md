# TASK 36 — Discharge basin preconnectedness (per-level maximum-modulus crux)

## Global context

`mlc_conjecture` rests on exactly two axioms (`check_axioms.lean`):
`green_sublevel_translate_inter_mandelbrot_connected_straddling` and
`residualOpenVirtualNearMoleculeAxiom`. The Böttcher route to discharging the
straddling axiom builds a genuine holomorphic conjugating coordinate on
`basin_of_infinity c`. Its residuals were `holo_on_basin`, `conj_on_basin`, and
`IsPreconnected (basin_of_infinity c)`; iteration 34
(`coherentBasinCoordinate_conj_of_holo_of_preconnected`) reduced `conj` to
holomorphicity + basin preconnectedness, and iteration 35 reduced basin
preconnectedness to the single per-level crux

```
∀ n, IsPreconnected {z | R c < ‖orbit c z n‖}
```

landing the assembly lemma `basin_preconnected_of_forall_superlevel_preconnected`
in the leaf file `Mlc/BasinConnected.lean`. **This task discharges that crux
unconditionally**, so `IsPreconnected (basin_of_infinity c)` becomes a plain
theorem and the only surviving Böttcher-route residual is `holo_on_basin`.

## The idea: maximum modulus without component machinery

Fix `n` and set `P z := orbit c z n` (an entire polynomial in `z`, since
`orbit c · (k+1) = (orbit c · k)^2 + c`). The superlevel set
`U = {z | R c < ‖P z‖}` is open (preimage of an open ray under the continuous
`‖P ·‖`) and contains the far exterior `E = {z | R c < ‖z‖}`, which is connected
(polar image of `Ioi (R c) ×ˢ univ`). Because once the orbit passes the escape
radius it never returns (`norm_orbit_ge_of_norm_ge_R`), `E ⊆ U`.

Mathlib has **no** "complement of a compact set has no bounded components" lemma,
so we argue directly. Suppose a separation `U ⊆ u ∪ v`, `U ∩ (u ∩ v) = ∅`, with
both `U ∩ u` and `U ∩ v` nonempty. The connected exterior `E` cannot be split, so
it sits entirely in one side; say `E ∩ w = ∅` for the *other* side `w`. Then the
open set `U ∩ w` omits the whole exterior, hence is bounded (contained in the
closed ball of radius `R c`). On its frontier `‖P‖ ≤ R c` (frontier points are
outside `U`, by `frontier_side_subset_compl`), while inside `‖P‖ > R c` — a direct
contradiction with the maximum modulus principle
(`Complex.exists_mem_frontier_isMaxOn_norm`). Hence no separation exists and `U`
is preconnected.

## Placement

APPEND the script below to the EXISTING leaf file `Mlc/BasinConnected.lean`,
immediately BEFORE its closing `end MLC.Quadratic`. The file already has the
required imports and `open` line:

```lean
import Mlc.FilledJuliaConnected
import Mlc.Quadratic.Complex.Bottcher.BottcherCore
open MLC MLC.Quadratic Complex Topology Filter Set

namespace MLC.Quadratic

-- (existing) basin_preconnected_of_forall_superlevel_preconnected
-- <<< APPEND THE SCRIPT BELOW HERE >>>

end MLC.Quadratic
```

Do NOT create a new file, do NOT alter the imports/`open` line, and do NOT touch
the existing reduction lemma.

## Verbatim proof script (planner-verified: full `lake build` green, axioms exit 0)

```lean
lemma differentiable_orbit (c : ℂ) (n : ℕ) :
    Differentiable ℂ (fun z => orbit c z n) := by
  induction n with
  | zero => simp only [orbit_zero]; exact differentiable_id
  | succ n ih =>
      have heq : (fun z => orbit c z (n + 1)) = (fun z => (orbit c z n) ^ 2 + c) := by
        funext z; rw [orbit_succ]; rfl
      rw [heq]
      exact (ih.pow 2).add (differentiable_const c)

lemma exterior_subset_superlevel (c : ℂ) (n : ℕ) :
    {z : ℂ | R c < ‖z‖} ⊆ {z : ℂ | R c < ‖orbit c z n‖} := by
  intro z hz
  exact lt_of_lt_of_le hz (norm_orbit_ge_of_norm_ge_R c z n hz)

lemma exterior_preconnected (c : ℂ) : IsPreconnected {z : ℂ | R c < ‖z‖} := by
  have hcont : Continuous (fun p : ℝ × ℝ => (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * I)) := by
    fun_prop
  have hpre : IsPreconnected ((Set.Ioi (R c)) ×ˢ (Set.univ : Set ℝ)) :=
    isPreconnected_Ioi.prod isPreconnected_univ
  have himg := hpre.image _ hcont.continuousOn
  have hset : (fun p : ℝ × ℝ => (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * I))
        '' ((Set.Ioi (R c)) ×ˢ (Set.univ : Set ℝ)) = {z : ℂ | R c < ‖z‖} := by
    ext z
    constructor
    · rintro ⟨⟨t, θ⟩, ⟨ht, -⟩, rfl⟩
      simp only [Set.mem_setOf_eq, norm_mul, Complex.norm_real, Complex.norm_exp_ofReal_mul_I,
        mul_one]
      rw [Real.norm_of_nonneg (le_of_lt (lt_trans (R_pos c) ht))]
      exact ht
    · intro hz
      refine ⟨(‖z‖, Complex.arg z), ⟨hz, Set.mem_univ _⟩, ?_⟩
      simpa using Complex.abs_mul_exp_arg_mul_I z
  rwa [hset] at himg

/-- Max-modulus contradiction: an entire `P` cannot exceed `R c` throughout a bounded
open set while staying `≤ R c` on its frontier. -/
lemma maxmod_absurd {c : ℂ} {P : ℂ → ℂ} (hPdiff : Differentiable ℂ P)
    {B : Set ℂ} (hBbdd : Bornology.IsBounded B) (hBne : B.Nonempty)
    (hin : ∀ x ∈ B, R c < ‖P x‖) (hfr : ∀ x ∈ frontier B, ‖P x‖ ≤ R c) : False := by
  obtain ⟨z0, hz0f, hz0max⟩ :=
    Complex.exists_mem_frontier_isMaxOn_norm hBbdd hBne hPdiff.diffContOnCl
  obtain ⟨b, hbB⟩ := hBne
  have h1 : R c < ‖P b‖ := hin b hbB
  have h2 : ‖P z0‖ ≤ R c := hfr z0 hz0f
  have h3 : ‖P b‖ ≤ ‖P z0‖ := hz0max (subset_closure hbB)
  linarith

/-- Frontier of the `b`-side of a separation lies outside `U`. -/
lemma frontier_side_subset_compl {U u v : Set ℂ} (hUopen : IsOpen U)
    (hu : IsOpen u) (hv : IsOpen v) (hUuv : U ⊆ u ∪ v) (hsep : U ∩ (u ∩ v) = ∅) :
    frontier (U ∩ v) ⊆ Uᶜ := by
  intro x hx
  rw [frontier, Set.mem_diff] at hx
  obtain ⟨hxcl, hxnint⟩ := hx
  intro hxU
  rcases hUuv hxU with hxu | hxv
  · -- x ∈ u : the open nbhd u ∩ U is disjoint from U ∩ v
    have hoa : IsOpen (u ∩ U) := hu.inter hUopen
    have hmem : x ∈ u ∩ U := ⟨hxu, hxU⟩
    have hdisj : (u ∩ U) ∩ (U ∩ v) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro y hy
      have hy2 : y ∈ U ∩ (u ∩ v) := ⟨hy.1.2, hy.1.1, hy.2.2⟩
      rw [hsep] at hy2
      exact hy2
    have hxnotcl : x ∉ closure (U ∩ v) := by
      rw [mem_closure_iff]; push_neg
      exact ⟨u ∩ U, hoa, hmem, hdisj⟩
    exact hxnotcl hxcl
  · -- x ∈ v : then x ∈ interior (U ∩ v), contradicting frontier
    have : x ∈ U ∩ v := ⟨hxU, hxv⟩
    have hint : x ∈ interior (U ∩ v) := by
      rw [(hUopen.inter hv).interior_eq]; exact this
    exact hxnint hint

theorem isPreconnected_orbit_superlevel (c : ℂ) (n : ℕ) :
    IsPreconnected {z : ℂ | R c < ‖orbit c z n‖} := by
  set P : ℂ → ℂ := fun z => orbit c z n with hPdef
  have hPdiff : Differentiable ℂ P := differentiable_orbit c n
  have hUopen : IsOpen {z : ℂ | R c < ‖P z‖} :=
    isOpen_lt continuous_const hPdiff.continuous.norm
  set U : Set ℂ := {z : ℂ | R c < ‖P z‖} with hUdef
  have hEsub : {z : ℂ | R c < ‖z‖} ⊆ U := exterior_subset_superlevel c n
  have hEpre : IsPreconnected {z : ℂ | R c < ‖z‖} := exterior_preconnected c
  intro u v hu hv hUuv hUu hUv
  by_contra hcon
  rw [Set.not_nonempty_iff_eq_empty] at hcon
  -- The bounded side leads to a max-modulus contradiction.
  -- Helper: given the side set `w` that the exterior avoids, build the contradiction.
  have bounded_side : ∀ w : Set ℂ, IsOpen w → (U ∩ w).Nonempty →
      ({z : ℂ | R c < ‖z‖} ∩ w = ∅) → frontier (U ∩ w) ⊆ Uᶜ → False := by
    intro w hw hUw hEw hfrontier
    have hBbdd : Bornology.IsBounded (U ∩ w) := by
      apply (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := R c)).subset
      intro z hz
      simp only [Metric.mem_closedBall, dist_zero_right]
      by_contra hgt
      push_neg at hgt
      have hzE : z ∈ {z : ℂ | R c < ‖z‖} := hgt
      have : z ∈ ({z : ℂ | R c < ‖z‖} ∩ w) := ⟨hzE, hz.2⟩
      rw [hEw] at this; exact this
    exact maxmod_absurd hPdiff hBbdd hUw
      (fun x hx => hx.1) (fun x hx => not_lt.1 (hfrontier hx))
  by_cases hEv : ({z : ℂ | R c < ‖z‖} ∩ v).Nonempty
  · by_cases hEu : ({z : ℂ | R c < ‖z‖} ∩ u).Nonempty
    · have hEuv := hEpre u v hu hv (hEsub.trans hUuv) hEu hEv
      obtain ⟨x, hxE, hxuv⟩ := hEuv
      have hxmem : x ∈ U ∩ (u ∩ v) := ⟨hEsub hxE, hxuv⟩
      rw [hcon] at hxmem; exact hxmem
    · -- E ∩ u = ∅ : bounded side is U ∩ u
      rw [Set.not_nonempty_iff_eq_empty] at hEu
      have hsep' : U ∩ (v ∩ u) = ∅ := by rw [Set.inter_comm v u]; exact hcon
      exact bounded_side u hu hUu hEu
        (frontier_side_subset_compl hUopen hv hu (by rwa [Set.union_comm] at hUuv) hsep')
  · -- E ∩ v = ∅ : bounded side is U ∩ v
    rw [Set.not_nonempty_iff_eq_empty] at hEv
    exact bounded_side v hv hUv hEv
      (frontier_side_subset_compl hUopen hu hv hUuv hcon)

/-- **The basin of infinity is preconnected** (for every parameter `c`). -/
theorem basin_of_infinity_isPreconnected (c : ℂ) :
    IsPreconnected (MLC.Quadratic.basin_of_infinity c) :=
  basin_preconnected_of_forall_superlevel_preconnected
    (fun n => isPreconnected_orbit_superlevel c n)
```

## Verification checklist

- Append the seven declarations verbatim before `end MLC.Quadratic`; keep the
  existing reduction lemma and imports untouched.
- `lake build` completes cleanly (one expected `linter.unnecessarySimpa` warning
  at the `exterior_preconnected` `simpa using Complex.abs_mul_exp_arg_mul_I z`
  line — acceptable, do not "fix" it by deleting the term).
- No new `sorry` / `axiom`.
- `lake env lean check_axioms.lean` exits 0: the frontier is still exactly
  `green_sublevel_translate_inter_mandelbrot_connected_straddling` and
  `residualOpenVirtualNearMoleculeAxiom`.
- Do NOT edit `ConstructiveBasinCoordinate.lean` or `ConstructiveBasinModulus.lean`.
- Do NOT commit.

## Report

In `plan/GPT54_RESULT_36_DISCHARGE_BASIN_PRECONNECTED.md`, state:
- `basin_of_infinity_isPreconnected c : IsPreconnected (basin_of_infinity c)`
  now holds **unconditionally** for every `c` — the basin-preconnectedness
  residual is fully discharged.
- Therefore the iteration-34 `conj` obligation
  (`coherentBasinCoordinate_conj_of_holo_of_preconnected`) is now derivable, and
  the ONLY remaining residual on the genuine Böttcher-coordinate route is
  `holo_on_basin` (holomorphicity of the coherent branch).
- Confirm build + axiom-frontier status (job count, exit codes).
