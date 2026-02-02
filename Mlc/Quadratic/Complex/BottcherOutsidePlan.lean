import Mlc.Quadratic.Complex.BottcherOutsideOutline
import Mlc.Quadratic.Complex.BottcherAnalyticInjective

namespace MLC

open Quadratic Complex Topology Set Filter

/-!
Plan: eliminate `bottcher_map_inj_on_outside`.

Step 1: Analyticity on the exterior.
  Goal: `AnalyticOnNhd ℂ (bottcher_map c) {‖z‖ > ‖c‖ + 2}`.
  Requires: `outside_disk` (or the open exterior) is contained in `slit_orbit c`.

Step 2: Normalization at infinity.
  Goal: `Tendsto (fun z => bottcher_map c z / z) atInfinity (𝓝 1)`.
  Use: the root sequence, branch coherence on slit, and escape estimates.

Step 3: Derivative nonvanishing on the exterior.
  Goal: `deriv (bottcher_map c) z ≠ 0` on `outside_disk c`.
  Use: analytic order lemma + local injectivity from Step 2.

Step 4: Properness / degree-one argument.
  Goal: global injectivity on `outside_disk c`.
  Use: local injectivity + properness.

Once Steps 1–4 are formalized, remove the axiom
`bottcher_map_inj_on_outside`.
-/

lemma bottcher_map_analytic_on_outside
    (c : ℂ) (hslit : {z : ℂ | ‖z‖ > ‖c‖ + 2} ⊆ slit_orbit c) :
    AnalyticOnNhd ℂ (Quadratic.bottcher_map c) {z : ℂ | ‖z‖ > ‖c‖ + 2} :=
  bottcher_map_analytic_on_outside_of_slit c hslit

lemma not_injOn_nhds_of_deriv_eq_zero
    {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) (hderiv : deriv f z = 0) :
    ∀ s ∈ 𝓝 z, ¬ Set.InjOn f s := by
  have hge :
      (2 : ℕ∞) ≤ analyticOrderAt (fun w => f w - f z) z :=
    analyticOrderAt_sub_ge_two_of_deriv_eq_zero hf hderiv
  exact not_injOn_nhds_of_analyticOrderAt_ge_two hf hge

lemma deriv_ne_zero_of_injOn_nhds
    {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z)
    (s : Set ℂ) (hs : s ∈ 𝓝 z) (hinj : Set.InjOn f s) :
    deriv f z ≠ 0 := by
  intro hzero
  have hnot := not_injOn_nhds_of_deriv_eq_zero hf hzero s hs
  exact hnot hinj

lemma bottcher_ratio_analytic_on_outside
    (c : ℂ) (hslit : {z : ℂ | ‖z‖ > ‖c‖ + 2} ⊆ slit_orbit c) :
    AnalyticOnNhd ℂ (fun z => (Quadratic.bottcher_map c z) / z)
      {z : ℂ | ‖z‖ > ‖c‖ + 2} := by
  let U : Set ℂ := {z : ℂ | ‖z‖ > ‖c‖ + 2}
  have hU : AnalyticOnNhd ℂ (Quadratic.bottcher_map c) U :=
    bottcher_map_analytic_on_outside c hslit
  have hid : AnalyticOnNhd ℂ (fun z : ℂ => z) U := by
    simpa [U] using (analyticOnNhd_id (𝕜 := ℂ) (s := U))
  have hne : ∀ z ∈ U, z ≠ 0 := by
    intro z hz
    have hz' : ‖z‖ > ‖c‖ + 2 := by simpa [U] using hz
    have hc : 0 < ‖c‖ + 2 := by
      have hc' : 0 ≤ ‖c‖ := by exact norm_nonneg _
      nlinarith
    have : 0 < ‖z‖ := lt_trans hc hz'
    exact (norm_ne_zero_iff).1 (ne_of_gt this)
  simpa [U] using (AnalyticOnNhd.div (f := Quadratic.bottcher_map c) (g := fun z : ℂ => z)
    hU hid hne)

lemma bottcher_normalized_at_infty_iff
    (c : ℂ) :
    bottcher_normalized_at_infty c ↔
      Tendsto (fun z => ‖(Quadratic.bottcher_map c z) / z - (1 : ℂ)‖) atInfinity (𝓝 0) := by
  -- `Tendsto` to `1` in a metric space is equivalent to the norm of the difference tending to `0`.
  simpa [bottcher_normalized_at_infty, dist_eq_norm] using
    (tendsto_iff_dist_tendsto_zero (f := fun z => (Quadratic.bottcher_map c z) / z)
      (a := (1 : ℂ)) (x := atInfinity))

lemma eventually_atInfinity_norm_gt (R : ℝ) :
    ∀ᶠ z in atInfinity, R < ‖z‖ := by
  -- unfold `atInfinity` and use the `atTop` basis.
  dsimp [atInfinity]
  have hR : ∀ᶠ r in (atTop : Filter ℝ), R < r :=
    (Filter.eventually_atTop.2 ⟨R + 1, by intro r hr; linarith⟩)
  -- use the comap characterization
  refine (Filter.eventually_comap).2 ?_
  refine hR.mono ?_
  intro r hr z hz
  simpa [hz] using hr

lemma eventually_atInfinity_mem_outside_open (c : ℂ) :
    ∀ᶠ z in atInfinity, z ∈ {z : ℂ | ‖z‖ > ‖c‖ + 2} := by
  have h := eventually_atInfinity_norm_gt (‖c‖ + 2)
  simpa using h

lemma outside_open_subset_outside_disk (c : ℂ) :
    {z : ℂ | ‖z‖ > ‖c‖ + 2} ⊆ outside_disk c := by
  intro z hz
  have hz' : ‖z‖ > ‖c‖ + 2 := by simpa using hz
  exact le_of_lt hz'

lemma bottcher_map_deriv_ne_zero_on_outside
    (c : ℂ) (hslit : {z : ℂ | ‖z‖ > ‖c‖ + 2} ⊆ slit_orbit c)
    (hinj : Set.InjOn (Quadratic.bottcher_map c) (outside_disk c)) :
    ∀ z, ‖z‖ > ‖c‖ + 2 → deriv (Quadratic.bottcher_map c) z ≠ 0 := by
  intro z hz
  let U : Set ℂ := {z : ℂ | ‖z‖ > ‖c‖ + 2}
  have hUopen : IsOpen U := by
    simpa [U] using (isOpen_lt continuous_const continuous_norm)
  have hUnhds : U ∈ 𝓝 z := hUopen.mem_nhds (by simpa [U] using hz)
  have hf : AnalyticAt ℂ (Quadratic.bottcher_map c) z :=
    (bottcher_map_analytic_on_outside c hslit) z (by simpa [U] using hz)
  have hinjU : Set.InjOn (Quadratic.bottcher_map c) U :=
    hinj.mono (by simpa [U] using outside_open_subset_outside_disk c)
  exact deriv_ne_zero_of_injOn_nhds hf U hUnhds hinjU

-- The open exterior `{‖z‖ > ‖c‖ + 2}` is the natural domain for Step 1.
-- Extending analyticity to the closed `outside_disk` would need boundary control.

def slitPlaneRot (θ : ℝ) : Set ℂ :=
  {z | z * Complex.exp (-Complex.I * θ) ∈ Complex.slitPlane}

lemma isOpen_slitPlaneRot (θ : ℝ) : IsOpen (slitPlaneRot θ) := by
  have hcont : Continuous (fun z : ℂ => z * Complex.exp (-Complex.I * θ)) := by
    simpa using (continuous_id.mul continuous_const)
  exact (isOpen_slitPlane.preimage hcont)

def slit_orbit_rot (c : ℂ) (θ : ℝ) : Set ℂ :=
  {z | ∀ n, (quadratic_map c)^[n] z ∈ slitPlaneRot θ}

lemma slitPlaneRot_zero : slitPlaneRot 0 = Complex.slitPlane := by
  ext z
  simp [slitPlaneRot]

lemma slit_orbit_rot_zero (c : ℂ) : slit_orbit_rot c 0 = slit_orbit c := by
  ext z
  simp [slit_orbit_rot, slit_orbit, slitPlaneRot_zero]

lemma slit_orbit_rot_iff (c : ℂ) (θ : ℝ) (z : ℂ) :
    z ∈ slit_orbit_rot c θ ↔
      ∀ n, (quadratic_map c)^[n] z * Complex.exp (-Complex.I * θ) ∈ Complex.slitPlane := by
  rfl

lemma quadratic_map_rotate (c : ℂ) (θ : ℝ) (z : ℂ) :
    quadratic_map c (z * Complex.exp (Complex.I * θ)) =
      (quadratic_map (c * Complex.exp (-Complex.I * θ * 2)) z) *
        Complex.exp (Complex.I * θ * 2) := by
  -- Algebraic conjugation identity under rotation.
  have hexp :
      (Complex.exp (Complex.I * θ)) ^ 2 = Complex.exp (Complex.I * θ * 2) := by
    -- `exp (2 * x) = exp x ^ 2`
    have h := (Complex.exp_nat_mul (Complex.I * θ) 2).symm
    -- rewrite `2 * (I*θ)` as `(I*θ) * 2`
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  calc
    quadratic_map c (z * Complex.exp (Complex.I * θ))
        = (z * Complex.exp (Complex.I * θ)) ^ 2 + c := by rfl
    _ = z ^ 2 * (Complex.exp (Complex.I * θ)) ^ 2 + c := by
          simp [pow_two, mul_assoc, mul_comm, mul_left_comm]
    _ = z ^ 2 * Complex.exp (Complex.I * θ * 2) + c := by
          simp [hexp]
    _ = z ^ 2 * Complex.exp (Complex.I * θ * 2) +
        Complex.exp (Complex.I * θ * 2) * c * Complex.exp (-Complex.I * θ * 2) := by
          have hmul :
              Complex.exp (Complex.I * θ * 2) * Complex.exp (-(Complex.I * θ * 2)) = 1 := by
            rw [← Complex.exp_add]
            simp
          -- insert `1 = exp(...) * exp(-...)` next to `c`
          calc
            z ^ 2 * Complex.exp (Complex.I * θ * 2) + c
                = z ^ 2 * Complex.exp (Complex.I * θ * 2) +
                    c * (Complex.exp (Complex.I * θ * 2) * Complex.exp (-(Complex.I * θ * 2))) := by
                      simp [hmul]
            _ = z ^ 2 * Complex.exp (Complex.I * θ * 2) +
                Complex.exp (Complex.I * θ * 2) * c * Complex.exp (-Complex.I * θ * 2) := by
                  ring_nf
    _ = (quadratic_map (c * Complex.exp (-Complex.I * θ * 2)) z) *
        Complex.exp (Complex.I * θ * 2) := by
          simp [quadratic_map, mul_add, mul_assoc, mul_comm, mul_left_comm]

lemma quadratic_map_rotate_only_trivial
    (c c' : ℂ) (θ : ℝ)
    (h : ∀ z, quadratic_map c (z * Complex.exp (Complex.I * θ)) =
      (quadratic_map c' z) * Complex.exp (Complex.I * θ)) :
    Complex.exp (Complex.I * θ) = 1 ∧ c' = c := by
  have h0 := h 0
  have h1 := h 1
  set e : ℂ := Complex.exp (Complex.I * θ)
  have hc : c = c' * e := by
    simpa [quadratic_map, e] using h0
  have h1' : e ^ 2 + c' * e = e + c' * e := by
    have h1'' : e ^ 2 + c = e * (1 + c') := by
      simpa [quadratic_map, e, pow_two, mul_assoc, mul_comm, mul_left_comm] using h1
    have h1''' : e ^ 2 + c = e + c' * e := by
      simpa [mul_add, mul_comm, mul_left_comm, mul_assoc] using h1''
    simpa [hc, add_assoc, add_left_comm, add_comm] using h1'''
  have hθ : e ^ 2 = e := by
    have h1'' : c' * e + e ^ 2 = c' * e + e := by
      simpa [add_comm, add_left_comm, add_assoc] using h1'
    exact add_left_cancel h1''
  have hθ' : e = 1 := by
    have h : e * (e - 1) = 0 := by
      calc
        e * (e - 1) = e ^ 2 - e := by ring
        _ = 0 := by simp [hθ]
    have hne : e ≠ 0 := by
      dsimp [e]
      exact Complex.exp_ne_zero (Complex.I * θ)
    have : e - 1 = 0 := (mul_eq_zero.mp h).resolve_left hne
    exact sub_eq_zero.mp this
  have hc' : c' = c := by
    have hc'' : c = c' := by
      simpa [hθ'] using hc
    exact hc''.symm
  exact ⟨hθ', hc'⟩

lemma slit_orbit_rot_forward (c : ℂ) (θ : ℝ) :
    MapsTo (quadratic_map c) (slit_orbit_rot c θ) (slit_orbit_rot c θ) := by
  intro z hz n
  -- unfold `slit_orbit_rot` and shift the index
  simpa [Function.iterate_succ_apply] using (hz (n + 1))

def local_slit (z₀ : ℂ) (ε : ℝ) : Set ℂ :=
  {z | dist z z₀ < ε} ∩ {z | z - z₀ ∈ Complex.slitPlane}

lemma local_slit_subset_slitPlane (z₀ : ℂ) (ε : ℝ) :
    local_slit z₀ ε ⊆ {z | z - z₀ ∈ Complex.slitPlane} := by
  intro z hz
  exact hz.2

lemma local_slit_isOpen (z₀ : ℂ) (ε : ℝ) : IsOpen (local_slit z₀ ε) := by
  have hball : IsOpen {z : ℂ | dist z z₀ < ε} :=
    Metric.isOpen_ball
  have hslit : IsOpen {z : ℂ | z - z₀ ∈ Complex.slitPlane} := by
    have hcont : Continuous (fun z : ℂ => z - z₀) := by
      simpa using (continuous_id.sub continuous_const)
    exact (isOpen_slitPlane.preimage hcont)
  exact hball.inter hslit

-- TODO: for each exterior point z₀, choose ε>0 with
-- `local_slit z₀ ε ⊆ slit_orbit c` (avoid the branch cut locally).

lemma bottcher_map_analytic_on_local_slit
    (c z₀ : ℂ) (ε : ℝ)
    (hslit : local_slit z₀ ε ⊆ slit_orbit c)
    (hbasin : local_slit z₀ ε ⊆ Quadratic.basin_of_infinity c) :
    AnalyticOnNhd ℂ (Quadratic.bottcher_map c) (local_slit z₀ ε) := by
  have hopen : IsOpen (local_slit z₀ ε) := local_slit_isOpen z₀ ε
  exact bottcher_map_analyticOnNhd_open c (local_slit z₀ ε) hopen hslit hbasin

lemma isOpen_preimage_slitPlane_iter (c : ℂ) (n : ℕ) :
    IsOpen {z : ℂ | (quadratic_map c)^[n] z ∈ Complex.slitPlane} := by
  have hcont : Continuous (fun z : ℂ => (quadratic_map c)^[n] z) :=
    (continuous_quadratic_map c).iterate n
  exact (isOpen_slitPlane.preimage hcont)

lemma exists_ball_subset_slit_orbit_prefix
    (c z₀ : ℂ) (N : ℕ) (hz₀ : z₀ ∈ slit_orbit c) :
    ∃ ε > 0, ∀ z, dist z z₀ < ε →
      ∀ n ≤ N, (quadratic_map c)^[n] z ∈ Complex.slitPlane := by
  induction N with
  | zero =>
      have hmem : z₀ ∈ {z : ℂ | z ∈ Complex.slitPlane} := hz₀ 0
      have hnhds : {z : ℂ | z ∈ Complex.slitPlane} ∈ 𝓝 z₀ :=
        isOpen_slitPlane.mem_nhds hmem
      rcases Metric.mem_nhds_iff.mp hnhds with ⟨ε, εpos, hball⟩
      refine ⟨ε, εpos, ?_⟩
      intro z hz n hn
      have hn' : n = 0 := Nat.le_zero.mp hn
      subst hn'
      exact hball hz
  | succ N ih =>
      rcases ih with ⟨ε, εpos, hε⟩
      have hmem : z₀ ∈ {z : ℂ | (quadratic_map c)^[N + 1] z ∈ Complex.slitPlane} :=
        hz₀ (N + 1)
      have hnhds :
          {z : ℂ | (quadratic_map c)^[N + 1] z ∈ Complex.slitPlane} ∈ 𝓝 z₀ :=
        (isOpen_preimage_slitPlane_iter c (N + 1)).mem_nhds hmem
      rcases Metric.mem_nhds_iff.mp hnhds with ⟨ε2, ε2pos, hball2⟩
      let ε' := min ε ε2
      have ε'pos : 0 < ε' := lt_min εpos ε2pos
      refine ⟨ε', ε'pos, ?_⟩
      intro z hz n hn
      have hzε : dist z z₀ < ε := lt_of_lt_of_le hz (min_le_left _ _)
      have hzε2 : dist z z₀ < ε2 := lt_of_lt_of_le hz (min_le_right _ _)
      have hle : n ≤ N ∨ n = N + 1 := by
        exact (lt_or_eq_of_le hn).elim (fun hlt => Or.inl (Nat.le_of_lt_succ hlt)) Or.inr
      cases hle with
      | inl hle' =>
          exact hε z hzε n hle'
      | inr hEq =>
          subst hEq
          exact hball2 hzε2

-- TODO: iterate-level conjugacy under rotation.
-- This should follow from `quadratic_map_rotate` by induction, with a corrected
-- expression for the parameter after rotation.

-- TODO: relate rotated slit orbits to the principal slit orbit.
-- The naive statement `z * exp(-I*θ) ∈ slit_orbit c` requires a conjugacy
-- argument on iterates, which will use `quadratic_map_rotate`.

lemma bottcher_map_analytic_on_outside_of_slit_rot
    (c : ℂ) (θ : ℝ)
    (_hslit : {z : ℂ | ‖z‖ > ‖c‖ + 2} ⊆ slit_orbit_rot c θ)
    (hslit : {z : ℂ | ‖z‖ > ‖c‖ + 2} ⊆ slit_orbit c) :
    AnalyticOnNhd ℂ (Quadratic.bottcher_map c) {z : ℂ | ‖z‖ > ‖c‖ + 2} :=
  bottcher_map_analytic_on_outside c hslit
end MLC
