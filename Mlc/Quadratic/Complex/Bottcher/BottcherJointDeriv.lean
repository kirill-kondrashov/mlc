import Mlc.Quadratic.Complex.Bottcher.BottcherJointAnalytic

/-!
# Joint `ℂ²`-differentiability of the Böttcher coordinate

Building on the per-term joint analyticity (`BottcherJointAnalytic.lean`), this
file establishes the **keystone**: the logarithmic-correction series
`(c,z) ↦ logCorrectionSeries c z` — and hence the Böttcher coordinate
`φ_c(z) = logSeriesBottcherApprox c z` — is jointly `ℂ`-Fréchet differentiable on
an exterior polydisc, i.e. holomorphic in the two complex variables `(c, z)`
simultaneously.

Mathlib has no several-complex-variables analyticity theorem (no Osgood/Hartogs),
but it *does* have the **set-local** smooth-series lemma
`hasFDerivAt_tsum_of_isPreconnected`, which upgrades a termwise `HasFDerivAt` with
a summable bound on the derivatives to `HasFDerivAt` of the sum — over a general
Banach domain, in particular `ℂ² = ℂ × ℂ`. The one missing ingredient it needs is
a **summable bound on the joint Fréchet derivatives** of the terms; we supply this
by controlling the two coordinate partials via the one-variable Cauchy estimate
`Complex.norm_deriv_le_of_forall_mem_sphere_norm_le` and combining them with
`norm_clm_prod_le`.

Since the inverse function theorem over `𝕂 = ℂ` preserves `ℂ`-differentiability
(= holomorphy in each variable), joint `ℂ`-differentiability — *not* the stronger
joint analyticity — is exactly what is required to build the parametrized
holomorphic Böttcher inverse.
-/

namespace MLC

open Quadratic Complex Topology Set Filter Metric

/-- **Cauchy bound on the parameter (`c`) partial** of a Böttcher term.  On a
`c`-disc of radius `ρ` staying in the exterior (for fixed `z`), the one-variable
Cauchy estimate bounds the `c`-derivative by the majorant `(3/2)(‖c‖+ρ)(1/2)^{n+1}`
divided by `ρ`. -/
lemma norm_derivC_nearOneLogCorrection_le (n : ℕ) {c z : ℂ} {ρ : ℝ}
    (hρ : 0 < ρ) (hz : ‖c‖ + ρ + 2 < ‖z‖) :
    ‖deriv (fun c' => nearOneLogCorrection c' n z) c‖
      ≤ ((3 / 2 : ℝ) * (‖c‖ + ρ) * (1 / 2 : ℝ) ^ (n + 1)) / ρ := by
  set M : ℝ := (3 / 2 : ℝ) * (‖c‖ + ρ) * (1 / 2 : ℝ) ^ (n + 1) with hM
  -- differentiability on a slightly larger c-ball keeps the whole closed disc exterior
  set r : ℝ := ρ + (‖z‖ - ‖c‖ - ρ - 2) / 2 with hr
  have hrρ : ρ < r := by rw [hr]; linarith
  have hrz : ‖c‖ + r + 2 < ‖z‖ := by rw [hr]; linarith
  have hdiffOn : DifferentiableOn ℂ (fun c' => nearOneLogCorrection c' n z)
      (ball c r) :=
    nearOneLogCorrection_differentiableOn_param (c₀ := c) (r := r)
      (by linarith) (z := z) n hrz
  have hdcc : DiffContOnCl ℂ (fun c' => nearOneLogCorrection c' n z) (ball c ρ) :=
    hdiffOn.diffContOnCl_ball (Metric.closedBall_subset_ball hrρ)
  -- value bound on the boundary sphere
  have hC : ∀ c' ∈ sphere c ρ, ‖nearOneLogCorrection c' n z‖ ≤ M := by
    intro c' hc'
    rw [Metric.mem_sphere, dist_eq_norm] at hc'
    have hcc : ‖c'‖ ≤ ‖c‖ + ρ := by
      calc ‖c'‖ = ‖(c' - c) + c‖ := by ring_nf
        _ ≤ ‖c' - c‖ + ‖c‖ := norm_add_le _ _
        _ = ρ + ‖c‖ := by rw [hc']
        _ = ‖c‖ + ρ := by ring
    have hzc : ‖c'‖ + 2 < ‖z‖ := by linarith
    have hb := norm_nearOneLogCorrection_le c' n (R := ‖c'‖ + 2) (le_refl _) hzc
    calc ‖nearOneLogCorrection c' n z‖
        ≤ (3 / 2 : ℝ) * ‖c'‖ * (1 / 2 : ℝ) ^ (n + 1) := hb
      _ ≤ M := by
          rw [hM]
          have : (0:ℝ) ≤ (1/2:ℝ)^(n+1) := by positivity
          nlinarith [norm_nonneg c', hcc, this]
  simpa [hM] using Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρ hdcc hC



/-- **Cauchy bound on the dynamical (`z`) partial** of a Böttcher term.  On a
`z`-disc of radius `ρ` staying in the exterior (for fixed `c`), the one-variable
Cauchy estimate bounds the `z`-derivative by `(3/2)‖c‖(1/2)^{n+1} / ρ`. -/
lemma norm_derivZ_nearOneLogCorrection_le (n : ℕ) {c z : ℂ} {ρ : ℝ}
    (hρ : 0 < ρ) (hz : ‖c‖ + ρ + 2 < ‖z‖) :
    ‖deriv (fun z' => nearOneLogCorrection c n z') z‖
      ≤ ((3 / 2 : ℝ) * ‖c‖ * (1 / 2 : ℝ) ^ (n + 1)) / ρ := by
  set M : ℝ := (3 / 2 : ℝ) * ‖c‖ * (1 / 2 : ℝ) ^ (n + 1) with hM
  -- differentiability on the exterior `{‖c‖+2 < ‖·‖}` covers the closed disc
  have hdiffOn : DifferentiableOn ℂ (nearOneLogCorrection c n)
      {z' : ℂ | ‖c‖ + 2 < ‖z'‖} :=
    nearOneLogCorrection_differentiableOn_large_radius c n (le_refl _)
  have hsub : closedBall z ρ ⊆ {z' : ℂ | ‖c‖ + 2 < ‖z'‖} := by
    intro w hw
    rw [Metric.mem_closedBall, dist_eq_norm] at hw
    have hwz : ‖z‖ - ‖w‖ ≤ ρ := by
      have := norm_sub_norm_le z w
      calc ‖z‖ - ‖w‖ ≤ ‖z - w‖ := this
        _ = ‖w - z‖ := by rw [norm_sub_rev]
        _ ≤ ρ := hw
    simp only [mem_setOf_eq]; linarith
  have hdcc : DiffContOnCl ℂ (nearOneLogCorrection c n) (ball z ρ) :=
    hdiffOn.diffContOnCl_ball hsub
  have hC : ∀ z' ∈ sphere z ρ, ‖nearOneLogCorrection c n z'‖ ≤ M := by
    intro z' hz'
    rw [Metric.mem_sphere, dist_eq_norm] at hz'
    have hz'ge : ‖c‖ + 2 < ‖z'‖ := hsub (by
      rw [Metric.mem_closedBall, dist_eq_norm]; rw [hz'])
    exact norm_nearOneLogCorrection_le c n (R := ‖c‖ + 2) (le_refl _) hz'ge
  simpa [hM] using Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρ hdcc hC



/-- The operator norm of a `ℂ`-linear map on `ℂ × ℂ` is controlled by its values
on the two coordinate directions. -/
lemma norm_clm_prod_le (L : (ℂ × ℂ) →L[ℂ] ℂ) :
    ‖L‖ ≤ ‖L (1, 0)‖ + ‖L (0, 1)‖ := by
  refine L.opNorm_le_bound (by positivity) (fun x => ?_)
  obtain ⟨h, k⟩ := x
  have hsplit : ((h, k) : ℂ × ℂ) = h • ((1 : ℂ), (0 : ℂ)) + k • ((0 : ℂ), (1 : ℂ)) := by
    simp
  have hh : ‖h‖ ≤ ‖(h, k)‖ := le_max_left _ _ |>.trans_eq (by rw [Prod.norm_def])
  have hk : ‖k‖ ≤ ‖(h, k)‖ := le_max_right _ _ |>.trans_eq (by rw [Prod.norm_def])
  calc ‖L (h, k)‖
      = ‖h • L (1, 0) + k • L (0, 1)‖ := by
        rw [hsplit, L.map_add, L.map_smul, L.map_smul]
    _ ≤ ‖h • L (1, 0)‖ + ‖k • L (0, 1)‖ := norm_add_le _ _
    _ = ‖h‖ * ‖L (1, 0)‖ + ‖k‖ * ‖L (0, 1)‖ := by rw [norm_smul, norm_smul]
    _ ≤ ‖(h, k)‖ * ‖L (1, 0)‖ + ‖(h, k)‖ * ‖L (0, 1)‖ := by
        gcongr
    _ = (‖L (1, 0)‖ + ‖L (0, 1)‖) * ‖(h, k)‖ := by ring



/-- **Summable joint-fderiv bound for the Böttcher terms.**  At an exterior point
`x = (c, z)` with a disc of radius `ρ` still exterior, the joint `ℂ²`-Fréchet
derivative of `(c,z) ↦ nearOneLogCorrection c n z` is bounded by
`(2/ρ)·(3/2)(‖c‖+ρ)(1/2)^{n+1}`, a summable majorant in `n`. -/
lemma norm_fderiv_nearOneLogCorrection_joint_le (n : ℕ) {x : ℂ × ℂ} {ρ : ℝ}
    (hρ : 0 < ρ) (hxρ : ‖x.1‖ + ρ + 2 < ‖x.2‖) :
    ‖fderiv ℂ (fun p : ℂ × ℂ => nearOneLogCorrection p.1 n p.2) x‖
      ≤ (2 / ρ) * ((3 / 2 : ℝ) * (‖x.1‖ + ρ) * (1 / 2 : ℝ) ^ (n + 1)) := by
  obtain ⟨c, z⟩ := x
  simp only at hxρ ⊢
  have hxe : ‖c‖ + 2 < ‖z‖ := by linarith
  set F : ℂ × ℂ → ℂ := fun p => nearOneLogCorrection p.1 n p.2 with hF
  have hana : AnalyticAt ℂ F (c, z) :=
    analyticAt_nearOneLogCorrection_joint_exterior n (by simpa using hxe)
  have hderiv : HasFDerivAt F (fderiv ℂ F (c, z)) (c, z) :=
    hana.differentiableAt.hasFDerivAt
  set L := fderiv ℂ F (c, z) with hL
  have hcslice : deriv (fun c' => nearOneLogCorrection c' n z) c = L (1, 0) := by
    have hli : HasDerivAt (fun t : ℂ => (t, z)) ((1 : ℂ), (0 : ℂ)) c :=
      (hasDerivAt_id c).prodMk (hasDerivAt_const c z)
    have := (hderiv.comp_hasDerivAt c hli).deriv
    simpa [hF] using this
  have hzslice : deriv (fun z' => nearOneLogCorrection c n z') z = L (0, 1) := by
    have hri : HasDerivAt (fun t : ℂ => (c, t)) ((0 : ℂ), (1 : ℂ)) z :=
      (hasDerivAt_const z c).prodMk (hasDerivAt_id z)
    have := (hderiv.comp_hasDerivAt z hri).deriv
    simpa [hF] using this
  have hbc := norm_derivC_nearOneLogCorrection_le n hρ (c := c) (z := z) hxρ
  have hbz := norm_derivZ_nearOneLogCorrection_le n hρ (c := c) (z := z) hxρ
  rw [hcslice] at hbc
  rw [hzslice] at hbz
  have hpow : (0:ℝ) ≤ (1/2:ℝ)^(n+1) := by positivity
  calc ‖L‖ ≤ ‖L (1, 0)‖ + ‖L (0, 1)‖ := norm_clm_prod_le L
    _ ≤ ((3 / 2 : ℝ) * (‖c‖ + ρ) * (1 / 2 : ℝ) ^ (n + 1)) / ρ
          + ((3 / 2 : ℝ) * ‖c‖ * (1 / 2 : ℝ) ^ (n + 1)) / ρ := add_le_add hbc hbz
    _ ≤ ((3 / 2 : ℝ) * (‖c‖ + ρ) * (1 / 2 : ℝ) ^ (n + 1)) / ρ
          + ((3 / 2 : ℝ) * (‖c‖ + ρ) * (1 / 2 : ℝ) ^ (n + 1)) / ρ := by
        have hBA : (3 / 2 : ℝ) * ‖c‖ * (1 / 2 : ℝ) ^ (n + 1)
            ≤ (3 / 2 : ℝ) * (‖c‖ + ρ) * (1 / 2 : ℝ) ^ (n + 1) := by
          nlinarith [norm_nonneg c, hpow, le_of_lt hρ]
        exact add_le_add (le_refl _) (div_le_div_of_nonneg_right hBA (le_of_lt hρ))
    _ = (2 / ρ) * ((3 / 2 : ℝ) * (‖c‖ + ρ) * (1 / 2 : ℝ) ^ (n + 1)) := by ring



/-- **Keystone: joint `ℂ²`-differentiability of the Böttcher log-correction series.**
On a polydisc `ball c₀ a ×ˢ ball z₀ a` sitting deep in the exterior
(`‖c₀‖ + 3a + 2 < ‖z₀‖`), the series `(c,z) ↦ logCorrectionSeries c z` is jointly
`ℂ`-Fréchet differentiable, with derivative the sum of the term derivatives.
Obtained from Mathlib's set-local smooth-series lemma
`hasFDerivAt_tsum_of_isPreconnected` fed by the summable joint-fderiv bound. -/
lemma logCorrectionSeries_hasFDerivAt_joint
    {c₀ z₀ : ℂ} {a : ℝ} (ha : 0 < a) (hz₀ : ‖c₀‖ + 3 * a + 2 < ‖z₀‖)
    {x : ℂ × ℂ} (hx : x ∈ ball c₀ a ×ˢ ball z₀ a) :
    HasFDerivAt (fun p : ℂ × ℂ => logCorrectionSeries p.1 p.2)
      (∑' n, fderiv ℂ (fun p : ℂ × ℂ => nearOneLogCorrection p.1 n p.2) x) x := by
  set s : Set (ℂ × ℂ) := ball c₀ a ×ˢ ball z₀ a with hs
  set v : ℕ → ℝ := fun n => (2 / a) * ((3 / 2 : ℝ) * (‖c₀‖ + 2 * a) * (1 / 2 : ℝ) ^ (n + 1))
    with hv
  -- geometric majorant is summable
  have hvsum : Summable v := by
    have : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1)) := by
      simpa using (summable_geometric_two).comp_injective (add_left_injective 1)
    simpa [hv, mul_comm, mul_left_comm, mul_assoc] using
      (this.mul_left ((2 / a) * ((3 / 2 : ℝ) * (‖c₀‖ + 2 * a))))
  have hsopen : IsOpen s := (isOpen_ball).prod (isOpen_ball)
  have hspre : IsPreconnected s :=
    ((convex_ball c₀ a).isPreconnected).prod ((convex_ball z₀ a).isPreconnected)
  -- membership unfolding + exterior facts on s
  have hmem : ∀ y : ℂ × ℂ, y ∈ s → ‖y.1‖ < ‖c₀‖ + a ∧ ‖z₀‖ - a < ‖y.2‖ := by
    intro y hy
    rw [hs, Set.mem_prod, mem_ball, mem_ball, dist_eq_norm, dist_eq_norm] at hy
    constructor
    · calc ‖y.1‖ = ‖(y.1 - c₀) + c₀‖ := by ring_nf
        _ ≤ ‖y.1 - c₀‖ + ‖c₀‖ := norm_add_le _ _
        _ < a + ‖c₀‖ := by linarith [hy.1]
        _ = ‖c₀‖ + a := by ring
    · have h2 : ‖z₀‖ - ‖y.2‖ ≤ ‖y.2 - z₀‖ := by
        have := norm_sub_norm_le z₀ y.2; rw [norm_sub_rev] at this; linarith [this]
      linarith [hy.2]
  have hext : ∀ y : ℂ × ℂ, y ∈ s → ‖y.1‖ + a + 2 < ‖y.2‖ := by
    intro y hy
    obtain ⟨h1, h2⟩ := hmem y hy
    linarith
  -- hypotheses of the smooth-series lemma
  have hf : ∀ (n : ℕ) (y : ℂ × ℂ), y ∈ s →
      HasFDerivAt (fun p : ℂ × ℂ => nearOneLogCorrection p.1 n p.2)
        (fderiv ℂ (fun p : ℂ × ℂ => nearOneLogCorrection p.1 n p.2) y) y := by
    intro n y hy
    have hye : ‖y.1‖ + 2 < ‖y.2‖ := by linarith [hext y hy]
    exact (analyticAt_nearOneLogCorrection_joint_exterior n hye).differentiableAt.hasFDerivAt
  have hf' : ∀ (n : ℕ) (y : ℂ × ℂ), y ∈ s →
      ‖fderiv ℂ (fun p : ℂ × ℂ => nearOneLogCorrection p.1 n p.2) y‖ ≤ v n := by
    intro n y hy
    obtain ⟨h1, _⟩ := hmem y hy
    have hb := norm_fderiv_nearOneLogCorrection_joint_le n (x := y) (ρ := a) ha (hext y hy)
    refine hb.trans ?_
    rw [hv]
    have hpow : (0:ℝ) ≤ (1/2:ℝ)^(n+1) := by positivity
    have : ‖y.1‖ + a ≤ ‖c₀‖ + 2 * a := by linarith
    have h2a : (0:ℝ) < 2 / a := by positivity
    apply mul_le_mul_of_nonneg_left _ (le_of_lt h2a)
    nlinarith [hpow, this]
  -- base point and pointwise convergence there
  have hx₀ : (c₀, z₀) ∈ s := by
    rw [hs, Set.mem_prod, mem_ball, mem_ball, dist_self, dist_self]; exact ⟨ha, ha⟩
  have hf0 : Summable fun n => nearOneLogCorrection c₀ n z₀ := by
    apply Summable.of_norm_bounded (g := fun n => (3 / 2 : ℝ) * ‖c₀‖ * (1 / 2 : ℝ) ^ (n + 1))
    · have : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1)) := by
        simpa using (summable_geometric_two).comp_injective (add_left_injective 1)
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (this.mul_left ((3 / 2 : ℝ) * ‖c₀‖))
    · intro n
      exact norm_nearOneLogCorrection_le c₀ n (R := ‖c₀‖ + 2) (le_refl _) (by linarith)
  exact hasFDerivAt_tsum_of_isPreconnected hvsum hsopen hspre hf hf' hx₀ hf0 hx



/-- **Joint `ℂ²`-differentiability of the Böttcher coordinate** `φ_c(z)` on the
exterior polydisc. This is the parameter-and-dynamical joint holomorphy needed to
run the holomorphic inverse function theorem in `ℂ²`. -/
lemma logSeriesBottcherApprox_differentiableAt_joint
    {c₀ z₀ : ℂ} {a : ℝ} (ha : 0 < a) (hz₀ : ‖c₀‖ + 3 * a + 2 < ‖z₀‖)
    {x : ℂ × ℂ} (hx : x ∈ ball c₀ a ×ˢ ball z₀ a) :
    DifferentiableAt ℂ (fun p : ℂ × ℂ => logSeriesBottcherApprox p.1 p.2) x := by
  have hL : DifferentiableAt ℂ (fun p : ℂ × ℂ => logCorrectionSeries p.1 p.2) x :=
    (logCorrectionSeries_hasFDerivAt_joint ha hz₀ hx).differentiableAt
  have hEq : (fun p : ℂ × ℂ => logSeriesBottcherApprox p.1 p.2)
      = fun p : ℂ × ℂ => p.2 * Complex.exp (logCorrectionSeries p.1 p.2) := rfl
  rw [hEq]
  exact differentiableAt_snd.mul hL.cexp

/-- **`C¹` regularity of the joint log-correction series.**
On the exterior polydisc, `(c,z) ↦ logCorrectionSeries c z` is not merely jointly
`ℂ`-differentiable but jointly `C¹`: its Fréchet derivative is continuous. This is
the strictness enabler for the `ℂ²` inverse function theorem — a `C¹` map over `ℂ`
is strictly differentiable, so `ContDiffAt.to_localInverse` applies. Continuity of
the derivative comes from `continuousOn_tsum` (uniform convergence of the termwise
Fréchet derivatives, each continuous by `AnalyticAt.fderiv`). -/
lemma logCorrectionSeries_contDiffAt_one_joint
    {c₀ z₀ : ℂ} {a : ℝ} (ha : 0 < a) (hz₀ : ‖c₀‖ + 3 * a + 2 < ‖z₀‖)
    {x : ℂ × ℂ} (hx : x ∈ ball c₀ a ×ˢ ball z₀ a) :
    ContDiffAt ℂ 1 (fun p : ℂ × ℂ => logCorrectionSeries p.1 p.2) x := by
  set s : Set (ℂ × ℂ) := ball c₀ a ×ˢ ball z₀ a with hs
  set v : ℕ → ℝ := fun n => (2 / a) * ((3 / 2 : ℝ) * (‖c₀‖ + 2 * a) * (1 / 2 : ℝ) ^ (n + 1))
    with hv
  have hvsum : Summable v := by
    have : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1)) := by
      simpa using (summable_geometric_two).comp_injective (add_left_injective 1)
    simpa [hv, mul_comm, mul_left_comm, mul_assoc] using
      (this.mul_left ((2 / a) * ((3 / 2 : ℝ) * (‖c₀‖ + 2 * a))))
  have hmem : ∀ y : ℂ × ℂ, y ∈ s → ‖y.1‖ < ‖c₀‖ + a ∧ ‖z₀‖ - a < ‖y.2‖ := by
    intro y hy
    rw [hs, Set.mem_prod, mem_ball, mem_ball, dist_eq_norm, dist_eq_norm] at hy
    refine ⟨?_, ?_⟩
    · calc ‖y.1‖ = ‖(y.1 - c₀) + c₀‖ := by ring_nf
        _ ≤ ‖y.1 - c₀‖ + ‖c₀‖ := norm_add_le _ _
        _ < a + ‖c₀‖ := by linarith [hy.1]
        _ = ‖c₀‖ + a := by ring
    · have h2 : ‖z₀‖ - ‖y.2‖ ≤ ‖y.2 - z₀‖ := by
        have := norm_sub_norm_le z₀ y.2; rw [norm_sub_rev] at this; linarith [this]
      linarith [hy.2]
  have hext : ∀ y : ℂ × ℂ, y ∈ s → ‖y.1‖ + a + 2 < ‖y.2‖ := by
    intro y hy; obtain ⟨h1, h2⟩ := hmem y hy; linarith
  rw [contDiffAt_one_iff]
  refine ⟨fun y => ∑' n, fderiv ℂ (fun p : ℂ × ℂ => nearOneLogCorrection p.1 n p.2) y,
    s, (hs ▸ (isOpen_ball.prod isOpen_ball)).mem_nhds hx, ?_, ?_⟩
  · apply continuousOn_tsum (u := v) _ hvsum
    · intro n y hy
      obtain ⟨h1, _⟩ := hmem y hy
      have hb := norm_fderiv_nearOneLogCorrection_joint_le n (x := y) (ρ := a) ha (hext y hy)
      refine hb.trans ?_
      rw [hv]
      have hpow : (0:ℝ) ≤ (1/2:ℝ)^(n+1) := by positivity
      have hle : ‖y.1‖ + a ≤ ‖c₀‖ + 2 * a := by linarith
      have h2a : (0:ℝ) < 2 / a := by positivity
      apply mul_le_mul_of_nonneg_left _ (le_of_lt h2a)
      nlinarith [hpow, hle]
    · intro n y hy
      have hye : ‖y.1‖ + 2 < ‖y.2‖ := by linarith [hext y hy]
      exact ((analyticAt_nearOneLogCorrection_joint_exterior n hye).fderiv).continuousAt.continuousWithinAt
  · intro y hy
    exact logCorrectionSeries_hasFDerivAt_joint ha hz₀ hy

/-- **`C¹` regularity of the joint Böttcher coordinate** `φ_c(z) = z·exp(…)`.
Immediate from the `C¹` regularity of the log-correction series together with the
smoothness of multiplication and `Complex.exp`. This is the hypothesis
`ContDiffAt ℂ 1 F` needed to invoke the `ℂ²` inverse function theorem. -/
lemma logSeriesBottcherApprox_contDiffAt_one_joint
    {c₀ z₀ : ℂ} {a : ℝ} (ha : 0 < a) (hz₀ : ‖c₀‖ + 3 * a + 2 < ‖z₀‖)
    {x : ℂ × ℂ} (hx : x ∈ ball c₀ a ×ˢ ball z₀ a) :
    ContDiffAt ℂ 1 (fun p : ℂ × ℂ => logSeriesBottcherApprox p.1 p.2) x := by
  have hL : ContDiffAt ℂ 1 (fun p : ℂ × ℂ => logCorrectionSeries p.1 p.2) x :=
    logCorrectionSeries_contDiffAt_one_joint ha hz₀ hx
  have hEq : (fun p : ℂ × ℂ => logSeriesBottcherApprox p.1 p.2)
      = fun p : ℂ × ℂ => p.2 * Complex.exp (logCorrectionSeries p.1 p.2) := rfl
  rw [hEq]
  exact contDiffAt_snd.mul hL.cexp


end MLC
