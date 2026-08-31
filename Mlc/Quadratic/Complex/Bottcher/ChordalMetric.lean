import Mlc.Quadratic.Complex.Bottcher.SphericalDerivative

/-!
# The chordal (spherical) metric on `ℂ` via stereographic embedding

For the modern Zalcman route to **strong Montel**, normal families are measured in the
**chordal metric** — the distance on the Riemann sphere `ℂ ∪ {∞}` induced by the round
metric of the unit sphere `S² ⊂ ℝ³`.  Rather than axiomatize this metric, we *realize* it
concretely as the pullback of the Euclidean metric of `ℝ³` under the inverse stereographic
embedding

  `stereo z = (1 / (1 + ‖z‖²)) • (2·Re z, 2·Im z, ‖z‖² − 1)  ∈  EuclideanSpace ℝ (Fin 3)`.

This lands `z` on the unit sphere (`stereo_norm`), so *all* metric properties — symmetry,
the triangle inequality, nonnegativity — are inherited **for free** from `EuclideanSpace`.
The one substantive computation is the closed form

  `chordalDist z w ² = 4‖z − w‖² / ((1 + ‖z‖²)(1 + ‖w‖²))`  (`chordalDist_sq`),

from which the two workhorse bounds `chordalDist z w ≤ 2‖z − w‖` and `chordalDist z w ≤ 2`
follow.  These are exactly the inputs Marty's equicontinuity criterion needs to convert a
uniform bound on the spherical derivative `g#` into chordal equicontinuity of a family.
-/

namespace MLC.Quadratic

open Complex

/-- Inverse stereographic embedding of `ℂ` onto the unit sphere in `ℝ³`. -/
noncomputable def stereo (z : ℂ) : EuclideanSpace ℝ (Fin 3) :=
  (1 / (1 + ‖z‖ ^ 2)) • (EuclideanSpace.equiv (Fin 3) ℝ).symm ![2 * z.re, 2 * z.im, ‖z‖ ^ 2 - 1]

/-- The image of `stereo` lies on the unit sphere of `ℝ³`. -/
theorem stereo_norm (z : ℂ) : ‖stereo z‖ = 1 := by
  have hs : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.norm_def, Real.sq_sqrt (Complex.normSq_nonneg z), Complex.normSq_apply]; ring
  have hc : ∀ i : Fin 3, (stereo z) i = (1 / (1 + ‖z‖ ^ 2)) * ![2 * z.re, 2 * z.im, ‖z‖ ^ 2 - 1] i := by
    intro i; rw [stereo]; simp [EuclideanSpace.equiv]
  rw [EuclideanSpace.norm_eq, show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
  congr 1
  simp only [Fin.sum_univ_three, hc, Real.norm_eq_abs, sq_abs,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  rw [hs]; field_simp; ring

/-- The **chordal distance**: the Euclidean chord between the stereographic images. -/
noncomputable def chordalDist (z w : ℂ) : ℝ := dist (stereo z) (stereo w)

/-- Nonnegativity (inherited from the ambient metric). -/
theorem chordalDist_nonneg (z w : ℂ) : 0 ≤ chordalDist z w := dist_nonneg

/-- Symmetry (inherited from the ambient metric). -/
theorem chordalDist_comm (z w : ℂ) : chordalDist z w = chordalDist w z := dist_comm _ _

/-- Triangle inequality (inherited from the ambient metric). -/
theorem chordalDist_triangle (z w v : ℂ) :
    chordalDist z v ≤ chordalDist z w + chordalDist w v := dist_triangle _ _ _

/-- **Closed form** for the squared chordal distance. -/
theorem chordalDist_sq (z w : ℂ) :
    chordalDist z w ^ 2 = 4 * ‖z - w‖ ^ 2 / ((1 + ‖z‖ ^ 2) * (1 + ‖w‖ ^ 2)) := by
  have hsz : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.norm_def, Real.sq_sqrt (Complex.normSq_nonneg z), Complex.normSq_apply]; ring
  have hsw : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
    rw [Complex.norm_def, Real.sq_sqrt (Complex.normSq_nonneg w), Complex.normSq_apply]; ring
  have hzw : ‖z - w‖ ^ 2 = (z.re - w.re) ^ 2 + (z.im - w.im) ^ 2 := by
    rw [Complex.norm_def, Real.sq_sqrt (Complex.normSq_nonneg _), Complex.normSq_apply]
    simp [Complex.sub_re, Complex.sub_im]; ring
  have hcz : ∀ i : Fin 3, (stereo z) i = (1 / (1 + ‖z‖ ^ 2)) * ![2 * z.re, 2 * z.im, ‖z‖ ^ 2 - 1] i := by
    intro i; rw [stereo]; simp [EuclideanSpace.equiv]
  have hcw : ∀ i : Fin 3, (stereo w) i = (1 / (1 + ‖w‖ ^ 2)) * ![2 * w.re, 2 * w.im, ‖w‖ ^ 2 - 1] i := by
    intro i; rw [stereo]; simp [EuclideanSpace.equiv]
  have hDz : (0 : ℝ) < 1 + ‖z‖ ^ 2 := by positivity
  have hDw : (0 : ℝ) < 1 + ‖w‖ ^ 2 := by positivity
  rw [chordalDist, EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity)]
  simp only [Fin.sum_univ_three, hcz, hcw, Real.dist_eq, sq_abs,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  rw [hsz, hsw, hzw]; field_simp; ring

/-- The chordal distance is bounded by twice the Euclidean distance. -/
theorem chordalDist_le_two_mul (z w : ℂ) : chordalDist z w ≤ 2 * ‖z - w‖ := by
  have h1 : (1 : ℝ) ≤ (1 + ‖z‖ ^ 2) * (1 + ‖w‖ ^ 2) := by nlinarith [norm_nonneg z, norm_nonneg w]
  have hsq : chordalDist z w ^ 2 ≤ (2 * ‖z - w‖) ^ 2 := by
    rw [chordalDist_sq]
    calc 4 * ‖z - w‖ ^ 2 / ((1 + ‖z‖ ^ 2) * (1 + ‖w‖ ^ 2))
        ≤ 4 * ‖z - w‖ ^ 2 := div_le_self (by positivity) h1
      _ = (2 * ‖z - w‖) ^ 2 := by ring
  have hb : (0 : ℝ) ≤ 2 * ‖z - w‖ := by positivity
  nlinarith [chordalDist_nonneg z w, hsq, hb]

/-- The chordal distance never exceeds `2` (the diameter of the unit sphere). -/
theorem chordalDist_le_two (z w : ℂ) : chordalDist z w ≤ 2 := by
  have h : chordalDist z w ≤ ‖stereo z‖ + ‖stereo w‖ := by
    rw [chordalDist, dist_eq_norm]
    exact (norm_sub_le _ _)
  rw [stereo_norm, stereo_norm] at h
  linarith

/-- The stereographic embedding is continuous. -/
theorem continuous_stereo : Continuous stereo := by
  unfold stereo
  have hden : Continuous fun z : ℂ => 1 / (1 + ‖z‖ ^ 2) :=
    Continuous.div continuous_const (by fun_prop) (fun z => by positivity)
  have hvec : Continuous fun z : ℂ =>
      (EuclideanSpace.equiv (Fin 3) ℝ).symm ![2 * z.re, 2 * z.im, ‖z‖ ^ 2 - 1] := by
    apply Continuous.comp (g := (EuclideanSpace.equiv (Fin 3) ℝ).symm)
    · exact (EuclideanSpace.equiv (Fin 3) ℝ).symm.continuous
    · exact continuous_pi fun i => by fin_cases i <;> simp <;> fun_prop
  exact hden.smul hvec

/-- The chordal distance is jointly continuous. -/
theorem continuous_chordalDist : Continuous fun p : ℂ × ℂ => chordalDist p.1 p.2 :=
  continuous_dist.comp ((continuous_stereo.comp continuous_fst).prodMk
    (continuous_stereo.comp continuous_snd))

/-- The **sqrt closed form** for the chordal distance. -/
theorem chordalDist_eq (z w : ℂ) :
    chordalDist z w = 2 * ‖z - w‖ / Real.sqrt ((1 + ‖z‖ ^ 2) * (1 + ‖w‖ ^ 2)) := by
  have h1 : chordalDist z w = Real.sqrt (chordalDist z w ^ 2) :=
    (Real.sqrt_sq (chordalDist_nonneg z w)).symm
  rw [h1, chordalDist_sq, show 4 * ‖z - w‖ ^ 2 = (2 * ‖z - w‖) ^ 2 by ring,
    Real.sqrt_div' _ (by positivity), Real.sqrt_sq (by positivity)]

/-- The stereographic embedding is (real-)differentiable everywhere. -/
theorem differentiable_stereo : Differentiable ℝ stereo := by
  have hre : Differentiable ℝ (fun z : ℂ => z.re) := Complex.reCLM.differentiable
  have him : Differentiable ℝ (fun z : ℂ => z.im) := Complex.imCLM.differentiable
  have hsq : Differentiable ℝ (fun z : ℂ => ‖z‖ ^ 2) := by
    have h : (fun z : ℂ => ‖z‖ ^ 2) = (fun z : ℂ => z.re ^ 2 + z.im ^ 2) := by
      funext z; rw [Complex.norm_def, Real.sq_sqrt (Complex.normSq_nonneg z), Complex.normSq_apply]; ring
    rw [h]; exact (hre.pow 2).add (him.pow 2)
  have hns : Differentiable ℝ (fun z : ℂ => 1 + ‖z‖ ^ 2) := (differentiable_const 1).add hsq
  have hscal : Differentiable ℝ (fun z : ℂ => 1 / (1 + ‖z‖ ^ 2)) := by
    simp only [one_div]; exact hns.inv (fun z => by positivity)
  have hvec : Differentiable ℝ (fun z : ℂ =>
      (EuclideanSpace.equiv (Fin 3) ℝ).symm ![2 * z.re, 2 * z.im, ‖z‖ ^ 2 - 1]) := by
    apply Differentiable.comp (g := (EuclideanSpace.equiv (Fin 3) ℝ).symm)
      (EuclideanSpace.equiv (Fin 3) ℝ).symm.differentiable
    refine differentiable_pi.2 (fun i => ?_)
    fin_cases i
    · simpa using hre.const_mul 2
    · simpa using him.const_mul 2
    · simpa using hsq.sub_const 1
  unfold stereo; exact hscal.smul hvec

/-- A differentiable curve pushed to the sphere has a derivative. -/
theorem hasDerivAt_stereo_comp {c : ℝ → ℂ} {c' : ℂ} {u : ℝ} (hc : HasDerivAt c c' u) :
    HasDerivAt (fun t => stereo (c t)) (fderiv ℝ stereo (c u) c') u :=
  ((differentiable_stereo (c u)).hasFDerivAt).comp_hasDerivAt u hc

open Filter Topology in
/-- **Conformality of stereographic projection** in curve form: the speed of the pushed-forward
curve is the *spherical* speed `2‖c'‖ / (1 + ‖c u‖²)` of the original curve.  Proved by a slope
argument — no explicit Jacobian — using the closed form `chordalDist_eq`. -/
theorem norm_deriv_stereo_comp {c : ℝ → ℂ} {c' : ℂ} {u : ℝ} (hc : HasDerivAt c c' u) :
    ‖deriv (fun t => stereo (c t)) u‖ = 2 * ‖c'‖ / (1 + ‖c u‖ ^ 2) := by
  have hγ : HasDerivAt (fun t => stereo (c t)) (fderiv ℝ stereo (c u) c') u :=
    hasDerivAt_stereo_comp hc
  set v := fderiv ℝ stereo (c u) c' with hv
  rw [hγ.deriv]
  have hnormγ : Tendsto (fun y => ‖slope (fun t => stereo (c t)) u y‖) (𝓝[≠] u) (𝓝 ‖v‖) :=
    (continuous_norm.tendsto v).comp (hasDerivAt_iff_tendsto_slope.1 hγ)
  have hreform : (fun y => ‖slope (fun t => stereo (c t)) u y‖)
      =ᶠ[𝓝[≠] u] (fun y => 2 * ‖slope c u y‖ / Real.sqrt ((1 + ‖c y‖ ^ 2) * (1 + ‖c u‖ ^ 2))) := by
    filter_upwards with y
    have hsc : ‖slope c u y‖ = |(y - u)⁻¹| * ‖c y - c u‖ := by
      rw [slope, norm_smul, Real.norm_eq_abs, vsub_eq_sub]
    have hL : ‖slope (fun t => stereo (c t)) u y‖ = |(y - u)⁻¹| * chordalDist (c y) (c u) := by
      rw [slope, norm_smul, Real.norm_eq_abs, chordalDist, dist_eq_norm, vsub_eq_sub]
    rw [hL, chordalDist_eq, hsc]; ring
  have hslopec : Tendsto (fun y => ‖slope c u y‖) (𝓝[≠] u) (𝓝 ‖c'‖) :=
    (continuous_norm.tendsto c').comp (hasDerivAt_iff_tendsto_slope.1 hc)
  have hden : Tendsto (fun y => Real.sqrt ((1 + ‖c y‖ ^ 2) * (1 + ‖c u‖ ^ 2)))
      (𝓝[≠] u) (𝓝 (1 + ‖c u‖ ^ 2)) := by
    have hcc : Continuous fun p : ℂ => Real.sqrt ((1 + ‖p‖ ^ 2) * (1 + ‖c u‖ ^ 2)) := by fun_prop
    have hca : ContinuousAt (fun y : ℝ => Real.sqrt ((1 + ‖c y‖ ^ 2) * (1 + ‖c u‖ ^ 2))) u :=
      hcc.continuousAt.comp hc.continuousAt
    have h := hca.tendsto.mono_left (nhdsWithin_le_nhds (s := {u}ᶜ))
    have he : Real.sqrt ((1 + ‖c u‖ ^ 2) * (1 + ‖c u‖ ^ 2)) = 1 + ‖c u‖ ^ 2 := by
      rw [show (1 + ‖c u‖ ^ 2) * (1 + ‖c u‖ ^ 2) = (1 + ‖c u‖ ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
    rw [he] at h; exact h
  have h2 : Tendsto (fun y => 2 * ‖slope c u y‖ / Real.sqrt ((1 + ‖c y‖ ^ 2) * (1 + ‖c u‖ ^ 2)))
      (𝓝[≠] u) (𝓝 (2 * ‖c'‖ / (1 + ‖c u‖ ^ 2))) := by
    have hnum : Tendsto (fun y => 2 * ‖slope c u y‖) (𝓝[≠] u) (𝓝 (2 * ‖c'‖)) := hslopec.const_mul 2
    exact hnum.div hden (by positivity)
  exact tendsto_nhds_unique (hnormγ.congr' hreform) h2

open Set in
/-- **Marty-type equicontinuity bound.**  If `g` is holomorphic on the closed segment `[a, b]`
and its spherical derivative is bounded by `M` there, then the chordal distance between the
images is controlled linearly: `chordalDist (g a) (g b) ≤ 2 M ‖b − a‖`.

This is the mechanism that converts a *uniform* bound on the spherical derivative of a family
into chordal equicontinuity — the hypothesis of Arzelà–Ascoli en route to Montel's theorem. -/
theorem chordalDist_image_le_of_sphericalDeriv_le (g : ℂ → ℂ) (a b : ℂ) (M : ℝ)
    (hg : ∀ u ∈ Icc (0 : ℝ) 1, DifferentiableAt ℂ g (a + (↑u) * (b - a)))
    (hM : ∀ u ∈ Icc (0 : ℝ) 1, sphericalDeriv g (a + (↑u) * (b - a)) ≤ M) :
    chordalDist (g a) (g b) ≤ 2 * M * ‖b - a‖ := by
  set φ : ℝ → ℂ := fun t => a + (↑t : ℂ) * (b - a) with hφdef
  set c : ℝ → ℂ := fun t => g (φ t) with hcdef
  set γ : ℝ → EuclideanSpace ℝ (Fin 3) := fun t => stereo (c t) with hγdef
  have hcderiv : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt c ((b - a) * deriv g (φ u)) u := by
    intro u hu
    have hφ : HasDerivAt φ (b - a) u := by
      have h1 : HasDerivAt (fun t : ℝ => (↑t : ℂ)) 1 u := Complex.ofRealCLM.hasDerivAt
      simpa [hφdef] using (h1.mul_const (b - a)).const_add a
    simpa [hcdef, mul_comm] using (hg u hu).hasDerivAt.scomp u hφ
  have hbound : ∀ u ∈ Icc (0 : ℝ) 1, ‖deriv γ u‖ ≤ 2 * M * ‖b - a‖ := by
    intro u hu
    have hn : ‖deriv γ u‖ = 2 * ‖(b - a) * deriv g (φ u)‖ / (1 + ‖c u‖ ^ 2) :=
      norm_deriv_stereo_comp (hcderiv u hu)
    have hcu : c u = g (φ u) := rfl
    rw [hn, norm_mul, hcu,
      show 2 * (‖b - a‖ * ‖deriv g (φ u)‖) / (1 + ‖g (φ u)‖ ^ 2)
        = 2 * ‖b - a‖ * (‖deriv g (φ u)‖ / (1 + ‖g (φ u)‖ ^ 2)) by ring,
      show ‖deriv g (φ u)‖ / (1 + ‖g (φ u)‖ ^ 2) = sphericalDeriv g (φ u) from by rw [sphericalDeriv]]
    nlinarith [hM u hu, (by positivity : (0 : ℝ) ≤ 2 * ‖b - a‖)]
  have hdiffOn : DifferentiableOn ℝ γ (Icc (0 : ℝ) 1) := fun u hu =>
    ((hasDerivAt_stereo_comp (hcderiv u hu)).differentiableAt).differentiableWithinAt
  have hfin : ‖γ 1 - γ 0‖ ≤ 2 * M * ‖b - a‖ := by
    refine norm_image_sub_le_of_norm_deriv_le_segment_01 hdiffOn (fun x hx => ?_)
    have hxIcc : x ∈ Icc (0 : ℝ) 1 := Ico_subset_Icc_self hx
    rw [(hasDerivAt_stereo_comp (hcderiv x hxIcc)).differentiableAt.derivWithin
      (uniqueDiffOn_Icc (by norm_num) x hxIcc)]
    exact hbound x hxIcc
  have h1 : γ 1 = stereo (g b) := by simp [hγdef, hcdef, hφdef]
  have h0 : γ 0 = stereo (g a) := by simp [hγdef, hcdef, hφdef]
  rw [h1, h0] at hfin
  calc chordalDist (g a) (g b) = ‖stereo (g b) - stereo (g a)‖ := by
          rw [chordalDist, dist_eq_norm, norm_sub_rev]
    _ ≤ 2 * M * ‖b - a‖ := hfin

open Set in
/-- **Marty forward direction on a convex set.**  If `g` is holomorphic on a convex set `s`
with spherical derivative bounded by `M`, then `g` is *uniformly chordal-Lipschitz* on `s`:
`chordalDist (g z) (g w) ≤ 2 M ‖w − z‖`.  (Convexity guarantees the whole segment `[z, w]`
stays inside `s`, so the segment bound applies.) -/
theorem chordalDist_le_of_sphericalDeriv_le_on_convex {s : Set ℂ} (hs : Convex ℝ s)
    (g : ℂ → ℂ) (M : ℝ) (hg : ∀ z ∈ s, DifferentiableAt ℂ g z)
    (hM : ∀ z ∈ s, sphericalDeriv g z ≤ M) {z w : ℂ} (hz : z ∈ s) (hw : w ∈ s) :
    chordalDist (g z) (g w) ≤ 2 * M * ‖w - z‖ := by
  have hseg : ∀ u ∈ Icc (0 : ℝ) 1, z + (↑u) * (w - z) ∈ s := by
    intro u hu
    have hmem := hs hz hw (by linarith [hu.2] : (0 : ℝ) ≤ 1 - u) hu.1 (by ring)
    have heq : ((1 - u : ℝ)) • z + (u : ℝ) • w = z + (↑u) * (w - z) := by
      simp only [Complex.real_smul]; push_cast; ring
    rwa [heq] at hmem
  exact chordalDist_image_le_of_sphericalDeriv_le g z w M
    (fun u hu => hg _ (hseg u hu)) (fun u hu => hM _ (hseg u hu))

open Set in
/-- **Chordal equicontinuity of a family with uniformly bounded spherical derivative.**
This is the Arzelà–Ascoli input for Montel's theorem: a family `f` of holomorphic functions
on a convex set `s`, whose spherical derivatives are uniformly bounded by `M`, is uniformly
(chordally) equicontinuous — the modulus of continuity is *independent of the index* `i`. -/
theorem uniformEquicontinuous_of_sphericalDeriv_le {ι : Type*} {s : Set ℂ} (hs : Convex ℝ s)
    (f : ι → ℂ → ℂ) (M : ℝ) (hM0 : 0 ≤ M)
    (hdiff : ∀ i, ∀ z ∈ s, DifferentiableAt ℂ (f i) z)
    (hb : ∀ i, ∀ z ∈ s, sphericalDeriv (f i) z ≤ M) :
    ∀ ε > 0, ∃ δ > 0, ∀ i, ∀ z ∈ s, ∀ w ∈ s,
      ‖z - w‖ < δ → chordalDist (f i z) (f i w) < ε := by
  intro ε hε
  refine ⟨ε / (2 * M + 1), by positivity, fun i z hz w hw hzw => ?_⟩
  have hle : chordalDist (f i z) (f i w) ≤ 2 * M * ‖w - z‖ :=
    chordalDist_le_of_sphericalDeriv_le_on_convex hs (f i) M (hdiff i) (hb i) hz hw
  rw [norm_sub_rev] at hle
  have hpos : (0 : ℝ) < 2 * M + 1 := by positivity
  have hmul : (2 * M + 1) * ‖z - w‖ < ε := by
    have h := mul_lt_mul_of_pos_left hzw hpos
    rwa [mul_div_cancel₀ _ (ne_of_gt hpos)] at h
  nlinarith [norm_nonneg (z - w), hmul, hM0, hle]

open Set Filter Topology in
/-- **Ascoli input.**  The family `x ↦ stereo (f i x)`, lifted to the (compact) sphere in `ℝ³`
and restricted to a convex set `s` with uniformly bounded spherical derivatives, is
**uniformly equicontinuous** in the sense of Mathlib's `UniformEquicontinuous` — with the
explicit global continuity modulus `t ↦ 2 M t`.  Together with compactness of the sphere,
this is exactly the hypothesis of the Arzelà–Ascoli theorem, giving normality of the family. -/
theorem uniformEquicontinuous_stereo_comp {ι : Type*} {s : Set ℂ} (hs : Convex ℝ s)
    (f : ι → ℂ → ℂ) (M : ℝ)
    (hdiff : ∀ i, ∀ z ∈ s, DifferentiableAt ℂ (f i) z)
    (hb : ∀ i, ∀ z ∈ s, sphericalDeriv (f i) z ≤ M) :
    UniformEquicontinuous (fun (i : ι) (p : ↥s) => stereo (f i (↑p))) := by
  apply Metric.uniformEquicontinuous_of_continuity_modulus (fun t => 2 * M * t)
  · have h : Tendsto (fun t : ℝ => 2 * M * t) (nhds 0) (nhds (2 * M * 0)) :=
      (continuous_const.mul continuous_id).tendsto 0
    simpa using h
  · intro x y i
    have hchord : dist (stereo (f i ↑x)) (stereo (f i ↑y)) = chordalDist (f i ↑x) (f i ↑y) := rfl
    rw [hchord]
    have hd : dist x y = ‖(↑y : ℂ) - ↑x‖ := by
      rw [Subtype.dist_eq, Complex.dist_eq, norm_sub_rev]
    rw [hd]
    exact chordalDist_le_of_sphericalDeriv_le_on_convex hs (f i) M (hdiff i) (hb i) x.2 y.2

end MLC.Quadratic
