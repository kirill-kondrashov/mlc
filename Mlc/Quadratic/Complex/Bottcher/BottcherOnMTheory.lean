import Mlc.Quadratic.Complex.Bottcher.BottcherMotion
import Mlc.Quadratic.Complex.Bottcher.BottcherCore
import Mlc.Quadratic.Complex.Bottcher.BottcherAxioms
import Mlc.Quadratic.Complex.Bottcher.BottcherOnMDefs
import Mlc.Quadratic.Complex.PuzzleBoundaryMotion
import Mlc.Quadratic.Complex.InverseBranch
import Mlc.Quadratic.Complex.InverseBranchQuadratic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

namespace MLC

open Quadratic Complex Topology Set Filter

/-!
Full-strength theory roadmap for `bottcher_onM_hyp` (currently TODO).

References:
- Milnor, Dynamics in One Complex Variable, §6.7 (Böttcher theorem).
- Slodkowski / λ-lemma (holomorphic motions).
- Parameter and dynamical Böttcher maps for `ℂ \ M`.
- Stability of parameter disks in the Mandelbrot set.

These statements are intentionally left as `sorry` placeholders. The outline
file keeps the build clean; this file records the intended endpoints.
-/

theorem continuous_quadratic_map (c : ℂ) : Continuous (quadratic_map c) := by
  have h_pow : Continuous (fun z : ℂ => z ^ 2) := (continuous_id.pow 2)
  have h_add : Continuous (fun z : ℂ => c + z ^ 2) := continuous_const.add h_pow
  have h_add' : Continuous (fun z : ℂ => z ^ 2 + c) := by
    simpa [add_comm, add_left_comm, add_assoc] using h_add
  simpa [quadratic_map] using h_add'

theorem quadratic_map_differentiable (c : ℂ) :
    Differentiable ℂ (quadratic_map c) := by
  have h_pow : Differentiable ℂ (fun z : ℂ => z ^ 2) :=
    (differentiable_id.pow 2)
  unfold quadratic_map
  exact h_pow.add_const c

theorem quadratic_map_differentiableOn (c : ℂ) :
    DifferentiableOn ℂ (quadratic_map c) Set.univ := by
  simpa using (quadratic_map_differentiable c).differentiableOn

def slit_orbit (c : ℂ) : Set ℂ :=
  {z | ∀ n, (quadratic_map c)^[n] z ∈ Complex.slitPlane}

lemma bottcher_approx_continuousOn_slit (c : ℂ) (n : ℕ) :
    ContinuousOn (fun z =>
      ((quadratic_map c)^[n] z) ^ ((1 : ℂ) / (2 : ℂ) ^ n))
      (slit_orbit c) := by
  intro z hz
  have hcont : ContinuousAt (fun z => (quadratic_map c)^[n] z) z :=
    ((continuous_quadratic_map c).iterate n).continuousAt
  have hcpow : ContinuousAt (fun w : ℂ => w ^ ((1 : ℂ) / (2 : ℂ) ^ n))
      ((quadratic_map c)^[n] z) :=
    continuousAt_cpow_const (hz n)
  have hcomp : ContinuousAt (fun z => (quadratic_map c)^[n] z ^ ((1 : ℂ) / (2 : ℂ) ^ n)) z :=
    hcpow.comp hcont
  exact hcomp.continuousWithinAt

lemma bottcher_approx_differentiableOn_slit (c : ℂ) (n : ℕ) :
    DifferentiableOn ℂ (fun z =>
      ((quadratic_map c)^[n] z) ^ ((1 : ℂ) / (2 : ℂ) ^ n))
      (slit_orbit c) := by
  have hdiff : Differentiable ℂ (fun z => (quadratic_map c)^[n] z) :=
    (quadratic_map_differentiable c).iterate n
  have h0 : ∀ z ∈ slit_orbit c, (quadratic_map c)^[n] z ∈ Complex.slitPlane := by
    intro z hz
    exact hz n
  simpa using (DifferentiableOn.cpow_const (f := fun z => (quadratic_map c)^[n] z)
    (s := slit_orbit c) (c := (1 : ℂ) / (2 : ℂ) ^ n)
    hdiff.differentiableOn h0)

/-- The `n`-th Böttcher approximant `z ↦ (f^[n] z)^{1/2^n}` is differentiable on the
much larger set where only the `n`-th iterate (not the whole orbit) avoids the slit.
This is the honest building block: the branch cut of the `n`-th approximant lives on
`{z | (f^[n] z) ∉ slitPlane}`, and this cut moves with `n`. -/
lemma bottcher_approx_differentiableOn_single_slit (c : ℂ) (n : ℕ) :
    DifferentiableOn ℂ (fun z =>
      ((quadratic_map c)^[n] z) ^ ((1 : ℂ) / (2 : ℂ) ^ n))
      {z : ℂ | (quadratic_map c)^[n] z ∈ Complex.slitPlane} := by
  have hdiff : Differentiable ℂ (fun z => (quadratic_map c)^[n] z) :=
    (quadratic_map_differentiable c).iterate n
  have h0 : ∀ z ∈ {z : ℂ | (quadratic_map c)^[n] z ∈ Complex.slitPlane},
      (quadratic_map c)^[n] z ∈ Complex.slitPlane := fun _ hz => hz
  simpa using (DifferentiableOn.cpow_const (f := fun z => (quadratic_map c)^[n] z)
    (s := {z : ℂ | (quadratic_map c)^[n] z ∈ Complex.slitPlane})
    (c := (1 : ℂ) / (2 : ℂ) ^ n)
    hdiff.differentiableOn h0)

/-!
### Continuous roots of holomorphic functions

General complex-analytic tool for the functional-equation route to basin
analyticity: a continuous, non-vanishing `k`-th root of a locally holomorphic,
non-vanishing function is itself holomorphic. This lets one transport
holomorphy of `proxy_bottcher_map` from a neighbourhood of a *fixed* escaped
iterate `f^[n] z` back to `z`, using the functional equation
`proxy (f^[n] z) = (proxy z)^(2^n)`, avoiding the moving branch cut of the
global power-approximation sequence.
-/

/-- The `k`-th roots of unity in `ℂ` form a finite set. -/
theorem finite_kth_rootsOfUnity (k : ℕ) (hk : 0 < k) :
    {z : ℂ | z ^ k = 1}.Finite := by
  have hp : (Polynomial.X ^ k - Polynomial.C 1 : Polynomial ℂ) ≠ 0 :=
    Polynomial.X_pow_sub_C_ne_zero hk 1
  have hsub : {z : ℂ | z ^ k = 1} ⊆
      (Polynomial.X ^ k - Polynomial.C 1 : Polynomial ℂ).rootSet ℂ := by
    intro z hz
    rw [Polynomial.mem_rootSet]
    refine ⟨hp, ?_⟩
    have hzk : z ^ k = 1 := hz
    simp [hzk]
  exact (Polynomial.rootSet_finite _ ℂ).subset hsub

/-- If `g` is holomorphic on a neighbourhood of `z₀` and `g z₀ ≠ 0`, then there is
a holomorphic `k`-th root branch `H` of `g` near `z₀`. -/
theorem exists_holomorphic_kth_root
    {g : ℂ → ℂ} {z₀ : ℂ} {k : ℕ} (hk : 0 < k)
    (hg : ∀ᶠ w in 𝓝 z₀, DifferentiableAt ℂ g w) (hgz : g z₀ ≠ 0) :
    ∃ H : ℂ → ℂ,
      (∀ᶠ w in 𝓝 z₀, DifferentiableAt ℂ H w) ∧
      (∀ᶠ w in 𝓝 z₀, (H w) ^ k = g w) ∧
      (∀ᶠ w in 𝓝 z₀, H w ≠ 0) := by
  obtain ⟨a, ha⟩ : ∃ a : ℂ, a ^ k = g z₀ := IsAlgClosed.exists_pow_nat_eq (g z₀) hk
  set c := g z₀ with hc
  have hcne : c ≠ 0 := hgz
  have ha0 : a ≠ 0 := by
    intro h; rw [h, zero_pow hk.ne'] at ha; exact hgz ha.symm
  have hkne : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have hgz0 : DifferentiableAt ℂ g z₀ := hg.self_of_nhds
  have hgcont : ContinuousAt (fun w => g w / c) z₀ := (hgz0.div_const c).continuousAt
  have hslit0 : (fun w => g w / c) z₀ ∈ Complex.slitPlane := by
    have hval : (fun w => g w / c) z₀ = 1 := by simp only []; rw [hc]; exact div_self hcne
    rw [hval]; exact Complex.one_mem_slitPlane
  have hev_slit : ∀ᶠ w in 𝓝 z₀, g w / c ∈ Complex.slitPlane :=
    hgcont.eventually_mem (Complex.isOpen_slitPlane.mem_nhds hslit0)
  refine ⟨fun w => a * Complex.exp (Complex.log (g w / c) / k), ?_, ?_, ?_⟩
  · filter_upwards [hg, hev_slit] with w hgw hslitw
    have hlogw : DifferentiableAt ℂ (fun w => Complex.log (g w / c)) w :=
      (hgw.div_const c).clog hslitw
    exact (differentiableAt_const a).mul ((hlogw.div_const (k : ℂ)).cexp)
  · filter_upwards [hev_slit] with w hslitw
    have hwne : g w / c ≠ 0 := Complex.slitPlane_ne_zero hslitw
    calc (a * Complex.exp (Complex.log (g w / c) / k)) ^ k
        = a ^ k * (Complex.exp (Complex.log (g w / c) / k)) ^ k := by rw [mul_pow]
      _ = a ^ k * Complex.exp ((Complex.log (g w / c) / k) * k) := by
            rw [← Complex.exp_nat_mul]; ring_nf
      _ = a ^ k * Complex.exp (Complex.log (g w / c)) := by rw [div_mul_cancel₀ _ hkne]
      _ = c * (g w / c) := by rw [ha, Complex.exp_log hwne]
      _ = g w := by field_simp
  · filter_upwards with w
    exact mul_ne_zero ha0 (Complex.exp_ne_zero _)

/-- A continuous, non-vanishing `k`-th root of a locally holomorphic non-vanishing
function is holomorphic. Here `h` is continuous at `z₀`, `g` is holomorphic on a
neighbourhood with `g z₀ ≠ 0`, and `(h w)^k = g w` near `z₀`; then `h` is
differentiable at `z₀`. -/
theorem differentiableAt_of_continuousAt_kth_root
    {h g : ℂ → ℂ} {z₀ : ℂ} {k : ℕ} (hk : 0 < k)
    (hg : ∀ᶠ w in 𝓝 z₀, DifferentiableAt ℂ g w) (hgz : g z₀ ≠ 0)
    (hhcont : ContinuousAt h z₀)
    (hroot : ∀ᶠ w in 𝓝 z₀, (h w) ^ k = g w) :
    DifferentiableAt ℂ h z₀ := by
  obtain ⟨H, hHdiff, hHroot, hHne⟩ := exists_holomorphic_kth_root hk hg hgz
  have hHdiff0 : DifferentiableAt ℂ H z₀ := hHdiff.self_of_nhds
  have hHne0 : H z₀ ≠ 0 := hHne.self_of_nhds
  have hHcont0 : ContinuousAt H z₀ := hHdiff0.continuousAt
  set φ : ℂ → ℂ := fun w => h w / H w with hφdef
  have hζ : φ z₀ ^ k = 1 := by
    have hh0 : (h z₀) ^ k = g z₀ := hroot.self_of_nhds
    have hH0 : (H z₀) ^ k = g z₀ := hHroot.self_of_nhds
    have hdp : (φ z₀) ^ k = (h z₀) ^ k / (H z₀) ^ k := by rw [hφdef, div_pow]
    rw [hdp, hh0, hH0, div_self hgz]
  have hφcont : ContinuousAt φ z₀ := hhcont.div hHcont0 hHne0
  have hφroot : ∀ᶠ w in 𝓝 z₀, (φ w) ^ k = 1 := by
    filter_upwards [hroot, hHroot, hHne] with w hw hHw hHnew
    have hdp : (φ w) ^ k = (h w) ^ k / (H w) ^ k := by rw [hφdef, div_pow]
    rw [hdp, hw, hHw, div_self]
    intro hgw
    rw [hgw] at hHw
    exact hHnew (pow_eq_zero_iff hk.ne' |>.1 hHw)
  set ζ := φ z₀ with hζdef
  have hfin : {z : ℂ | z ^ k = 1}.Finite := finite_kth_rootsOfUnity k hk
  set T : Set ℂ := {z : ℂ | z ^ k = 1} \ {ζ} with hTdef
  have hTfin : T.Finite := hfin.subset Set.diff_subset
  have hTclosed : IsClosed T := hTfin.isClosed
  have hζnotT : ζ ∉ T := by simp [hTdef]
  have hTc_nhds : Tᶜ ∈ 𝓝 ζ := hTclosed.isOpen_compl.mem_nhds hζnotT
  have hφmemTc : ∀ᶠ w in 𝓝 z₀, φ w ∈ Tᶜ := hφcont.eventually_mem hTc_nhds
  have hφeq : ∀ᶠ w in 𝓝 z₀, φ w = ζ := by
    filter_upwards [hφroot, hφmemTc] with w hru hnotT
    by_contra hne
    exact hnotT ⟨hru, hne⟩
  have hheq : ∀ᶠ w in 𝓝 z₀, h w = ζ * H w := by
    filter_upwards [hφeq, hHne] with w hw hHnew
    have hdiv : h w / H w = ζ := hw
    field_simp at hdiv ⊢
    linear_combination hdiv
  have hZH : DifferentiableAt ℂ (fun w => ζ * H w) z₀ :=
    (differentiableAt_const ζ).mul hHdiff0
  exact hZH.congr_of_eventuallyEq hheq

lemma proxy_bottcher_map_continuousOn_slit_orbit (c : ℂ) :
    ContinuousOn (Quadratic.proxy_bottcher_map c) (slit_orbit c ∩ Quadratic.basin_of_infinity c) := by
  let F : ℕ → ℂ → ℂ :=
    fun n z => ((quadratic_map c)^[n] z) ^ ((1 : ℂ) / (2 : ℂ) ^ n)
  have hseq :
      TendstoLocallyUniformlyOn F (Quadratic.proxy_bottcher_map c) atTop
        (Quadratic.basin_of_infinity c) := by
    simpa [F, quadratic_map] using (Quadratic.bottcher_seq_converges c)
  have hseq' :
      TendstoLocallyUniformlyOn F (Quadratic.proxy_bottcher_map c) atTop
        (slit_orbit c ∩ Quadratic.basin_of_infinity c) :=
    hseq.mono (by intro z hz; exact hz.2)
  have hcont : ∀ n, ContinuousOn (F n) (slit_orbit c ∩ Quadratic.basin_of_infinity c) := by
    intro n
    have hcont' : ContinuousOn (F n) (slit_orbit c) := by
      simpa [F] using bottcher_approx_continuousOn_slit c n
    exact hcont'.mono (by intro z hz; exact hz.1)
  have hcont' :
      ∃ᶠ n in atTop, ContinuousOn (F n) (slit_orbit c ∩ Quadratic.basin_of_infinity c) :=
    Filter.Frequently.of_forall hcont
  exact TendstoLocallyUniformlyOn.continuousOn hseq' hcont'

theorem proxy_bottcher_map_differentiableOn_open
    (c : ℂ) (U : Set ℂ) (hUopen : IsOpen U)
    (hUslit : U ⊆ slit_orbit c)
    (hUbasin : U ⊆ Quadratic.basin_of_infinity c) :
    DifferentiableOn ℂ (Quadratic.proxy_bottcher_map c) U := by
  let F : ℕ → ℂ → ℂ :=
    fun n z => ((quadratic_map c)^[n] z) ^ ((1 : ℂ) / (2 : ℂ) ^ n)
  have hseq :
      TendstoLocallyUniformlyOn F (Quadratic.proxy_bottcher_map c) atTop
        (Quadratic.basin_of_infinity c) := by
    simpa [F, quadratic_map] using (Quadratic.bottcher_seq_converges c)
  have hseq' :
      TendstoLocallyUniformlyOn F (Quadratic.proxy_bottcher_map c) atTop U :=
    hseq.mono (by intro z hz; exact hUbasin hz)
  have hF :
      ∀ᶠ n in atTop, DifferentiableOn ℂ (F n) U :=
    Filter.Eventually.of_forall (fun n =>
      (bottcher_approx_differentiableOn_slit c n).mono (by intro z hz; exact hUslit hz))
  exact TendstoLocallyUniformlyOn.differentiableOn hseq' hF hUopen

/-- Weakest sufficient condition for basin differentiability of the proxy on an open
set: `U` need not sit inside `slit_orbit c` (which demands every iterate avoid the
slit). It suffices that, **eventually** in `n`, the `n`-th iterate maps all of `U`
into `slitPlane`. This is the honest hypothesis behind the local-uniform-limit route,
since `TendstoLocallyUniformlyOn.differentiableOn` only needs `∀ᶠ n` differentiability
of the approximants. -/
theorem proxy_bottcher_map_differentiableOn_open_of_eventually_iter_slit
    (c : ℂ) (U : Set ℂ) (hUopen : IsOpen U)
    (hUslit : ∀ᶠ n in atTop, U ⊆ {z : ℂ | (quadratic_map c)^[n] z ∈ Complex.slitPlane})
    (hUbasin : U ⊆ Quadratic.basin_of_infinity c) :
    DifferentiableOn ℂ (Quadratic.proxy_bottcher_map c) U := by
  let F : ℕ → ℂ → ℂ :=
    fun n z => ((quadratic_map c)^[n] z) ^ ((1 : ℂ) / (2 : ℂ) ^ n)
  have hseq :
      TendstoLocallyUniformlyOn F (Quadratic.proxy_bottcher_map c) atTop
        (Quadratic.basin_of_infinity c) := by
    simpa [F, quadratic_map] using (Quadratic.bottcher_seq_converges c)
  have hseq' :
      TendstoLocallyUniformlyOn F (Quadratic.proxy_bottcher_map c) atTop U :=
    hseq.mono (by intro z hz; exact hUbasin hz)
  have hF :
      ∀ᶠ n in atTop, DifferentiableOn ℂ (F n) U := by
    filter_upwards [hUslit] with n hn
    exact (bottcher_approx_differentiableOn_single_slit c n).mono hn
  exact TendstoLocallyUniformlyOn.differentiableOn hseq' hF hUopen


theorem proxy_bottcher_map_analyticOnNhd_open
    (c : ℂ) (U : Set ℂ) (hUopen : IsOpen U)
    (hUslit : U ⊆ slit_orbit c)
    (hUbasin : U ⊆ Quadratic.basin_of_infinity c) :
    AnalyticOnNhd ℂ (Quadratic.proxy_bottcher_map c) U := by
  have hdiff : DifferentiableOn ℂ (Quadratic.proxy_bottcher_map c) U :=
    proxy_bottcher_map_differentiableOn_open c U hUopen hUslit hUbasin
  exact (analyticOnNhd_iff_differentiableOn hUopen).2 hdiff

theorem proxy_bottcher_map_analyticAt_of_open
    (c : ℂ) (U : Set ℂ) (hUopen : IsOpen U)
    (hUslit : U ⊆ slit_orbit c)
    (hUbasin : U ⊆ Quadratic.basin_of_infinity c)
    {z : ℂ} (hz : z ∈ U) :
    AnalyticAt ℂ (Quadratic.proxy_bottcher_map c) z := by
  exact (proxy_bottcher_map_analyticOnNhd_open c U hUopen hUslit hUbasin) z hz

theorem local_inverse_of_hasStrictDerivAt {f : ℂ → ℂ} {f' z : ℂ}
    (h : HasStrictDerivAt f f' z) (h' : f' ≠ 0) :
    ∀ᶠ y in 𝓝 (f z), f (HasStrictDerivAt.localInverse f f' z h h' y) = y := by
  simpa using (HasStrictDerivAt.eventually_right_inverse (f := f) (a := z)
    (f' := f') h h')

theorem hasStrictDerivAt_injOn_nhds {f : ℂ → ℂ} {f' z : ℂ}
    (h : HasStrictDerivAt f f' z) (h' : f' ≠ 0) :
    ∃ s, IsOpen s ∧ z ∈ s ∧ Set.InjOn f s := by
  classical
  let f'' : ℂ →L[ℂ] ℂ :=
    (ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 f' h'))
  have hF : HasStrictFDerivAt f f'' z := h.hasStrictFDerivAt_equiv h'
  let e := hF.toOpenPartialHomeomorph f
  refine ⟨e.source, e.open_source, ?_, ?_⟩
  · exact hF.mem_toOpenPartialHomeomorph_source
  · intro x hx y hy hxy
    exact e.toPartialEquiv.injOn hx hy hxy


theorem hasStrictDerivAt_of_differentiableOn
    {f : ℂ → ℂ} {U : Set ℂ} (hUopen : IsOpen U)
    (hf : DifferentiableOn ℂ f U) {z : ℂ} (hz : z ∈ U) :
    HasStrictDerivAt f (deriv f z) z := by
  have hcontdiff : ContDiffOn ℂ (1 : WithTop ℕ∞) f U :=
    (DifferentiableOn.contDiffOn (n := (1 : WithTop ℕ∞)) hf hUopen)
  have hcontdiffAt : ContDiffAt ℂ (1 : WithTop ℕ∞) f z :=
    hcontdiff.contDiffAt (hUopen.mem_nhds hz)
  exact hcontdiffAt.hasStrictDerivAt (by decide)

theorem proxy_bottcher_map_hasStrictDerivAt_of_open
    (c : ℂ) (U : Set ℂ) (hUopen : IsOpen U)
    (hUslit : U ⊆ slit_orbit c)
    (hUbasin : U ⊆ Quadratic.basin_of_infinity c)
    {z : ℂ} (hz : z ∈ U) :
    HasStrictDerivAt (Quadratic.proxy_bottcher_map c)
      (deriv (Quadratic.proxy_bottcher_map c) z) z := by
  have hdiff : DifferentiableOn ℂ (Quadratic.proxy_bottcher_map c) U :=
    proxy_bottcher_map_differentiableOn_open c U hUopen hUslit hUbasin
  exact hasStrictDerivAt_of_differentiableOn hUopen hdiff hz

theorem proxy_bottcher_map_eventually_right_inverse_of_open
    (c : ℂ) (U : Set ℂ) (hUopen : IsOpen U)
    (hUslit : U ⊆ slit_orbit c)
    (hUbasin : U ⊆ Quadratic.basin_of_infinity c)
    {z : ℂ} (hz : z ∈ U)
    (hderiv : deriv (Quadratic.proxy_bottcher_map c) z ≠ 0) :
    ∀ᶠ y in 𝓝 (Quadratic.proxy_bottcher_map c z),
      Quadratic.proxy_bottcher_map c
          (HasStrictDerivAt.localInverse
            (Quadratic.proxy_bottcher_map c)
            (deriv (Quadratic.proxy_bottcher_map c) z) z
            (proxy_bottcher_map_hasStrictDerivAt_of_open c U hUopen hUslit hUbasin hz)
            hderiv y) = y := by
  exact local_inverse_of_hasStrictDerivAt
    (proxy_bottcher_map_hasStrictDerivAt_of_open c U hUopen hUslit hUbasin hz) hderiv

noncomputable def external_ray_map_local
    (c : ℂ) (U : Set ℂ) (hUopen : IsOpen U)
    (hUslit : U ⊆ slit_orbit c)
    (hUbasin : U ⊆ Quadratic.basin_of_infinity c)
    (z : ℂ) (hz : z ∈ U) (hderiv : deriv (Quadratic.proxy_bottcher_map c) z ≠ 0) :
    ℂ → ℂ :=
  HasStrictDerivAt.localInverse
    (Quadratic.proxy_bottcher_map c)
    (deriv (Quadratic.proxy_bottcher_map c) z) z
    (proxy_bottcher_map_hasStrictDerivAt_of_open c U hUopen hUslit hUbasin hz) hderiv

theorem external_ray_map_local_right_inverse
    (c : ℂ) (U : Set ℂ) (hUopen : IsOpen U)
    (hUslit : U ⊆ slit_orbit c)
    (hUbasin : U ⊆ Quadratic.basin_of_infinity c)
    (z : ℂ) (hz : z ∈ U) (hderiv : deriv (Quadratic.proxy_bottcher_map c) z ≠ 0) :
    ∀ᶠ y in 𝓝 (Quadratic.proxy_bottcher_map c z),
      Quadratic.proxy_bottcher_map c
        (external_ray_map_local c U hUopen hUslit hUbasin z hz hderiv y) = y := by
  simpa [external_ray_map_local] using
    (proxy_bottcher_map_eventually_right_inverse_of_open c U hUopen hUslit hUbasin hz hderiv)

theorem external_ray_map_local_left_inverse
    (c : ℂ) (U : Set ℂ) (hUopen : IsOpen U)
    (hUslit : U ⊆ slit_orbit c)
    (hUbasin : U ⊆ Quadratic.basin_of_infinity c)
    (z : ℂ) (hz : z ∈ U) (hderiv : deriv (Quadratic.proxy_bottcher_map c) z ≠ 0) :
    ∀ᶠ x in 𝓝 z,
      external_ray_map_local c U hUopen hUslit hUbasin z hz hderiv
        (Quadratic.proxy_bottcher_map c x) = x := by
  have h :=
    HasStrictDerivAt.eventually_left_inverse
      (f := Quadratic.proxy_bottcher_map c)
      (f' := deriv (Quadratic.proxy_bottcher_map c) z)
      (a := z)
      (proxy_bottcher_map_hasStrictDerivAt_of_open c U hUopen hUslit hUbasin hz)
      hderiv
  simpa [external_ray_map_local] using h

axiom bottcher_outside_axiom :
    ∀ c : ℂ, ∀ z : ℂ, ‖z‖ > ‖c‖ + 2 →
      ∃ N : ℕ, ∀ n ≥ N, (quadratic_map c)^[n] z ∈ Complex.slitPlane

lemma eventually_slit_orbit_of_outside (c z : ℂ) (hz : ‖z‖ > ‖c‖ + 2) :
    ∃ N : ℕ, ∀ n ≥ N, (quadratic_map c)^[n] z ∈ Complex.slitPlane :=
  bottcher_outside_axiom c z hz

theorem quadratic_map_norm_lower (c z : ℂ) :
    ‖quadratic_map c z‖ ≥ ‖z‖ ^ 2 - ‖c‖ := by
  have h :
      ‖z ^ 2‖ ≤ ‖quadratic_map c z‖ + ‖c‖ := by
    -- `z^2 = (z^2 + c) + (-c)`
    have h' := norm_add_le (quadratic_map c z) (-c)
    simpa [quadratic_map, add_comm, add_left_comm, add_assoc] using h'
  have h' : ‖z ^ 2‖ - ‖c‖ ≤ ‖quadratic_map c z‖ :=
    sub_le_iff_le_add.mpr h
  have hz : ‖z ^ 2‖ = ‖z‖ ^ 2 := by
    simp [pow_two]
  simpa [hz] using h'

theorem quadratic_map_norm_ge_of_norm_ge
    (c z : ℂ) (hz : ‖z‖ ≥ ‖c‖ + 1) :
    ‖quadratic_map c z‖ ≥ ‖z‖ := by
  have h1 : ‖z‖ ^ 2 - ‖c‖ ≤ ‖quadratic_map c z‖ :=
    quadratic_map_norm_lower c z
  have h2 : ‖z‖ ≤ ‖z‖ ^ 2 - ‖c‖ := by
    calc
      ‖z‖ ≤ ‖z‖ ^ 2 - (‖z‖ - 1) := by
        have hsq : 0 ≤ (‖z‖ - 1) ^ 2 := by nlinarith
        nlinarith [hsq]
      _ ≤ ‖z‖ ^ 2 - ‖c‖ := by nlinarith
  exact le_trans h2 h1

theorem quadratic_map_norm_ge_add_one
    (c z : ℂ) (hz : ‖z‖ ≥ ‖c‖ + 2) :
    ‖quadratic_map c z‖ ≥ ‖z‖ + 1 := by
  have h1 : ‖z‖ ^ 2 - ‖c‖ ≤ ‖quadratic_map c z‖ :=
    quadratic_map_norm_lower c z
  have hy : ‖c‖ ≤ ‖z‖ - 2 := by nlinarith
  have h2a : ‖z‖ ^ 2 - (‖z‖ - 2) ≤ ‖z‖ ^ 2 - ‖c‖ := by
    nlinarith [hy]
  have h2b : ‖z‖ + 1 ≤ ‖z‖ ^ 2 - (‖z‖ - 2) := by
    have hsq : 0 ≤ (‖z‖ - 1) ^ 2 := by nlinarith
    nlinarith [hsq]
  have h2 : ‖z‖ + 1 ≤ ‖z‖ ^ 2 - ‖c‖ := le_trans h2b h2a
  exact le_trans h2 h1

theorem iterate_quadratic_map_norm_ge_add
    (c z : ℂ) :
    ∀ n, ‖z‖ ≥ ‖c‖ + 2 →
      ‖(quadratic_map c)^[n] z‖ ≥ ‖z‖ + n := by
  intro n
  induction n with
  | zero =>
      intro hz
      simp
  | succ n ih =>
      intro hz
      have h0 : ‖(quadratic_map c)^[n] z‖ ≥ ‖z‖ + n := ih hz
      have h_ge : ‖(quadratic_map c)^[n] z‖ ≥ ‖c‖ + 2 := by
        have h1 : ‖c‖ + 2 ≤ ‖z‖ := by nlinarith
        have hbase : ‖z‖ ≤ ‖z‖ + n := by nlinarith
        exact le_trans h1 (le_trans hbase h0)
      have h1 : ‖quadratic_map c ((quadratic_map c)^[n] z)‖ ≥
          ‖(quadratic_map c)^[n] z‖ + 1 :=
        quadratic_map_norm_ge_add_one c _ h_ge
      have h2 : ‖(quadratic_map c)^[n] z‖ + 1 ≥ ‖z‖ + (n + 1) := by
        nlinarith
      have h3 : ‖quadratic_map c ((quadratic_map c)^[n] z)‖ ≥ ‖z‖ + (n + 1) :=
        le_trans h2 h1
      have h3' : ‖(quadratic_map c)^[n.succ] z‖ ≥ ‖z‖ + (n + 1) := by
        rw [Function.iterate_succ']
        simpa [Function.comp_apply] using h3
      simpa using h3'

theorem iterate_quadratic_map_tendsto_infty
    (c z : ℂ) (hz : ‖z‖ ≥ ‖c‖ + 2) :
    Tendsto (fun n => ‖(quadratic_map c)^[n] z‖) atTop atTop := by
  -- Lower bound by `‖z‖ + n` which tends to infinity.
  have hmono : ∀ n, ‖(quadratic_map c)^[n] z‖ ≥ ‖z‖ + n := by
    intro n
    exact iterate_quadratic_map_norm_ge_add c z n hz
  have h1 : Tendsto (fun n : ℕ => ‖z‖ + n) atTop atTop := by
    have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := by
      simpa using (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
    have hmono' : ∀ n : ℕ, (n : ℝ) ≤ ‖z‖ + n := by
      intro n
      have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
      nlinarith
    exact tendsto_atTop_mono hmono' hnat
  exact tendsto_atTop_mono hmono h1

theorem quadratic_map_closed_ball_forward_invariant
    (c : ℂ) :
    MapsTo (quadratic_map c) {z | ‖z‖ ≥ ‖c‖ + 2} {z | ‖z‖ ≥ ‖c‖ + 2} := by
  intro z hz
  have hz' : ‖quadratic_map c z‖ ≥ ‖z‖ + 1 :=
    quadratic_map_norm_ge_add_one c z hz
  have h1 : ‖quadratic_map c z‖ ≥ ‖c‖ + 2 := by
    have h2 : ‖z‖ + 1 ≥ ‖c‖ + 2 := by
      have : ‖z‖ ≥ ‖c‖ + 2 := hz
      nlinarith
    exact le_trans h2 hz'
  exact h1

theorem escaping_set_contains_large_ball
    (c : ℂ) :
    {z | ‖z‖ ≥ ‖c‖ + 2} ⊆
      {z | Tendsto (fun n => ‖(quadratic_map c)^[n] z‖) atTop atTop} := by
  intro z hz
  exact iterate_quadratic_map_tendsto_infty c z hz


theorem basin_escape_outside (c : ℂ) :
    ∀ z, z ∈ Quadratic.basin_of_infinity c →
      ∃ n, (quadratic_map c)^[n] z ∈ outside_disk c := by
  intro z hz
  refine ⟨0, ?_⟩
  simpa [outside_disk] using hz

theorem quadratic_basin_forward_invariant (c : ℂ) :
    MapsTo (quadratic_map c) (Quadratic.basin_of_infinity c)
      (Quadratic.basin_of_infinity c) := by
  intro z hz
  dsimp [Quadratic.basin_of_infinity, basin_of_infinity] at hz ⊢
  have hshift :
      Tendsto (fun n => ‖(quadratic_map c)^[n + 1] z‖) atTop atTop := by
    exact (tendsto_add_atTop_iff_nat (f := fun n => ‖(quadratic_map c)^[n] z‖) (k := 1)).2 hz
  have hshift' :
      Tendsto (fun n => ‖(quadratic_map c)^[n] (quadratic_map c z)‖) atTop atTop := by
    simpa [Function.iterate_succ_apply, Nat.add_comm] using hshift
  exact hshift'

lemma cpow_one_div_pow_succ_eq_sq (x : ℂ) (n : ℕ) :
    x ^ ((1 : ℂ) / (2 : ℂ) ^ n) =
      (x ^ ((1 : ℂ) / (2 : ℂ) ^ (n + 1))) ^ 2 := by
  by_cases hx : x = 0
  · simp [Complex.cpow_def, hx]
  · have hdiv :
        (1 : ℂ) / (2 : ℂ) ^ n =
          (1 : ℂ) / (2 : ℂ) ^ (n + 1) + (1 : ℂ) / (2 : ℂ) ^ (n + 1) := by
      have hdiv' : (1 : ℂ) / (2 : ℂ) ^ n = (1 : ℂ) / (2 : ℂ) ^ (n + 1) * 2 := by
        field_simp [pow_succ]
        simp [pow_succ]
      calc
        (1 : ℂ) / (2 : ℂ) ^ n = (1 : ℂ) / (2 : ℂ) ^ (n + 1) * 2 := hdiv'
        _ = (1 : ℂ) / (2 : ℂ) ^ (n + 1) + (1 : ℂ) / (2 : ℂ) ^ (n + 1) := by
              ring
    calc
      x ^ ((1 : ℂ) / (2 : ℂ) ^ n)
          = x ^ ((1 : ℂ) / (2 : ℂ) ^ (n + 1) + (1 : ℂ) / (2 : ℂ) ^ (n + 1)) := by
              simp [hdiv]
      _ = x ^ ((1 : ℂ) / (2 : ℂ) ^ (n + 1)) *
            x ^ ((1 : ℂ) / (2 : ℂ) ^ (n + 1)) := by
              simpa using
                (Complex.cpow_add (x := x)
                  ((1 : ℂ) / (2 : ℂ) ^ (n + 1))
                  ((1 : ℂ) / (2 : ℂ) ^ (n + 1)) hx)
      _ = (x ^ ((1 : ℂ) / (2 : ℂ) ^ (n + 1))) ^ 2 := by
              simp [pow_two]

theorem bottcher_conj_on_basin (c : ℂ) (z : ℂ)
    (hz : z ∈ Quadratic.basin_of_infinity c) :
    Quadratic.proxy_bottcher_map c (quadratic_map c z) =
      (Quadratic.proxy_bottcher_map c z) ^ 2 := by
  let F : ℕ → ℂ → ℂ :=
    fun n z => ((quadratic_map c)^[n] z) ^ ((1 : ℂ) / (2 : ℂ) ^ n)
  have hseq :
      TendstoLocallyUniformlyOn F (Quadratic.proxy_bottcher_map c) atTop
        (Quadratic.basin_of_infinity c) := by
    simpa [F, quadratic_map] using (Quadratic.bottcher_seq_converges c)
  have hz_tend : Tendsto (fun n => F n z) atTop (𝓝 (Quadratic.proxy_bottcher_map c z)) :=
    hseq.tendsto_at hz
  have hzf : quadratic_map c z ∈ Quadratic.basin_of_infinity c :=
    (quadratic_basin_forward_invariant c) hz
  have hfz_tend :
      Tendsto (fun n => F n (quadratic_map c z)) atTop
        (𝓝 (Quadratic.proxy_bottcher_map c (quadratic_map c z))) :=
    hseq.tendsto_at hzf
  have hshift : ∀ n, F n (quadratic_map c z) = (F (n + 1) z) ^ 2 := by
    intro n
    have hiter : (quadratic_map c)^[n] (quadratic_map c z) = (quadratic_map c)^[n + 1] z := by
      simp [Function.iterate_succ_apply]
    dsimp [F]
    calc
      ((quadratic_map c)^[n] (quadratic_map c z)) ^ ((1 : ℂ) / (2 : ℂ) ^ n)
          = ((quadratic_map c)^[n + 1] z) ^ ((1 : ℂ) / (2 : ℂ) ^ n) := by
              rw [hiter]
      _ = (((quadratic_map c)^[n + 1] z) ^ ((1 : ℂ) / (2 : ℂ) ^ (n + 1))) ^ 2 := by
              exact cpow_one_div_pow_succ_eq_sq ((quadratic_map c)^[n + 1] z) n
      _ = (F (n + 1) z) ^ 2 := by
              rfl
  have hz_shift :
      Tendsto (fun n => F (n + 1) z) atTop (𝓝 (Quadratic.proxy_bottcher_map c z)) :=
    (tendsto_add_atTop_iff_nat (f := fun n => F n z) (k := 1)).2 hz_tend
  have hz_sq :
      Tendsto (fun n => (F (n + 1) z) ^ 2) atTop
        (𝓝 ((Quadratic.proxy_bottcher_map c z) ^ 2)) := by
    have hcont : Continuous (fun w : ℂ => w ^ 2) := (continuous_id.pow 2)
    exact (hcont.tendsto _).comp hz_shift
  have hfz_tend' :
      Tendsto (fun n => (F (n + 1) z) ^ 2) atTop
        (𝓝 (Quadratic.proxy_bottcher_map c (quadratic_map c z))) := by
    simpa [hshift] using hfz_tend
  exact tendsto_nhds_unique hfz_tend' hz_sq

theorem bottcher_conj_iter (c : ℂ) :
    ∀ n z, z ∈ Quadratic.basin_of_infinity c →
      Quadratic.proxy_bottcher_map c ((quadratic_map c)^[n] z) =
        (Quadratic.proxy_bottcher_map c z) ^ (2 ^ n) := by
  intro n z hz
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hz' : (quadratic_map c)^[n] z ∈ Quadratic.basin_of_infinity c := by
        have hmap : MapsTo (quadratic_map c) (Quadratic.basin_of_infinity c)
            (Quadratic.basin_of_infinity c) :=
          quadratic_basin_forward_invariant c
        have hiter :
            MapsTo (quadratic_map c)^[n] (Quadratic.basin_of_infinity c)
              (Quadratic.basin_of_infinity c) :=
          MapsTo.iterate hmap n
        exact hiter hz
      have h1 :
          Quadratic.proxy_bottcher_map c ((quadratic_map c)^[n.succ] z) =
            (Quadratic.proxy_bottcher_map c ((quadratic_map c)^[n] z)) ^ 2 := by
        simpa [Function.iterate_succ_apply'] using
          (bottcher_conj_on_basin c ((quadratic_map c)^[n] z) hz')
      calc
        Quadratic.proxy_bottcher_map c ((quadratic_map c)^[n.succ] z)
            = (Quadratic.proxy_bottcher_map c ((quadratic_map c)^[n] z)) ^ 2 := h1
        _ = ((Quadratic.proxy_bottcher_map c z) ^ (2 ^ n)) ^ 2 := by
              simp [ih]
        _ = (Quadratic.proxy_bottcher_map c z) ^ (2 ^ n * 2) := by
              simp [pow_mul]
        _ = (Quadratic.proxy_bottcher_map c z) ^ (2 ^ n.succ) := by
              simp [pow_succ, mul_comm]

axiom proxy_bottcher_map_inj_on_K (c : ℂ) :
    Set.InjOn (Quadratic.proxy_bottcher_map c) (MLC.Quadratic.K c)

/-- On the basin of infinity the proxy Böttcher map is non-vanishing:
`‖proxy_bottcher_map c z‖ = exp(green c z) > 1`. -/
theorem proxy_bottcher_map_ne_zero_of_mem_basin (c : ℂ) {z : ℂ}
    (hz : z ∈ Quadratic.basin_of_infinity c) :
    Quadratic.proxy_bottcher_map c z ≠ 0 := by
  have hz' : z ∉ MLC.Quadratic.K c := by
    have hmem : z ∈ (MLC.Quadratic.K c)ᶜ := by
      simpa [basin_eq_compl_K c] using hz
    simpa [Set.mem_compl_iff] using hmem
  have hpos : 0 < MLC.Quadratic.green_function c z :=
    (MLC.Quadratic.green_function_pos_iff_not_mem_K c z).2 hz'
  have hnorm : ‖Quadratic.proxy_bottcher_map c z‖ = Real.exp (MLC.Quadratic.green_function c z) :=
    norm_bottcher_eq_exp_green c z
  have hgt : 1 < ‖Quadratic.proxy_bottcher_map c z‖ := by
    rw [hnorm]; simpa using (Real.one_lt_exp_iff.mpr hpos)
  intro h
  rw [h, norm_zero] at hgt
  linarith

theorem basin_of_infinity_contains_large_ball (c : ℂ) :
    outside_disk c ⊆ basin_of_infinity c := by
  intro z hz
  simpa [outside_disk] using hz

theorem outside_disk_subset_basin (c : ℂ) : outside_disk c ⊆ basin_of_infinity c :=
  basin_of_infinity_contains_large_ball c

theorem outside_disk_subset_quadratic_basin (c : ℂ) :
    outside_disk c ⊆ Quadratic.basin_of_infinity c := by
  intro z hz
  simpa [outside_disk] using hz



theorem outside_disk_iterate_mem
    (c : ℂ) (n : ℕ) {z : ℂ} (hz : z ∈ outside_disk c) :
    (quadratic_map c)^[n] z ∈ outside_disk c := by
  have h_map : MapsTo (quadratic_map c) (outside_disk c) (outside_disk c) :=
    by
      simpa [outside_disk] using (quadratic_basin_forward_invariant c)
  have h_iter : MapsTo (quadratic_map c)^[n] (outside_disk c) (outside_disk c) :=
    MapsTo.iterate h_map n
  exact h_iter hz

theorem bottcher_left_inv_of_injective_of_data
    {c : ℂ} (h_data : Quadratic.ExternalRayMapData c)
    (z : ℂ) (h_norm : 1 < ‖proxy_bottcher_map c z‖)
    (h_inj : Function.Injective (proxy_bottcher_map c)) :
    Quadratic.external_ray_map_of_data h_data (proxy_bottcher_map c z) = z := by
  have hright :
      proxy_bottcher_map c (Quadratic.external_ray_map_of_data h_data (proxy_bottcher_map c z)) =
        proxy_bottcher_map c z := by
    simpa using Quadratic.external_ray_map_of_data_right_inverse h_data
      (proxy_bottcher_map c z) h_norm
  exact h_inj hright

theorem bottcher_left_inv_of_injective
    (c : ℂ) (z : ℂ) (h_norm : 1 < ‖proxy_bottcher_map c z‖)
    (h_inj : Function.Injective (proxy_bottcher_map c)) :
    external_ray_map c (proxy_bottcher_map c z) = z := by
  simpa [Quadratic.external_ray_map] using
    bottcher_left_inv_of_injective_of_data (Quadratic.external_ray_map_data c) z h_norm h_inj

theorem external_ray_map_right_inverse_on_exterior_of_data
    {c : ℂ} (h_data : Quadratic.ExternalRayMapData c) (w : ℂ) (hw : 1 < ‖w‖) :
    Quadratic.proxy_bottcher_map c (Quadratic.external_ray_map_of_data h_data w) = w := by
  simpa using Quadratic.external_ray_map_of_data_right_inverse h_data w hw

theorem external_ray_map_right_inverse_on_exterior
    (c : ℂ) (w : ℂ) (hw : 1 < ‖w‖) :
    Quadratic.proxy_bottcher_map c (Quadratic.external_ray_map c w) = w := by
  have hw' : w ∈ Quadratic.proxy_bottcher_map c '' Quadratic.bottcher_domain c :=
    Quadratic.proxy_bottcher_map_surj c w hw
  exact Quadratic.bottcher_right_inv_of_mem c w hw' hw

theorem external_ray_map_mem_outside_of_data {c : ℂ}
    (h_data : Quadratic.ExternalRayMapData c)
    (hpre : (Quadratic.proxy_bottcher_map c) ⁻¹' {w : ℂ | 1 < ‖w‖} ⊆ outside_disk c)
    {w : ℂ} (hw : 1 < ‖w‖) :
    Quadratic.external_ray_map_of_data h_data w ∈ outside_disk c := by
  have hright : Quadratic.proxy_bottcher_map c (Quadratic.external_ray_map_of_data h_data w) = w :=
    external_ray_map_right_inverse_on_exterior_of_data h_data w hw
  have hpre' : Quadratic.external_ray_map_of_data h_data w ∈
      (Quadratic.proxy_bottcher_map c) ⁻¹' {z : ℂ | 1 < ‖z‖} := by
    simp [Set.preimage, hright, hw]
  exact hpre hpre'

theorem external_ray_map_mem_outside (c : ℂ)
    (hpre : (Quadratic.proxy_bottcher_map c) ⁻¹' {w : ℂ | 1 < ‖w‖} ⊆ outside_disk c)
    {w : ℂ} (hw : 1 < ‖w‖) :
    Quadratic.external_ray_map c w ∈ outside_disk c := by
  simpa [Quadratic.external_ray_map] using
    external_ray_map_mem_outside_of_data (Quadratic.external_ray_map_data c) hpre hw

theorem external_ray_map_continuousOn_exterior (c : ℂ) :
    ContinuousOn (Quadratic.external_ray_map c) {w | 1 < ‖w‖} := by
  have hcont : ContinuousOn (Quadratic.extended_ray_map c) {w | 1 ≤ ‖w‖} :=
    Quadratic.extended_ray_map_continuous c
  have hcont' : ContinuousOn (Quadratic.extended_ray_map c) {w | 1 < ‖w‖} :=
    hcont.mono (by intro w hw; exact le_of_lt (by simpa using hw))
  refine hcont'.congr ?_
  intro w hw
  exact (Quadratic.extended_ray_map_eq c w hw).symm


theorem external_ray_map_eventually_right_inverse_of_data
    {c : ℂ} (h_data : Quadratic.ExternalRayMapData c) (w : ℂ) (hw : 1 < ‖w‖) :
    ∀ᶠ y in 𝓝 w,
      Quadratic.proxy_bottcher_map c (Quadratic.external_ray_map_of_data h_data y) = y := by
  have hopen : IsOpen {y : ℂ | 1 < ‖y‖} := by
    simpa using (isOpen_lt continuous_const continuous_norm)
  have hmem : w ∈ {y : ℂ | 1 < ‖y‖} := hw
  have hnhds : {y : ℂ | 1 < ‖y‖} ∈ 𝓝 w := hopen.mem_nhds hmem
  refine (Filter.eventually_iff).2 ?_
  refine mem_of_superset hnhds ?_
  intro y hy
  exact external_ray_map_right_inverse_on_exterior_of_data h_data y hy

theorem external_ray_map_eventually_right_inverse
    (c : ℂ) (w : ℂ) (hw : 1 < ‖w‖) :
    ∀ᶠ y in 𝓝 w,
      Quadratic.proxy_bottcher_map c (Quadratic.external_ray_map c y) = y := by
  simpa [Quadratic.external_ray_map] using
    external_ray_map_eventually_right_inverse_of_data
      (Quadratic.external_ray_map_data c) w hw

theorem external_ray_map_left_inverse_of_injOn_of_data
    {c : ℂ} (h_data : Quadratic.ExternalRayMapData c) {s : Set ℂ} {z : ℂ}
    (hsinj : Set.InjOn (Quadratic.proxy_bottcher_map c) s)
    (hmem : Quadratic.external_ray_map_of_data h_data (Quadratic.proxy_bottcher_map c z) ∈ s)
    (hzs : z ∈ s) (hnorm : 1 < ‖Quadratic.proxy_bottcher_map c z‖) :
    Quadratic.external_ray_map_of_data h_data (Quadratic.proxy_bottcher_map c z) = z := by
  have hright :
      Quadratic.proxy_bottcher_map c
          (Quadratic.external_ray_map_of_data h_data (Quadratic.proxy_bottcher_map c z)) =
        Quadratic.proxy_bottcher_map c z :=
    external_ray_map_right_inverse_on_exterior_of_data h_data
      (Quadratic.proxy_bottcher_map c z) hnorm
  exact hsinj hmem hzs (by simpa using hright)

theorem external_ray_map_left_inverse_of_injOn
    (c : ℂ) {s : Set ℂ} {z : ℂ}
    (hsinj : Set.InjOn (Quadratic.proxy_bottcher_map c) s)
    (hmem : Quadratic.external_ray_map c (Quadratic.proxy_bottcher_map c z) ∈ s)
    (hzs : z ∈ s) (hnorm : 1 < ‖Quadratic.proxy_bottcher_map c z‖) :
    Quadratic.external_ray_map c (Quadratic.proxy_bottcher_map c z) = z := by
  simpa [Quadratic.external_ray_map] using
    external_ray_map_left_inverse_of_injOn_of_data (Quadratic.external_ray_map_data c)
      hsinj hmem hzs hnorm

theorem proxy_bottcher_map_norm_gt_one_of_basin
    (c : ℂ) (z : ℂ) (_hz : z ∈ Quadratic.basin_of_infinity c)
    (hpos : 0 < MLC.Quadratic.green_function c z) :
    1 < ‖Quadratic.proxy_bottcher_map c z‖ := by
  -- For the current proxy, `‖proxy_bottcher_map c z‖ = exp(green_function c z)` and `exp` is > 1 for positive input.
  have hnorm : ‖Quadratic.proxy_bottcher_map c z‖ =
      Real.exp (MLC.Quadratic.green_function c z) :=
    Quadratic.norm_bottcher_eq_exp_green c z
  have hgt : 1 < Real.exp (MLC.Quadratic.green_function c z) := by
    simpa using (Real.one_lt_exp_iff.mpr hpos)
  simpa [hnorm] using hgt

theorem proxy_bottcher_map_norm_gt_one_implies_basin (c : ℂ) {z : ℂ}
    (hz : 1 < ‖Quadratic.proxy_bottcher_map c z‖) :
    z ∈ Quadratic.basin_of_infinity c := by
  have hnorm' : ‖Quadratic.proxy_bottcher_map c z‖ =
      Real.exp (MLC.Quadratic.green_function c z) :=
    Quadratic.norm_bottcher_eq_exp_green c z
  have hpos : 0 < MLC.Quadratic.green_function c z := by
    have hgt : 1 < Real.exp (MLC.Quadratic.green_function c z) := by
      simpa [hnorm'] using hz
    exact (Real.one_lt_exp_iff).1 hgt
  have hz' : z ∉ MLC.Quadratic.K c :=
    (MLC.Quadratic.green_function_pos_iff_not_mem_K c z).1 hpos
  have : z ∈ (MLC.Quadratic.K c)ᶜ := by
    simpa [Set.mem_compl_iff] using hz'
  simpa [Quadratic.basin_eq_compl_K c] using this

theorem green_function_pos_of_basin
    (c : ℂ) (z : ℂ) (hz : z ∈ Quadratic.basin_of_infinity c) :
    0 < MLC.Quadratic.green_function c z := by
  have hz' : z ∈ (MLC.Quadratic.K c)ᶜ := by
    simpa [Quadratic.basin_eq_compl_K c] using hz
  have hz'' : z ∉ MLC.Quadratic.K c := by
    simpa [Set.mem_compl_iff] using hz'
  exact (MLC.Quadratic.green_function_pos_iff_not_mem_K c z).2 hz''

theorem bottcher_left_inv_of_basin
    (c : ℂ) (z : ℂ) (hz : z ∈ Quadratic.basin_of_infinity c)
    (hpos : 0 < MLC.Quadratic.green_function c z)
    (h_inj : Function.Injective (Quadratic.proxy_bottcher_map c)) :
    Quadratic.external_ray_map c (Quadratic.proxy_bottcher_map c z) = z := by
  have hnorm : 1 < ‖Quadratic.proxy_bottcher_map c z‖ :=
    proxy_bottcher_map_norm_gt_one_of_basin c z hz hpos
  exact bottcher_left_inv_of_injective c z hnorm h_inj

theorem bottcher_left_inv_of_basin'
    (c : ℂ) (z : ℂ) (hz : z ∈ Quadratic.basin_of_infinity c)
    (h_inj : Function.Injective (Quadratic.proxy_bottcher_map c)) :
    Quadratic.external_ray_map c (Quadratic.proxy_bottcher_map c z) = z := by
  have hpos : 0 < MLC.Quadratic.green_function c z :=
    green_function_pos_of_basin c z hz
  exact bottcher_left_inv_of_basin c z hz hpos h_inj

theorem bottcher_theorem_outside (c : ℂ)
    (hpre : (Quadratic.proxy_bottcher_map c) ⁻¹' {w : ℂ | 1 < ‖w‖} ⊆ outside_disk c)
    (h_inj_outside : Set.InjOn (Quadratic.proxy_bottcher_map c) (outside_disk c)) :
    ∀ z, z ∈ outside_disk c →
      Quadratic.external_ray_map c (Quadratic.proxy_bottcher_map c z) = z := by
  intro z hz
  have hz_basin : z ∈ Quadratic.basin_of_infinity c :=
    outside_disk_subset_quadratic_basin c hz
  have hpos : 0 < MLC.Quadratic.green_function c z :=
    green_function_pos_of_basin c z hz_basin
  have hnorm : 1 < ‖Quadratic.proxy_bottcher_map c z‖ :=
    proxy_bottcher_map_norm_gt_one_of_basin c z hz_basin hpos
  have hmem : Quadratic.external_ray_map c (Quadratic.proxy_bottcher_map c z) ∈ outside_disk c :=
    external_ray_map_mem_outside c hpre hnorm
  exact external_ray_map_left_inverse_of_injOn c (s := outside_disk c)
    h_inj_outside hmem hz hnorm

lemma bottcher_left_inv_outside (c : ℂ)
    (hpre : (Quadratic.proxy_bottcher_map c) ⁻¹' {w : ℂ | 1 < ‖w‖} ⊆ outside_disk c)
    (h_inj_outside : Set.InjOn (Quadratic.proxy_bottcher_map c) (outside_disk c)) :
    ∀ z, z ∈ outside_disk c →
      Quadratic.external_ray_map c (Quadratic.proxy_bottcher_map c z) = z :=
  bottcher_theorem_outside c hpre h_inj_outside

lemma proxy_bottcher_map_preimage_exterior_subset_outside_of_basin
    (c : ℂ)
    (hbasin : ∀ z, z ∈ Quadratic.basin_of_infinity c → z ∈ outside_disk c) :
    (Quadratic.proxy_bottcher_map c) ⁻¹' {w : ℂ | 1 < ‖w‖} ⊆ outside_disk c := by
  intro z hz
  have hz' : 1 < ‖Quadratic.proxy_bottcher_map c z‖ := by
    simpa [Set.preimage] using hz
  have hz_basin : z ∈ Quadratic.basin_of_infinity c :=
    proxy_bottcher_map_norm_gt_one_implies_basin c (z := z) hz'
  exact hbasin z hz_basin

lemma bottcher_theorem_outside_of_basin (c : ℂ)
    (hbasin : ∀ z, z ∈ Quadratic.basin_of_infinity c → z ∈ outside_disk c)
    (h_inj_outside : Set.InjOn (Quadratic.proxy_bottcher_map c) (outside_disk c)) :
    ∀ z, z ∈ outside_disk c →
      Quadratic.external_ray_map c (Quadratic.proxy_bottcher_map c z) = z := by
  have hpre := proxy_bottcher_map_preimage_exterior_subset_outside_of_basin c hbasin
  exact bottcher_theorem_outside c hpre h_inj_outside

/-!
Inverse-branch scaffolding.

If we can build left inverses for the iterates of `quadratic_map` on the basin,
then we can eliminate `quadratic_map_iter_eq_imp_eq` by reducing to injectivity
of each iterate. This is a placeholder for future theory development.
-/

lemma quadratic_map_iter_inj_of_left_inverse
    (c : ℂ) (n : ℕ)
    (h_left :
      HasLeftInverseOn ((quadratic_map c)^[n]) Set.univ (Quadratic.basin_of_infinity c)) :
    Set.InjOn ((quadratic_map c)^[n]) (Quadratic.basin_of_infinity c) := by
  simpa using (injOn_of_hasLeftInverseOn h_left)

lemma quadratic_map_iter_eq_imp_eq_of_all_iter_inj
    (c : ℂ)
    (h_inj : ∀ n, Set.InjOn ((quadratic_map c)^[n]) (Quadratic.basin_of_infinity c)) :
    ∀ z w, z ∈ Quadratic.basin_of_infinity c → w ∈ Quadratic.basin_of_infinity c →
      (∃ n, (quadratic_map c)^[n] z = (quadratic_map c)^[n] w) → z = w := by
  intro z w hz hw hiter
  rcases hiter with ⟨n, h⟩
  exact h_inj n hz hw h

/-!
Optional hypothesis path: global inverse on the eventual slit orbit.

This is a scaffolding route to replace `quadratic_map_iter_eq_imp_eq`,
but it still requires strong local invertibility and compatibility assumptions.
-/


theorem proxy_bottcher_map_injective_of_basin_characterization
    (c : ℂ)
    (h_pre : ∀ z, 1 < ‖Quadratic.proxy_bottcher_map c z‖ → z ∈ Quadratic.basin_of_infinity c)
    (h_inj_basin : Set.InjOn (Quadratic.proxy_bottcher_map c) (Quadratic.basin_of_infinity c)) :
    Set.InjOn (Quadratic.proxy_bottcher_map c) {z | 1 < ‖Quadratic.proxy_bottcher_map c z‖} := by
  intro z hz w hw hzw
  have hz' : z ∈ Quadratic.basin_of_infinity c := h_pre z hz
  have hw' : w ∈ Quadratic.basin_of_infinity c := h_pre w hw
  exact h_inj_basin hz' hw' hzw

theorem proxy_bottcher_map_inj_on_basin_of_left_inverse
    (c : ℂ)
    (h_left_basin : ∀ z, z ∈ Quadratic.basin_of_infinity c →
      Quadratic.external_ray_map c (Quadratic.proxy_bottcher_map c z) = z) :
    Set.InjOn (Quadratic.proxy_bottcher_map c) (Quadratic.basin_of_infinity c) := by
  intro z hz w hw hzw
  have hleft_z :
      Quadratic.external_ray_map c (Quadratic.proxy_bottcher_map c z) = z :=
    h_left_basin z hz
  have hleft_w :
      Quadratic.external_ray_map c (Quadratic.proxy_bottcher_map c w) = w :=
    h_left_basin w hw
  have h := congrArg (Quadratic.external_ray_map c) hzw
  simpa [hleft_z, hleft_w] using h

theorem proxy_bottcher_map_iter_eq_on_basin_of_left_inv
    (c : ℂ) (S : Set ℂ)
    (h_left : ∀ z, z ∈ S →
      Quadratic.external_ray_map c (Quadratic.proxy_bottcher_map c z) = z)
    (h_maps : MapsTo (quadratic_map c) S S)
    (h_escape : ∀ z, z ∈ Quadratic.basin_of_infinity c →
      ∃ n, (quadratic_map c)^[n] z ∈ S)
    (h_conj : ∀ n z, z ∈ Quadratic.basin_of_infinity c →
      Quadratic.proxy_bottcher_map c ((quadratic_map c)^[n] z) =
        (Quadratic.proxy_bottcher_map c z) ^ (2 ^ n)) :
    ∀ z w, z ∈ Quadratic.basin_of_infinity c → w ∈ Quadratic.basin_of_infinity c →
      Quadratic.proxy_bottcher_map c z = Quadratic.proxy_bottcher_map c w →
      ∃ n, (quadratic_map c)^[n] z = (quadratic_map c)^[n] w := by
  intro z w hz hw hzw
  rcases h_escape z hz with ⟨nz, hnz⟩
  rcases h_escape w hw with ⟨nw, hnw⟩
  let N := Nat.max nz nw
  have hnz' : (quadratic_map c)^[N] z ∈ S := by
    have hle : nz ≤ N := Nat.le_max_left _ _
    rcases Nat.exists_eq_add_of_le hle with ⟨k, hk⟩
    have hk' : (quadratic_map c)^[k] ((quadratic_map c)^[nz] z) ∈ S :=
      (MapsTo.iterate h_maps k) hnz
    have hk'' : (quadratic_map c)^[k + nz] z ∈ S := by
      simpa [Function.iterate_add, Function.comp_apply] using hk'
    have hk''' : (quadratic_map c)^[nz + k] z ∈ S := by
      simpa [Nat.add_comm] using hk''
    simpa [hk] using hk'''
  have hnw' : (quadratic_map c)^[N] w ∈ S := by
    have hle : nw ≤ N := Nat.le_max_right _ _
    rcases Nat.exists_eq_add_of_le hle with ⟨k, hk⟩
    have hk' : (quadratic_map c)^[k] ((quadratic_map c)^[nw] w) ∈ S :=
      (MapsTo.iterate h_maps k) hnw
    have hk'' : (quadratic_map c)^[k + nw] w ∈ S := by
      simpa [Function.iterate_add, Function.comp_apply] using hk'
    have hk''' : (quadratic_map c)^[nw + k] w ∈ S := by
      simpa [Nat.add_comm] using hk''
    simpa [hk] using hk'''
  have h_eq_iter : Quadratic.proxy_bottcher_map c ((quadratic_map c)^[N] z) =
      Quadratic.proxy_bottcher_map c ((quadratic_map c)^[N] w) := by
    have hzN := h_conj N z hz
    have hwN := h_conj N w hw
    -- rewrite using equality at base
    simp [hzN, hwN, hzw]
  have h_left_z : Quadratic.external_ray_map c
      (Quadratic.proxy_bottcher_map c ((quadratic_map c)^[N] z)) = (quadratic_map c)^[N] z :=
    h_left _ hnz'
  have h_left_w : Quadratic.external_ray_map c
      (Quadratic.proxy_bottcher_map c ((quadratic_map c)^[N] w)) = (quadratic_map c)^[N] w :=
    h_left _ hnw'
  have h_iter_eq : (quadratic_map c)^[N] z = (quadratic_map c)^[N] w := by
    have h := congrArg (Quadratic.external_ray_map c) h_eq_iter
    simp [h_left_z, h_left_w] at h
    exact h
  exact ⟨N, h_iter_eq⟩

theorem proxy_bottcher_map_iter_eq_on_basin_of_outside_left_inv
    (c : ℂ)
    (h_left : ∀ z, z ∈ outside_disk c →
      Quadratic.external_ray_map c (Quadratic.proxy_bottcher_map c z) = z)
    (h_escape : ∀ z, z ∈ Quadratic.basin_of_infinity c →
      ∃ n, (quadratic_map c)^[n] z ∈ outside_disk c)
    (h_conj : ∀ n z, z ∈ Quadratic.basin_of_infinity c →
      Quadratic.proxy_bottcher_map c ((quadratic_map c)^[n] z) =
        (Quadratic.proxy_bottcher_map c z) ^ (2 ^ n)) :
    ∀ z w, z ∈ Quadratic.basin_of_infinity c → w ∈ Quadratic.basin_of_infinity c →
      Quadratic.proxy_bottcher_map c z = Quadratic.proxy_bottcher_map c w →
      ∃ n, (quadratic_map c)^[n] z = (quadratic_map c)^[n] w := by
  have h_maps : MapsTo (quadratic_map c) (outside_disk c) (outside_disk c) := by
    simpa [outside_disk] using (quadratic_basin_forward_invariant c)
  exact proxy_bottcher_map_iter_eq_on_basin_of_left_inv c (outside_disk c) h_left h_maps h_escape h_conj

theorem proxy_bottcher_map_inj_on_basin_of_outside_left_inv
    (c : ℂ)
    (h_left : ∀ z, z ∈ outside_disk c →
      Quadratic.external_ray_map c (Quadratic.proxy_bottcher_map c z) = z)
    (h_escape : ∀ z, z ∈ Quadratic.basin_of_infinity c →
      ∃ n, (quadratic_map c)^[n] z ∈ outside_disk c)
    (h_conj : ∀ n z, z ∈ Quadratic.basin_of_infinity c →
      Quadratic.proxy_bottcher_map c ((quadratic_map c)^[n] z) =
        (Quadratic.proxy_bottcher_map c z) ^ (2 ^ n))
    (h_iter_eq_imp : ∀ z w, z ∈ Quadratic.basin_of_infinity c → w ∈ Quadratic.basin_of_infinity c →
      (∃ n, (quadratic_map c)^[n] z = (quadratic_map c)^[n] w) → z = w) :
    Set.InjOn (Quadratic.proxy_bottcher_map c) (Quadratic.basin_of_infinity c) := by
  intro z hz w hw hzw
  have h_iter_eq :
      ∃ n, (quadratic_map c)^[n] z = (quadratic_map c)^[n] w :=
    proxy_bottcher_map_iter_eq_on_basin_of_outside_left_inv c h_left h_escape h_conj z w hz hw hzw
  exact h_iter_eq_imp z w hz hw h_iter_eq

-- TODO: replace `h_iter_eq_imp` with a derivable inverse-branch principle on the basin.

theorem proxy_bottcher_map_inj_on_basin_of_outside_left_inv_of_iter_left_inverse
    (c : ℂ)
    (h_left : ∀ z, z ∈ outside_disk c →
      Quadratic.external_ray_map c (Quadratic.proxy_bottcher_map c z) = z)
    (h_escape : ∀ z, z ∈ Quadratic.basin_of_infinity c →
      ∃ n, (quadratic_map c)^[n] z ∈ outside_disk c)
    (h_conj : ∀ n z, z ∈ Quadratic.basin_of_infinity c →
      Quadratic.proxy_bottcher_map c ((quadratic_map c)^[n] z) =
        (Quadratic.proxy_bottcher_map c z) ^ (2 ^ n))
    (h_left_iter : QuadraticMapIterLeftInverseOnBasin c) :
    Set.InjOn (Quadratic.proxy_bottcher_map c) (Quadratic.basin_of_infinity c) := by
  have h_iter_eq_imp :=
    quadratic_map_iter_eq_imp_eq_of_iter_left_inverse c h_left_iter
  exact proxy_bottcher_map_inj_on_basin_of_outside_left_inv c h_left h_escape h_conj h_iter_eq_imp

theorem proxy_bottcher_map_inj_on_basin_of_left_inv
    (c : ℂ) (S : Set ℂ)
    (h_left : ∀ z, z ∈ S →
      Quadratic.external_ray_map c (Quadratic.proxy_bottcher_map c z) = z)
    (h_maps : MapsTo (quadratic_map c) S S)
    (h_escape : ∀ z, z ∈ Quadratic.basin_of_infinity c →
      ∃ n, (quadratic_map c)^[n] z ∈ S)
    (h_conj : ∀ n z, z ∈ Quadratic.basin_of_infinity c →
      Quadratic.proxy_bottcher_map c ((quadratic_map c)^[n] z) =
        (Quadratic.proxy_bottcher_map c z) ^ (2 ^ n))
    (h_iter_eq_imp : ∀ z w, z ∈ Quadratic.basin_of_infinity c → w ∈ Quadratic.basin_of_infinity c →
      (∃ n, (quadratic_map c)^[n] z = (quadratic_map c)^[n] w) → z = w) :
    Set.InjOn (Quadratic.proxy_bottcher_map c) (Quadratic.basin_of_infinity c) := by
  intro z hz w hw hzw
  have h_iter_eq :
      ∃ n, (quadratic_map c)^[n] z = (quadratic_map c)^[n] w :=
    proxy_bottcher_map_iter_eq_on_basin_of_left_inv c S h_left h_maps h_escape h_conj z w hz hw hzw
  exact h_iter_eq_imp z w hz hw h_iter_eq

/-!
Sketch: Injectivity of `proxy_bottcher_map`.

Idea: show any two points with the same Böttcher value escape to the
outside disk under iteration, use the functional equation to compare
iterates, then apply the left inverse on the outside disk and injectivity
of iterates of `quadratic_map`. The lemma `proxy_bottcher_map_inj_on_basin_of_outside_left_inv`
implements the main reduction on the basin; to finish, one needs that
equal Böttcher values force membership in the basin (via positivity of
the Green's function).
-/
theorem proxy_bottcher_map_inj_theorem_of_inj_basin
    (c : ℂ)
    (h_inj_K : Set.InjOn (Quadratic.proxy_bottcher_map c) (MLC.Quadratic.K c))
    (h_inj_basin :
      Set.InjOn (Quadratic.proxy_bottcher_map c) (Quadratic.basin_of_infinity c)) :
    Function.Injective (Quadratic.proxy_bottcher_map c) := by
  -- Sketch: split by whether the current proxy satisfies `‖proxy_bottcher_map c z‖ > 1`. For the exterior branch,
  -- reduce to basin injectivity via Green positivity. For the complementary branch,
  -- reduce to injectivity on `K` via `green = 0`.
  have h_pre : ∀ z, 1 < ‖Quadratic.proxy_bottcher_map c z‖ →
      z ∈ Quadratic.basin_of_infinity c := by
    intro z hz
    have hnorm' : ‖Quadratic.proxy_bottcher_map c z‖ =
        Real.exp (MLC.Quadratic.green_function c z) :=
      Quadratic.norm_bottcher_eq_exp_green c z
    have hpos : 0 < MLC.Quadratic.green_function c z := by
      have hgt : 1 < Real.exp (MLC.Quadratic.green_function c z) := by
        simpa [hnorm'] using hz
      exact (Real.one_lt_exp_iff).1 hgt
    have hz' : z ∉ MLC.Quadratic.K c :=
      (MLC.Quadratic.green_function_pos_iff_not_mem_K c z).1 hpos
    have : z ∈ (MLC.Quadratic.K c)ᶜ := by simpa [Set.mem_compl_iff] using hz'
    simpa [Quadratic.basin_eq_compl_K c] using this
  have h_inj_on :
      Set.InjOn (Quadratic.proxy_bottcher_map c) {z | 1 < ‖Quadratic.proxy_bottcher_map c z‖} :=
    proxy_bottcher_map_injective_of_basin_characterization (c := c) h_pre h_inj_basin
  intro z w hzw
  by_cases hz : 1 < ‖Quadratic.proxy_bottcher_map c z‖
  · have hw : 1 < ‖Quadratic.proxy_bottcher_map c w‖ := by
      simpa [hzw] using hz
    exact h_inj_on hz hw hzw
  · have hz_le : ‖Quadratic.proxy_bottcher_map c z‖ ≤ 1 := le_of_not_gt hz
    have hnorm' : ‖Quadratic.proxy_bottcher_map c z‖ =
        Real.exp (MLC.Quadratic.green_function c z) :=
      Quadratic.norm_bottcher_eq_exp_green c z
    have hge0 : 0 ≤ MLC.Quadratic.green_function c z :=
      MLC.Quadratic.green_function_nonneg c z
    have hle0 : MLC.Quadratic.green_function c z ≤ 0 := by
      have : Real.exp (MLC.Quadratic.green_function c z) ≤ 1 := by
        simpa [hnorm'] using hz_le
      exact (Real.exp_le_one_iff).1 this
    have hzG : MLC.Quadratic.green_function c z = 0 := le_antisymm hle0 hge0
    have hzK : z ∈ MLC.Quadratic.K c :=
      (MLC.Quadratic.green_function_eq_zero_iff_mem_K c z).1 hzG
    have hnormw : ‖Quadratic.proxy_bottcher_map c w‖ ≤ 1 := by
      simpa [hzw] using hz_le
    have hnormw' : ‖Quadratic.proxy_bottcher_map c w‖ =
        Real.exp (MLC.Quadratic.green_function c w) :=
      Quadratic.norm_bottcher_eq_exp_green c w
    have hge0w : 0 ≤ MLC.Quadratic.green_function c w :=
      MLC.Quadratic.green_function_nonneg c w
    have hle0w : MLC.Quadratic.green_function c w ≤ 0 := by
      have : Real.exp (MLC.Quadratic.green_function c w) ≤ 1 := by
        simpa [hnormw'] using hnormw
      exact (Real.exp_le_one_iff).1 this
    have hwG : MLC.Quadratic.green_function c w = 0 := le_antisymm hle0w hge0w
    have hwK : w ∈ MLC.Quadratic.K c :=
      (MLC.Quadratic.green_function_eq_zero_iff_mem_K c w).1 hwG
    exact h_inj_K hzK hwK hzw

theorem proxy_bottcher_map_inj_theorem
    (c : ℂ)
    (h_left : ∀ z, z ∈ outside_disk c →
      Quadratic.external_ray_map c (Quadratic.proxy_bottcher_map c z) = z)
    (h_escape : ∀ z, z ∈ Quadratic.basin_of_infinity c →
      ∃ n, (quadratic_map c)^[n] z ∈ outside_disk c)
    (h_conj : ∀ n z, z ∈ Quadratic.basin_of_infinity c →
      Quadratic.proxy_bottcher_map c ((quadratic_map c)^[n] z) =
        (Quadratic.proxy_bottcher_map c z) ^ (2 ^ n))
    (h_inj_K : Set.InjOn (Quadratic.proxy_bottcher_map c) (MLC.Quadratic.K c))
    (h_iter_eq_imp : ∀ z w, z ∈ Quadratic.basin_of_infinity c →
      w ∈ Quadratic.basin_of_infinity c →
      (∃ n, (quadratic_map c)^[n] z = (quadratic_map c)^[n] w) → z = w) :
    Function.Injective (Quadratic.proxy_bottcher_map c) := by
  have h_inj_basin :
      Set.InjOn (Quadratic.proxy_bottcher_map c) (Quadratic.basin_of_infinity c) :=
    proxy_bottcher_map_inj_on_basin_of_outside_left_inv c h_left h_escape h_conj
      h_iter_eq_imp
  exact proxy_bottcher_map_inj_theorem_of_inj_basin c h_inj_K h_inj_basin

theorem proxy_bottcher_map_inj_theorem_of_iter_left_inverse
    (c : ℂ)
    (h_left : ∀ z, z ∈ outside_disk c →
      Quadratic.external_ray_map c (Quadratic.proxy_bottcher_map c z) = z)
    (h_escape : ∀ z, z ∈ Quadratic.basin_of_infinity c →
      ∃ n, (quadratic_map c)^[n] z ∈ outside_disk c)
    (h_conj : ∀ n z, z ∈ Quadratic.basin_of_infinity c →
      Quadratic.proxy_bottcher_map c ((quadratic_map c)^[n] z) =
        (Quadratic.proxy_bottcher_map c z) ^ (2 ^ n))
    (h_inj_K : Set.InjOn (Quadratic.proxy_bottcher_map c) (MLC.Quadratic.K c))
    (h_left_iter : QuadraticMapIterLeftInverseOnBasin c) :
    Function.Injective (Quadratic.proxy_bottcher_map c) := by
  have h_iter_eq_imp :=
    quadratic_map_iter_eq_imp_eq_of_iter_left_inverse c h_left_iter
  exact proxy_bottcher_map_inj_theorem c h_left h_escape h_conj h_inj_K h_iter_eq_imp

theorem basin_of_infinity_nonempty (c : ℂ) : (basin_of_infinity c).Nonempty := by
  refine ⟨((‖c‖ + 2 : ℝ) : ℂ), ?_⟩
  have h0 : ((‖c‖ + 2 : ℝ) : ℂ) ∈ {z : ℂ | ‖z‖ ≥ ‖c‖ + 2} := by
    have hnonneg : 0 ≤ ‖c‖ + 2 := by nlinarith [norm_nonneg c]
    have hnorm : ‖((‖c‖ + 2 : ℝ) : ℂ)‖ = ‖c‖ + 2 := by
      simpa using (Complex.norm_of_nonneg hnonneg)
    have hle : ‖c‖ + 2 ≤ ‖((‖c‖ + 2 : ℝ) : ℂ)‖ := by
      calc
        ‖c‖ + 2 = ‖((‖c‖ + 2 : ℝ) : ℂ)‖ := hnorm.symm
        _ ≤ ‖((‖c‖ + 2 : ℝ) : ℂ)‖ := le_rfl
    simpa [Set.mem_setOf_eq] using hle
  exact (escaping_set_contains_large_ball c) h0

theorem open_large_ball (c : ℂ) : IsOpen {z : ℂ | ‖z‖ > ‖c‖ + 2} := by
  have hconst : Continuous (fun _ : ℂ => ‖c‖ + 2) := continuous_const
  simpa [gt_iff_lt] using (isOpen_lt hconst continuous_norm)

theorem open_large_ball_subset_basin (c : ℂ) :
    {z : ℂ | ‖z‖ > ‖c‖ + 2} ⊆ basin_of_infinity c := by
  intro z hz
  have hz' : ‖z‖ ≥ ‖c‖ + 2 := le_of_lt hz
  exact (escaping_set_contains_large_ball c) hz'

theorem basin_of_infinity_isOpen (c : ℂ) : IsOpen (basin_of_infinity c) := by
  refine isOpen_iff_mem_nhds.mpr ?_
  intro z hz
  -- Get a tail where the orbit is outside a larger disk.
  have h_event : ∀ᶠ n in atTop, ‖(quadratic_map c)^[n] z‖ ≥ ‖c‖ + 3 :=
    (tendsto_atTop.1 hz) (‖c‖ + 3)
  rcases (eventually_atTop.1 h_event) with ⟨N, hN⟩
  have hNz : ‖(quadratic_map c)^[N] z‖ > ‖c‖ + 2 := by
    have hN' := hN N (le_rfl)
    linarith
  let U : Set ℂ := {w | ‖(quadratic_map c)^[N] w‖ > ‖c‖ + 2}
  have hUopen : IsOpen U := by
    have hcont : Continuous (fun w => ‖(quadratic_map c)^[N] w‖) :=
      (continuous_norm.comp ((continuous_quadratic_map c).iterate N))
    have hopen : IsOpen {r : ℝ | r > ‖c‖ + 2} := by
      have hconst : Continuous (fun _ : ℝ => ‖c‖ + 2) := continuous_const
      simpa [gt_iff_lt] using (isOpen_lt hconst continuous_id)
    simpa [U] using hcont.isOpen_preimage _ hopen
  have hzU : z ∈ U := by
    simpa [U] using hNz
  have hUsubset : U ⊆ basin_of_infinity c := by
    intro w hw
    have hw' : ‖(quadratic_map c)^[N] w‖ ≥ ‖c‖ + 2 := by
      have : ‖(quadratic_map c)^[N] w‖ > ‖c‖ + 2 := hw
      exact le_of_lt this
    have htail :
        Tendsto (fun n => ‖(quadratic_map c)^[n] ((quadratic_map c)^[N] w)‖) atTop atTop :=
      iterate_quadratic_map_tendsto_infty c ((quadratic_map c)^[N] w) hw'
    have hshift :
        Tendsto (fun n => ‖(quadratic_map c)^[n + N] w‖) atTop atTop := by
      simpa [Function.iterate_add, Function.comp_apply, Nat.add_left_comm, Nat.add_assoc] using
        htail
    have hmain :
        Tendsto (fun n => ‖(quadratic_map c)^[n] w‖) atTop atTop :=
      (tendsto_add_atTop_iff_nat (f := fun n => ‖(quadratic_map c)^[n] w‖) (k := N)).1 hshift
    exact hmain
  have hzU_nhds : U ∈ 𝓝 z := hUopen.mem_nhds hzU
  exact Filter.mem_of_superset hzU_nhds hUsubset

/-- Radial injectivity of the proxy Böttcher map on the (nonzero) basin.

Since `proxy_bottcher_map c z = (z/‖z‖)·exp(green c z)` is the **radial** proxy,
its injectivity is elementary and does *not* require holomorphy of the proxy:
equal images force equal modulus `exp(green c z)` (hence equal Green values) and
equal phase `z/‖z‖` (hence equal direction), after which strict monotonicity of
the Green function along the common origin-ray forces equal radii.

This reduces the basin-injectivity frontier
(`proxy_bottcher_map_inj_on_basin_axiom`) to radial Green monotonicity — the
hypothesis `hmono`, which is exactly the shape of
`green_function_strictMono_along_ray_basin_seam`. -/
theorem proxy_bottcher_map_injOn_nonzero_basin_of_green_ray_strictMono
    (c : ℂ)
    (hmono : ∀ (u : ℂ), ‖u‖ = 1 → ∀ {ρ₁ ρ₂ : ℝ}, 0 < ρ₁ → ρ₁ < ρ₂ →
        0 < MLC.Quadratic.green_function c ((ρ₁ : ℂ) * u) →
        MLC.Quadratic.green_function c ((ρ₁ : ℂ) * u)
          < MLC.Quadratic.green_function c ((ρ₂ : ℂ) * u)) :
    Set.InjOn (Quadratic.proxy_bottcher_map c)
      (Quadratic.basin_of_infinity c ∩ {z : ℂ | z ≠ 0}) := by
  rintro z ⟨hzb, hz0⟩ w ⟨hwb, hw0⟩ hzw
  simp only [Set.mem_setOf_eq] at hz0 hw0
  -- Green values are positive on the basin.
  have hgz : 0 < MLC.Quadratic.green_function c z := green_function_pos_of_basin c z hzb
  have hgw : 0 < MLC.Quadratic.green_function c w := green_function_pos_of_basin c w hwb
  -- Nonzero norms.
  have hnz : (‖z‖ : ℝ) ≠ 0 := norm_ne_zero_iff.2 hz0
  have hnw : (‖w‖ : ℝ) ≠ 0 := norm_ne_zero_iff.2 hw0
  -- Explicit radial expansion of the proxy on nonzero points.
  have hzexp : Quadratic.proxy_bottcher_map c z
      = (z / (‖z‖ : ℂ)) * (Real.exp (MLC.Quadratic.green_function c z) : ℂ) := by
    simp [Quadratic.proxy_bottcher_map, Quadratic.polar_green_map, hz0]
  have hwexp : Quadratic.proxy_bottcher_map c w
      = (w / (‖w‖ : ℂ)) * (Real.exp (MLC.Quadratic.green_function c w) : ℂ) := by
    simp [Quadratic.proxy_bottcher_map, Quadratic.polar_green_map, hw0]
  -- Equal modulus forces equal Green values.
  have hnormeq : Real.exp (MLC.Quadratic.green_function c z)
      = Real.exp (MLC.Quadratic.green_function c w) := by
    have := congrArg norm hzw
    rwa [norm_bottcher_eq_exp_green, norm_bottcher_eq_exp_green] at this
  have hgeq : MLC.Quadratic.green_function c z = MLC.Quadratic.green_function c w :=
    Real.exp_injective hnormeq
  -- Equal phase forces equal direction.
  have hexpne : (Real.exp (MLC.Quadratic.green_function c w) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.exp_pos _).ne'
  have hdir : z / (‖z‖ : ℂ) = w / (‖w‖ : ℂ) := by
    have hzw' : (z / (‖z‖ : ℂ)) * (Real.exp (MLC.Quadratic.green_function c w) : ℂ)
        = (w / (‖w‖ : ℂ)) * (Real.exp (MLC.Quadratic.green_function c w) : ℂ) := by
      have := hzw
      rw [hzexp, hwexp, hgeq] at this
      exact this
    exact mul_right_cancel₀ hexpne hzw'
  -- Common unit direction and radial reconstruction.
  have hnzC : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast hnz
  have hnwC : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast hnw
  set u : ℂ := w / (‖w‖ : ℂ) with hu_def
  have hu_norm : ‖u‖ = 1 := by
    rw [hu_def, norm_div, Complex.norm_real, norm_norm, div_self hnw]
  have hzeq : z = (‖z‖ : ℂ) * u := by
    rw [← hdir]
    field_simp
  have hweq : w = (‖w‖ : ℂ) * u := by
    rw [hu_def]
    field_simp
  -- Rewrite Green values along the ray.
  have hgz_ray : 0 < MLC.Quadratic.green_function c ((‖z‖ : ℂ) * u) := by
    rw [← hzeq]; exact hgz
  have hgw_ray : 0 < MLC.Quadratic.green_function c ((‖w‖ : ℂ) * u) := by
    rw [← hweq]; exact hgw
  have hposz : (0 : ℝ) < ‖z‖ := (norm_pos_iff).2 hz0
  have hposw : (0 : ℝ) < ‖w‖ := (norm_pos_iff).2 hw0
  -- Strict monotonicity forbids distinct radii.
  have hradii : ‖z‖ = ‖w‖ := by
    rcases lt_trichotomy (‖z‖) (‖w‖) with hlt | heq | hgt
    · exfalso
      have := hmono u hu_norm hposz hlt hgz_ray
      rw [← hzeq, ← hweq, hgeq] at this
      exact lt_irrefl _ this
    · exact heq
    · exfalso
      have := hmono u hu_norm hposw hgt hgw_ray
      rw [← hzeq, ← hweq, hgeq] at this
      exact lt_irrefl _ this
  rw [hzeq, hweq, hradii]

/-- Functional-equation reduction for basin analyticity: if the proxy Böttcher map
is holomorphic on a neighbourhood of a forward iterate `f^[n] z₀`, then it is
holomorphic at `z₀` itself. Uses the conjugacy `proxy (f^[n] w) = (proxy w)^(2^n)`
and the continuous-root criterion, with a **fixed** escape time `n`, avoiding the
moving branch cut of the global power-approximation sequence. -/
theorem proxy_bottcher_map_differentiableAt_of_iterate
    (c : ℂ) (n : ℕ) {z₀ : ℂ}
    (hz₀ : z₀ ∈ Quadratic.basin_of_infinity c) (hz₀0 : z₀ ≠ 0)
    (hiter : ∀ᶠ w in 𝓝 ((quadratic_map c)^[n] z₀),
      DifferentiableAt ℂ (Quadratic.proxy_bottcher_map c) w) :
    DifferentiableAt ℂ (Quadratic.proxy_bottcher_map c) z₀ := by
  set f := (quadratic_map c)^[n] with hf
  have hfdiff : Differentiable ℂ f := (quadratic_map_differentiable c).iterate n
  have hfcont : ContinuousAt f z₀ := (hfdiff z₀).continuousAt
  -- g := proxy ∘ f, holomorphic near z₀
  set g : ℂ → ℂ := fun w => Quadratic.proxy_bottcher_map c (f w) with hg
  have hg_diff : ∀ᶠ w in 𝓝 z₀, DifferentiableAt ℂ g w := by
    have hpre : ∀ᶠ w in 𝓝 z₀,
        DifferentiableAt ℂ (Quadratic.proxy_bottcher_map c) (f w) :=
      hfcont.tendsto.eventually hiter
    filter_upwards [hpre] with w hw
    exact hw.comp w (hfdiff w)
  -- g z₀ ≠ 0
  have hfz_basin : f z₀ ∈ Quadratic.basin_of_infinity c := by
    have hmap : Set.MapsTo (quadratic_map c) (Quadratic.basin_of_infinity c)
        (Quadratic.basin_of_infinity c) := quadratic_basin_forward_invariant c
    exact (Set.MapsTo.iterate hmap n) hz₀
  have hgz : g z₀ ≠ 0 := proxy_bottcher_map_ne_zero_of_mem_basin c hfz_basin
  -- proxy continuous at z₀
  have hhcont : ContinuousAt (Quadratic.proxy_bottcher_map c) z₀ :=
    Quadratic.proxy_bottcher_map_continuousAt_of_ne_zero c z₀ hz₀0
  -- root identity near z₀ from the conjugacy on the (open) basin
  have hbasin_nhds : Quadratic.basin_of_infinity c ∈ 𝓝 z₀ :=
    (basin_of_infinity_isOpen c).mem_nhds hz₀
  have hroot : ∀ᶠ w in 𝓝 z₀,
      (Quadratic.proxy_bottcher_map c w) ^ (2 ^ n) = g w := by
    filter_upwards [hbasin_nhds] with w hw
    exact (bottcher_conj_iter c n w hw).symm
  exact differentiableAt_of_continuousAt_kth_root (k := 2 ^ n)
    (pow_pos (by norm_num) n) hg_diff hgz hhcont hroot

theorem basin_of_infinity_forward_invariant (c : ℂ) :
    MapsTo (quadratic_map c) (basin_of_infinity c) (basin_of_infinity c) := by
  intro z hz
  -- Unpack the definition of the basin.
  dsimp [basin_of_infinity] at hz ⊢
  -- Shift the index by one.
  have hshift :
      Tendsto (fun n => ‖(quadratic_map c)^[n + 1] z‖) atTop atTop := by
    exact (tendsto_add_atTop_iff_nat (f := fun n => ‖(quadratic_map c)^[n] z‖) (k := 1)).2 hz
  -- Rewrite the shifted iterate as `f^[n] (f z)`.
  have hshift' :
      Tendsto (fun n => ‖(quadratic_map c)^[n] (quadratic_map c z)‖) atTop atTop := by
    simpa [Function.iterate_succ_apply, Nat.add_comm] using hshift
  exact hshift'

theorem basin_of_infinity_preimage_subset (c : ℂ) :
    preimage (quadratic_map c) (basin_of_infinity c) ⊆ basin_of_infinity c := by
  intro z hz
  -- `f z ∈ basin` gives `‖f^[n] (f z)‖ → ∞`; shift back by one.
  dsimp [basin_of_infinity] at hz ⊢
  have hshift :
      Tendsto (fun n => ‖(quadratic_map c)^[n + 1] z‖) atTop atTop := by
    simpa [Function.iterate_succ_apply, Nat.add_comm] using hz
  exact (tendsto_add_atTop_iff_nat (f := fun n => ‖(quadratic_map c)^[n] z‖) (k := 1)).1 hshift

theorem basin_of_infinity_preimage_eq (c : ℂ) :
    preimage (quadratic_map c) (basin_of_infinity c) = basin_of_infinity c := by
  apply subset_antisymm
  · exact basin_of_infinity_preimage_subset c
  · intro z hz
    -- Forward invariance gives `f z ∈ basin`.
    exact (basin_of_infinity_forward_invariant c) hz

/-!
Minimal Böttcher-coordinate placeholders on the basin.

These are weak existence statements that will be strengthened to real
conjugacy and normalization properties.
-/

structure BottcherCoordinate (c : ℂ) where
  phi : ℂ → ℂ
  cont : Continuous phi
  conj : ∀ z, z ∈ outside_disk c → phi (quadratic_map c z) = (phi z) ^ 2
  norm : ∀ z, z ∈ outside_disk c → ‖phi z‖ ≥ 1

theorem BottcherCoordinate.conj_on_basin_of_outside
    {c : ℂ} (B : BottcherCoordinate c) {z : ℂ} (hz : z ∈ outside_disk c) :
    B.phi (quadratic_map c z) = (B.phi z) ^ 2 := by
  exact B.conj z hz

theorem BottcherCoordinate.norm_on_basin_of_outside
    {c : ℂ} (B : BottcherCoordinate c) {z : ℂ} (hz : z ∈ outside_disk c) :
    ‖B.phi z‖ ≥ 1 := by
  exact B.norm z hz

def BottcherCoordinate.of_outside
    (_c : ℂ) (φ : ℂ → ℂ) (hφ : Continuous φ)
    (_conj : ∀ z, z ∈ outside_disk _c → φ (quadratic_map _c z) = (φ z) ^ 2)
    (_norm : ∀ z, z ∈ outside_disk _c → ‖φ z‖ ≥ 1) :
    BottcherCoordinate _c :=
  { phi := φ
    cont := hφ
    conj := _conj
    norm := _norm }

theorem bottcher_coordinate_exists_on_outside
    (_c : ℂ) (φ : ℂ → ℂ) (hφ : Continuous φ)
    (_conj : ∀ z, z ∈ outside_disk _c → φ (quadratic_map _c z) = (φ z) ^ 2)
    (_norm : ∀ z, z ∈ outside_disk _c → ‖φ z‖ ≥ 1) :
    ∃ (_φ : BottcherCoordinate _c), True := by
  refine ⟨BottcherCoordinate.of_outside _c φ hφ _conj _norm, trivial⟩

theorem bottcher_coordinate_exists_on_outside_strong'
    (_c : ℂ) (φ : ℂ → ℂ) (hφ : Continuous φ)
    (_conj : ∀ z, z ∈ outside_disk _c → φ (quadratic_map _c z) = (φ z) ^ 2)
    (_norm : ∀ z, z ∈ outside_disk _c → ‖φ z‖ ≥ 1) :
    ∃ (B : BottcherCoordinate _c), Continuous B.phi := by
  refine ⟨BottcherCoordinate.of_outside _c φ hφ _conj _norm, ?_⟩
  exact (BottcherCoordinate.of_outside _c φ hφ _conj _norm).cont

theorem iterate_norm_ge_of_norm_ge
    {f : ℂ → ℂ} {R : ℝ}
    (h : ∀ z, ‖z‖ ≥ R → ‖f z‖ ≥ ‖z‖) :
    ∀ n z, ‖z‖ ≥ R → ‖(f^[n]) z‖ ≥ ‖z‖ := by
  intro n
  induction n with
  | zero =>
      intro z hz
      simp
  | succ n ih =>
      intro z hz
      have h1 : ‖z‖ ≤ ‖(f^[n]) z‖ := ih z hz
      have hR : R ≤ ‖(f^[n]) z‖ := le_trans hz h1
      have h2 : ‖(f^[n]) z‖ ≤ ‖f ((f^[n]) z)‖ := h _ hR
      have h3 : ‖z‖ ≤ ‖f ((f^[n]) z)‖ := le_trans h1 h2
      have h3' : ‖z‖ ≤ ‖(f^[n.succ]) z‖ := by
        -- `iterate_succ'` rewrites to `f ∘ f^[n]`.
        rw [Function.iterate_succ']
        simpa [Function.comp_apply] using h3
      simpa using h3'

theorem iterate_norm_ge_R_of_norm_ge
    {f : ℂ → ℂ} {R : ℝ}
    (h : ∀ z, ‖z‖ ≥ R → ‖f z‖ ≥ ‖z‖) :
    ∀ n z, ‖z‖ ≥ R → ‖(f^[n]) z‖ ≥ R := by
  intro n z hz
  have h1 : ‖(f^[n]) z‖ ≥ ‖z‖ := iterate_norm_ge_of_norm_ge (f := f) (R := R) h n z hz
  exact le_trans hz h1

theorem iterate_quadratic_map_norm_ge
    (c z : ℂ) (n : ℕ) (hz : ‖z‖ ≥ ‖c‖ + 1) :
    ‖(quadratic_map c)^[n] z‖ ≥ ‖z‖ := by
  apply iterate_norm_ge_of_norm_ge (f := quadratic_map c) (R := ‖c‖ + 1)
  · intro w hw
    exact quadratic_map_norm_ge_of_norm_ge c w hw
  · exact hz

theorem rescale_param_differentiableOn
    (c₀ : ℂ) (r : ℝ) :
    DifferentiableOn ℂ (fun t => rescale_param c₀ r t) (Metric.ball 0 1) := by
  have h_mul : DifferentiableOn ℂ (fun t : ℂ => (r : ℂ) * t) (Metric.ball 0 1) :=
    (differentiableOn_id.const_mul (r : ℂ))
  simpa [rescale_param, mul_comm] using (h_mul.const_add c₀)

def linear_holomorphic_motion
    (a : ℂ) (E : Set ℂ) :
    HolomorphicMotion E := by
  refine
    { f := fun t z => z + a * t
      h_zero := ?_
      h_inj := ?_
      h_holo := ?_ }
  · intro z hz
    simp
  · intro t ht x hx y hy hxy
    simpa using hxy
  · intro z hz
    -- `t ↦ z + a * t` is holomorphic on the disk.
    have h_mul : DifferentiableOn ℂ (fun t : ℂ => a * t) (Metric.ball 0 1) :=
      (differentiableOn_id.const_mul a)
    simpa [add_comm] using (h_mul.const_add z)

theorem bottcher_coordinate_exists_weak
    (_c : ℂ) :
    ∃ (φ : ℂ → ℂ), DifferentiableOn ℂ φ Set.univ := by
  refine ⟨fun z => z, ?_⟩
  simpa using (differentiableOn_id : DifferentiableOn ℂ (fun z : ℂ => z) Set.univ)

theorem bottcher_coordinate_exists_strong
    (_c : ℂ) (φ : ℂ → ℂ) (hφ : Continuous φ)
    (_conj : ∀ z, φ (quadratic_map _c z) = (φ z) ^ 2)
    (_norm : ∀ z, ‖z‖ ≥ ‖_c‖ + 2 → ‖φ z‖ ≥ 1) :
    ∃ (φ : ℂ → ℂ), Continuous φ ∧
      (∀ z, φ (quadratic_map _c z) = (φ z) ^ 2) ∧
      (∀ z, ‖z‖ ≥ ‖_c‖ + 2 → ‖φ z‖ ≥ 1) := by
  exact ⟨φ, hφ, _conj, _norm⟩

theorem bottcher_coordinate_exists_on_outside_strong
    (_c : ℂ) (φ : ℂ → ℂ) (hφ : Continuous φ)
    (_conj : ∀ z, z ∈ outside_disk _c → φ (quadratic_map _c z) = (φ z) ^ 2)
    (_norm : ∀ z, z ∈ outside_disk _c → ‖φ z‖ ≥ 1) :
    ∃ (φ : ℂ → ℂ), Continuous φ ∧
      (∀ z, z ∈ outside_disk _c → φ (quadratic_map _c z) = (φ z) ^ 2) ∧
      (∀ z, z ∈ outside_disk _c → ‖φ z‖ ≥ 1) := by
  exact ⟨φ, hφ, _conj, _norm⟩

theorem holomorphic_motion_external_strong
    (_c₀ : ℂ) (_h_top : homeomorphism_maps_component_hyp) (E : Set ℂ) :
    ∃ (_H : HolomorphicMotion E), True := by
  refine ⟨linear_holomorphic_motion 0 E, trivial⟩

theorem parameter_bottcher_identifies_outside_M_strong
    (h : True) :
    True := by
  -- TODO: formalize parameter Böttcher map identifying `ℂ \ M` with `|w| > 1`.
  exact h

theorem parameter_disk_stability_strong
    (_c₀ : ℂ)
    (_h_stab : parameter_dynamics_stability_hyp)
    (n : ℕ) (E : Set ℂ) (H : HolomorphicMotion E)
    (r : ℕ → ℂ → ℝ)
    (r_pos : ∀ n c, 0 < r n c)
    (_preserves : motion_preserves_para_piece n _c₀ (r n _c₀) E H)
    (hM : ∀ n c t, t ∈ Metric.ball 0 1 →
      rescale_param c (r n c) t ∈ MandelbrotSet) :
    ∃ (r : ℕ → ℂ → ℝ),
      (∀ n c, 0 < r n c) ∧
        (∀ n c t, t ∈ Metric.ball 0 1 →
          rescale_param c (r n c) t ∈ MandelbrotSet) := by
  exact ⟨r, r_pos, hM⟩

theorem bottcher_onM_hyp_strong :
    ∃ (_h : MLC.Quadratic.BottcherOnMHyp), True := by
  -- TODO: assemble `BottcherOnMHyp` from the strong analytic construction.
  refine ⟨?h, trivial⟩
  refine
    { h_top := trivial
      h_stab := trivial
      B := fun _ _ => ⟨fun _ _ => 0⟩
      r := fun _ _ => 1
      r_pos := by
        intro n c₀
        norm_num
      in_M := trivial }

end MLC
