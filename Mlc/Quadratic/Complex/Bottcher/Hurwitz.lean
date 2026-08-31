import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Normed.Module.RCLike.Real

/-!
# The minimum modulus principle (Hurwitz engine)

Toward the value-preservation (Hurwitz) step of Zalcman's rescaling lemma, this file proves the
**minimum modulus principle**: a holomorphic function with no zeros on a closed disk attains no
interior minimum of `‖·‖` below its boundary values.  Concretely, if `h` is holomorphic and
nonvanishing on `closedBall z₀ r` and `‖h‖ ≥ m` on the boundary sphere, then `‖h z₀‖ ≥ m`.

The proof is **Rouché-free**: it applies the maximum modulus principle
(`Complex.norm_le_of_forall_mem_frontier_norm_le`) to the reciprocal `1/h`, which is holomorphic
because `h` has no zeros.  This is the analytic core of Hurwitz's theorem (a locally uniform limit
of nonvanishing holomorphic functions is nonvanishing or identically zero), which in turn feeds
the "the renormalized limit omits `{0,1}`" clause of the strong Montel theorem.

All results are sorry-free and use only the Lean-core axioms.
-/

namespace MLC.Quadratic

open Complex Metric

/-- **Minimum modulus principle.**  If `h` is holomorphic and nonvanishing on the closed disk
`closedBall z₀ r` (`r > 0`) and its modulus is at least `m > 0` on the boundary sphere, then its
modulus at the centre is also at least `m`.  Proved by applying the maximum modulus principle to
the reciprocal `1/h`. -/
theorem norm_center_ge_of_forall_mem_sphere_le {h : ℂ → ℂ} {z₀ : ℂ} {r m : ℝ}
    (hr : 0 < r) (hm : 0 < m) (hd : DifferentiableOn ℂ h (closedBall z₀ r))
    (hne : ∀ z ∈ closedBall z₀ r, h z ≠ 0)
    (hlb : ∀ w ∈ sphere z₀ r, m ≤ ‖h w‖) :
    m ≤ ‖h z₀‖ := by
  have hball : ball z₀ r ⊆ closedBall z₀ r := ball_subset_closedBall
  have hclosure : closure (ball z₀ r) = closedBall z₀ r := closure_ball z₀ hr.ne'
  have hinvdiff : DifferentiableOn ℂ (fun z => (h z)⁻¹) (ball z₀ r) :=
    (hd.mono hball).inv (fun z hz => hne z (hball hz))
  have hinvcont : ContinuousOn (fun z => (h z)⁻¹) (closure (ball z₀ r)) := by
    rw [hclosure]; exact hd.continuousOn.inv₀ hne
  have hdc : DiffContOnCl ℂ (fun z => (h z)⁻¹) (ball z₀ r) := ⟨hinvdiff, hinvcont⟩
  have hC : ∀ z ∈ frontier (ball z₀ r), ‖(h z)⁻¹‖ ≤ m⁻¹ := by
    rw [frontier_ball z₀ hr.ne']
    intro w hw
    rw [norm_inv]
    exact inv_anti₀ hm (hlb w hw)
  have hz₀ : z₀ ∈ closure (ball z₀ r) := by
    rw [hclosure]; exact mem_closedBall_self hr.le
  have hmain := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hdc hC hz₀
  rw [norm_inv] at hmain
  have hpos : 0 < ‖h z₀‖ := norm_pos_iff.2 (hne z₀ (mem_closedBall_self hr.le))
  exact (inv_le_inv₀ hpos hm).1 hmain

/-- **Hurwitz's theorem (nonvanishing form).**  If holomorphic functions `F i`, each nowhere zero
on an open preconnected set `U`, converge locally uniformly to `g` (analytic on `U`), then the
limit `g` is either identically zero or nowhere zero on `U`.  This is the value-preservation step
of the Zalcman route to strong Montel: applied to `F i - v` it shows the renormalized limit still
omits every value omitted by the whole family (in particular `{0,1}`).

The proof is Rouché-free.  If `g` had a zero `z₀` without vanishing identically, the identity
theorem isolates that zero, so `‖g‖ ≥ m > 0` on a small boundary sphere; uniform convergence makes
`‖F i‖ ≥ m/2` on that sphere for large `i`, whence the minimum modulus principle forces
`‖F i z₀‖ ≥ m/2`, contradicting `F i z₀ → g z₀ = 0`. -/
theorem hurwitz_ne_zero_of_forall_ne_zero {ι : Type*} {p : Filter ι} [p.NeBot]
    {F : ι → ℂ → ℂ} {g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hUc : IsPreconnected U)
    (hF : TendstoLocallyUniformlyOn F g p U) (hFd : ∀ i, DifferentiableOn ℂ (F i) U)
    (hFne : ∀ i, ∀ z ∈ U, F i z ≠ 0) (hg : AnalyticOnNhd ℂ g U)
    (hgnc : ¬ Set.EqOn g 0 U) :
    ∀ z ∈ U, g z ≠ 0 := by
  intro z₀ hz₀ hzero
  -- The zero is isolated: `g` is nonzero on a punctured neighbourhood of `z₀`.
  have hne_punct : ∀ᶠ w in nhdsWithin z₀ {z₀}ᶜ, g w ≠ 0 := by
    have hnot : ¬ ∃ᶠ w in nhdsWithin z₀ {z₀}ᶜ, g w = 0 := fun hfreq =>
      hgnc (hg.eqOn_zero_of_preconnected_of_frequently_eq_zero hUc hz₀ hfreq)
    exact Filter.not_frequently.1 hnot
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hne_punct
  obtain ⟨δ, hδ, hδne⟩ := hne_punct
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU z₀ hz₀
  set r : ℝ := min δ ε / 2 with hrdef
  have hmin : 0 < min δ ε := lt_min hδ hε
  have hr : 0 < r := by rw [hrdef]; exact half_pos hmin
  have hrδ : r < δ := by
    rw [hrdef]; exact (half_lt_self hmin).trans_le (min_le_left _ _)
  have hrε : r < ε := by
    rw [hrdef]; exact (half_lt_self hmin).trans_le (min_le_right _ _)
  have hsubBall : Metric.closedBall z₀ r ⊆ Metric.ball z₀ ε := Metric.closedBall_subset_ball hrε
  have hsub : Metric.closedBall z₀ r ⊆ U := hsubBall.trans hεU
  -- `g` is nonzero on the boundary sphere of radius `r`.
  have hgne_sphere : ∀ w ∈ Metric.sphere z₀ r, g w ≠ 0 := by
    intro w hw
    have hwdist : dist w z₀ = r := hw
    refine hδne (by rw [hwdist]; exact hrδ) ?_
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hwz; rw [hwz, dist_self] at hwdist; exact hr.ne' hwdist.symm
  -- Minimum of `‖g‖` on the compact sphere is positive.
  have hspNe : (Metric.sphere z₀ r).Nonempty := NormedSpace.sphere_nonempty.2 hr.le
  have hcontg : ContinuousOn (fun w => ‖g w‖) (Metric.sphere z₀ r) :=
    ((hg.continuousOn).mono (sphere_subset_closedBall.trans hsub)).norm
  obtain ⟨w₀, hw₀sp, hw₀min⟩ := (isCompact_sphere z₀ r).exists_isMinOn hspNe hcontg
  set m : ℝ := ‖g w₀‖ with hmdef
  have hm : 0 < m := by rw [hmdef]; exact norm_pos_iff.2 (hgne_sphere w₀ hw₀sp)
  have hlb_g : ∀ w ∈ Metric.sphere z₀ r, m ≤ ‖g w‖ := fun w hw => hw₀min hw
  -- Uniform convergence on the compact closed ball, and pointwise at the centre.
  have huc : TendstoUniformlyOn F g p (Metric.closedBall z₀ r) :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).1 hF _ hsub (isCompact_closedBall z₀ r)
  have hus : TendstoUniformlyOn F g p (Metric.sphere z₀ r) := huc.mono sphere_subset_closedBall
  have hbnd_sphere : ∀ᶠ i in p, ∀ w ∈ Metric.sphere z₀ r, dist (g w) (F i w) < m / 2 :=
    Metric.tendstoUniformlyOn_iff.1 hus (m / 2) (half_pos hm)
  have hcenter : Filter.Tendsto (fun i => F i z₀) p (nhds (g z₀)) :=
    huc.tendsto_at (mem_closedBall_self hr.le)
  have hbnd_center : ∀ᶠ i in p, ‖F i z₀‖ < m / 2 := by
    have := Metric.tendsto_nhds.1 hcenter (m / 2) (half_pos hm)
    filter_upwards [this] with i hi
    rwa [hzero, dist_zero_right] at hi
  -- Pick an index satisfying both bounds and derive a contradiction via minimum modulus.
  obtain ⟨i, hi_sp, hi_ce⟩ := (hbnd_sphere.and hbnd_center).exists
  have hlb_Fi : ∀ w ∈ Metric.sphere z₀ r, m / 2 ≤ ‖F i w‖ := by
    intro w hw
    have h1 : ‖g w‖ - ‖F i w‖ ≤ dist (g w) (F i w) := by
      rw [dist_eq_norm]; exact norm_sub_norm_le _ _
    have h2 := hi_sp w hw
    have h3 : m ≤ ‖g w‖ := hlb_g w hw
    linarith
  have hFi_center : m / 2 ≤ ‖F i z₀‖ :=
    norm_center_ge_of_forall_mem_sphere_le hr (half_pos hm)
      ((hFd i).mono hsub) (fun z hz => hFne i z (hsub hz)) hlb_Fi
  exact absurd hFi_center (not_le.2 hi_ce)

/-- **Hurwitz value preservation.**  If holomorphic functions `F i`, each omitting the value `v`
on an open preconnected set `U`, converge locally uniformly to `g` (analytic on `U`), then the
limit `g` either equals `v` identically or omits `v` everywhere on `U`.  This is the form consumed
by strong Montel: the renormalized limit of a family omitting `{0,1}` still omits `{0,1}` unless it
is constant. -/
theorem hurwitz_ne_of_forall_ne {ι : Type*} {p : Filter ι} [p.NeBot]
    {F : ι → ℂ → ℂ} {g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hUc : IsPreconnected U)
    (hF : TendstoLocallyUniformlyOn F g p U) (hFd : ∀ i, DifferentiableOn ℂ (F i) U) (v : ℂ)
    (hFne : ∀ i, ∀ z ∈ U, F i z ≠ v) (hg : AnalyticOnNhd ℂ g U)
    (hgnc : ¬ Set.EqOn g (fun _ => v) U) :
    ∀ z ∈ U, g z ≠ v := by
  have hFsub : TendstoLocallyUniformlyOn (fun i z => F i z - v) (fun z => g z - v) p U := by
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hU]
    intro K hKU hK
    have h := (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).1 hF K hKU hK
    rw [Metric.tendstoUniformlyOn_iff] at h ⊢
    intro δ hδ
    filter_upwards [h δ hδ] with i hi w hw
    simpa [dist_eq_norm, sub_sub_sub_cancel_right] using hi w hw
  have hgsub : AnalyticOnNhd ℂ (fun z => g z - v) U := hg.sub analyticOnNhd_const
  have hgncsub : ¬ Set.EqOn (fun z => g z - v) 0 U := by
    intro h; apply hgnc; intro z hz
    have := h hz; simpa [sub_eq_zero] using this
  have hkey := hurwitz_ne_zero_of_forall_ne_zero hU hUc hFsub
    (fun i => (hFd i).sub_const v) (fun i z hz => sub_ne_zero.2 (hFne i z hz)) hgsub hgncsub
  intro z hz
  exact sub_ne_zero.1 (hkey z hz)

end MLC.Quadratic
