import Mlc.Quadratic.Complex.Bottcher.BottcherParamInverse
import Mlc.Quadratic.Complex.Bottcher.Slodkowski

/-!
# A local parameter-inverse motion

The parametrized inverse theorem gives a `C¹` inverse germ for the joint
Böttcher map.  This file extracts a small parameter disk on which that germ
can be evaluated along a parameter path.  The resulting motion is deliberately
supported on a singleton: it is a genuine nonempty space-holomorphic motion
and records the checked inverse-family interface without claiming a
parameter/dynamical puzzle correspondence.
-/

namespace MLC.Quadratic

open Complex Topology Set Metric

noncomputable section

/-- A singleton motion obtained by evaluating the local parametrized Böttcher
inverse at a fixed exterior Böttcher value. -/
theorem exists_param_inverse_singleton_motion (c₀ : ℂ) :
    ∃ (z₀ w₀ : ℂ) (H : SpaceHolomorphicMotion ({z₀} : Set ℂ)),
      w₀ = logSeriesBottcherApprox c₀ z₀ ∧
      H.f 0 z₀ = z₀ := by
  obtain ⟨z₀, w₀, ψ, hw₀, hψcd, hψ0, _hleft, _hc_holo, _hz_holo⟩ :=
    exists_param_holo_bottcher_inverse c₀
  obtain ⟨U, hU, hψU⟩ := hψcd.contDiffOn (le_refl 1) (by simp)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hU
  let r : ℝ := δ / 2
  have hr : 0 < r := by
    dsimp [r]
    linarith
  let path : ℂ → ℂ × ℂ := fun t => (c₀ + (r : ℂ) * t, w₀)
  have hpath :
      ∀ t ∈ Metric.ball (0 : ℂ) 1, path t ∈ Metric.ball (c₀, w₀) δ := by
    intro t ht
    have ht_norm : ‖t‖ < 1 := by
      simpa [Metric.mem_ball, dist_zero_right] using ht
    have hfirst : dist (c₀ + (r : ℂ) * t) c₀ < δ := by
      rw [dist_eq_norm]
      have hnorm : ‖(r : ℂ) * t‖ = r * ‖t‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.le]
      rw [show c₀ + (r : ℂ) * t - c₀ = (r : ℂ) * t by ring, hnorm]
      dsimp [r]
      nlinarith
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
    exact ⟨hfirst, by simpa [path] using hδ⟩
  have hpathU : ∀ t ∈ Metric.ball (0 : ℂ) 1, path t ∈ U := by
    intro t ht
    exact hball (hpath t ht)
  have hpath_diff :
      DifferentiableOn ℂ path (Metric.ball (0 : ℂ) 1) := by
    have hfirst :
        DifferentiableOn ℂ (fun t : ℂ => c₀ + (r : ℂ) * t)
          (Metric.ball (0 : ℂ) 1) :=
      (differentiableOn_const c₀).add (differentiableOn_id.const_mul (r : ℂ))
    exact hfirst.prodMk (differentiableOn_const w₀)
  let f : ℂ → ℂ → ℂ := fun t _ => (ψ (path t)).2
  have hf_holo :
      DifferentiableOn ℂ (fun t : ℂ => (ψ (path t)).2)
        (Metric.ball (0 : ℂ) 1) := by
    have hψdiff : DifferentiableOn ℂ ψ U := hψU.differentiableOn_one
    have hcomp : DifferentiableOn ℂ (fun t => ψ (path t))
        (Metric.ball (0 : ℂ) 1) :=
      hψdiff.fun_comp hpath_diff hpathU
    exact hcomp.snd
  refine ⟨z₀, w₀,
    { f := f
      h_zero := ?_
      h_inj := ?_
      h_holo := ?_
      U := Set.univ
      hEU := by intro z hz; trivial
      hU_open := isOpen_univ
      h_space_holo := ?_ },
    hw₀, ?_⟩
  · intro z hz
    have hz_eq : z = z₀ := by simpa using hz
    subst z
    simp [f, path, hψ0]
  · intro t ht a ha b hb _
    have ha' : a = z₀ := by simpa using ha
    have hb' : b = z₀ := by simpa using hb
    exact ha'.trans hb'.symm
  · intro z hz
    simpa [f] using hf_holo
  · intro t ht
    exact differentiableOn_const _
  · simp [f, path, hψ0]

/-! The next theorem records a nontrivial motion relation, rather than only the
existence of a local inverse germ. -/

/-- A nontrivial singleton motion tracked by the local parametrized Böttcher
inverse.  The parameter and dynamical coordinates both move along a small
complex disk, and the inverse identity recovers the moving dynamical point.
This is local analytic infrastructure only; it does not identify a
Mandelbrot parameter piece. -/
theorem exists_nontrivial_param_inverse_motion (c₀ : ℂ) :
    ∃ (z₀ w₀ : ℂ) (ψ : ℂ × ℂ → ℂ × ℂ) (a b : ℝ)
      (H : SpaceHolomorphicMotion ({z₀} : Set ℂ)),
      w₀ = logSeriesBottcherApprox c₀ z₀ ∧
      0 < a ∧ 0 < b ∧
      (∀ t ∈ Metric.ball (0 : ℂ) 1,
        ψ (c₀ + (b : ℂ) * t,
          logSeriesBottcherApprox (c₀ + (b : ℂ) * t) (z₀ + (a : ℂ) * t)) =
          (c₀ + (b : ℂ) * t, z₀ + (a : ℂ) * t)) ∧
      (∀ t z, H.f t z = z₀ + (a : ℂ) * t) ∧
      H.f (1 / 2 : ℂ) z₀ ≠ H.f 0 z₀ := by
  obtain ⟨z₀, w₀, ψ, hw₀, _hψcd, _hψ0, hleft, _hc_holo, _hz_holo⟩ :=
    exists_param_holo_bottcher_inverse c₀
  have hleft_set :
      {p : ℂ × ℂ |
          ψ (p.1, logSeriesBottcherApprox p.1 p.2) = p} ∈
        𝓝 (c₀, z₀) :=
    hleft
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hleft_set
  let a : ℝ := δ / 2
  let b : ℝ := δ / 2
  have ha : 0 < a := by
    dsimp [a]
    linarith
  have hb : 0 < b := by
    dsimp [b]
    linarith
  let path : ℂ → ℂ × ℂ := fun t =>
    (c₀ + (b : ℂ) * t, z₀ + (a : ℂ) * t)
  have hpath :
      ∀ t ∈ Metric.ball (0 : ℂ) 1, path t ∈ Metric.ball (c₀, z₀) δ := by
    intro t ht
    have ht_norm : ‖t‖ < 1 := by
      simpa [Metric.mem_ball, dist_zero_right] using ht
    have hfirst : dist (c₀ + (b : ℂ) * t) c₀ < δ := by
      rw [dist_eq_norm]
      have hnorm : ‖(b : ℂ) * t‖ = b * ‖t‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hb.le]
      rw [show c₀ + (b : ℂ) * t - c₀ = (b : ℂ) * t by ring, hnorm]
      dsimp [b]
      nlinarith
    have hsecond : dist (z₀ + (a : ℂ) * t) z₀ < δ := by
      rw [dist_eq_norm]
      have hnorm : ‖(a : ℂ) * t‖ = a * ‖t‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ha.le]
      rw [show z₀ + (a : ℂ) * t - z₀ = (a : ℂ) * t by ring, hnorm]
      dsimp [a]
      nlinarith
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
    exact ⟨hfirst, hsecond⟩
  let f : ℂ → ℂ → ℂ := fun t _ => z₀ + (a : ℂ) * t
  let H : SpaceHolomorphicMotion ({z₀} : Set ℂ) :=
    { f := f
      h_zero := by
        intro z hz
        have hz_eq : z = z₀ := by simpa using hz
        subst z
        simp [f]
      h_inj := by
        intro t ht x hx y hy hxy
        have hx' : x = z₀ := by simpa using hx
        have hy' : y = z₀ := by simpa using hy
        exact hx'.trans hy'.symm
      h_holo := by
        intro z hz
        simpa [f] using
          (differentiableOn_const z₀).add
            (differentiableOn_id.const_mul (a : ℂ))
      U := Set.univ
      hEU := by intro z hz; trivial
      hU_open := isOpen_univ
      h_space_holo := by
        intro t ht
        exact differentiableOn_const _ }
  refine ⟨z₀, w₀, ψ, a, b, H, hw₀, ha, hb, ?_, ?_, ?_⟩
  · intro t ht
    have hp : path t ∈
        {p : ℂ × ℂ |
          ψ (p.1, logSeriesBottcherApprox p.1 p.2) = p} :=
      hball (hpath t ht)
    simpa [path] using hp
  · intro t z
    simp [H, f]
  · have ht : (1 / 2 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
      rw [Metric.mem_ball, dist_zero_right]
      norm_num
    have hneq : z₀ + (a : ℂ) * (1 / 2 : ℂ) ≠ z₀ := by
      intro h
      have : (a : ℂ) * (1 / 2 : ℂ) = 0 := by
        linear_combination h
      have hac : (a : ℂ) ≠ 0 := by
        exact_mod_cast (ne_of_gt ha)
      exact hac (Or.resolve_right (mul_eq_zero.mp this) (by norm_num))
    simpa [H, f] using hneq

/-! The same local inverse relation can be tracked on a connected continuum,
not only on one point. -/

/-- A nontrivial space-holomorphic translation of a small closed disk whose
points are all recovered by the local parametrized Böttcher inverse.  The
disk is an explicit connected source object; no connectivity conclusion about
a Mandelbrot slice is included. -/
theorem exists_nontrivial_param_inverse_disk_motion (c₀ : ℂ) :
    ∃ (z₀ w₀ : ℂ) (ψ : ℂ × ℂ → ℂ × ℂ) (ε a b : ℝ)
      (H : SpaceHolomorphicMotion (Metric.closedBall z₀ ε)),
      w₀ = logSeriesBottcherApprox c₀ z₀ ∧
      0 < ε ∧ 0 < a ∧ 0 < b ∧
      IsConnected (Metric.closedBall z₀ ε) ∧
      (∀ t ∈ Metric.ball (0 : ℂ) 1, ∀ z ∈ Metric.closedBall z₀ ε,
        ψ (c₀ + (b : ℂ) * t,
          logSeriesBottcherApprox (c₀ + (b : ℂ) * t) (H.f t z)) =
          (c₀ + (b : ℂ) * t, H.f t z)) ∧
      H.f (1 / 2 : ℂ) z₀ ≠ H.f 0 z₀ := by
  obtain ⟨z₀, w₀, ψ, hw₀, _hψcd, _hψ0, hleft, _hc_holo, _hz_holo⟩ :=
    exists_param_holo_bottcher_inverse c₀
  have hleft_set :
      {p : ℂ × ℂ |
          ψ (p.1, logSeriesBottcherApprox p.1 p.2) = p} ∈
        𝓝 (c₀, z₀) :=
    hleft
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hleft_set
  let ε : ℝ := δ / 4
  let a : ℝ := δ / 4
  let b : ℝ := δ / 4
  have hε : 0 < ε := by
    dsimp [ε]
    linarith
  have ha : 0 < a := by
    dsimp [a]
    linarith
  have hb : 0 < b := by
    dsimp [b]
    linarith
  let path : ℂ → ℂ → ℂ × ℂ := fun t z =>
    (c₀ + (b : ℂ) * t, z + (a : ℂ) * t)
  have hpath :
      ∀ t ∈ Metric.ball (0 : ℂ) 1, ∀ z ∈ Metric.closedBall z₀ ε,
        path t z ∈ Metric.ball (c₀, z₀) δ := by
    intro t ht z hz
    have ht_norm : ‖t‖ < 1 := by
      simpa [Metric.mem_ball, dist_zero_right] using ht
    have hfirst : dist (c₀ + (b : ℂ) * t) c₀ < δ := by
      rw [dist_eq_norm]
      have hnorm : ‖(b : ℂ) * t‖ = b * ‖t‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hb.le]
      rw [show c₀ + (b : ℂ) * t - c₀ = (b : ℂ) * t by ring, hnorm]
      dsimp [b]
      nlinarith
    have hmove : dist (z + (a : ℂ) * t) z < δ / 4 := by
      rw [dist_eq_norm]
      have hnorm : ‖(a : ℂ) * t‖ = a * ‖t‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ha.le]
      rw [show z + (a : ℂ) * t - z = (a : ℂ) * t by ring, hnorm]
      dsimp [a]
      nlinarith
    have hbase : dist z z₀ ≤ ε := hz
    have hsecond : dist (z + (a : ℂ) * t) z₀ < δ := by
      calc
        dist (z + (a : ℂ) * t) z₀ ≤
            dist (z + (a : ℂ) * t) z + dist z z₀ := dist_triangle _ _ _
        _ < δ / 4 + ε := add_lt_add_of_lt_of_le hmove hbase
        _ < δ := by dsimp [ε]; linarith
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
    exact ⟨hfirst, hsecond⟩
  let f : ℂ → ℂ → ℂ := fun t z => z + (a : ℂ) * t
  let H : SpaceHolomorphicMotion (Metric.closedBall z₀ ε) :=
    { f := f
      h_zero := by
        intro z hz
        simp [f]
      h_inj := by
        intro t ht x hx y hy hxy
        have hxy' : x + (a : ℂ) * t = y + (a : ℂ) * t := by
          simpa [f] using hxy
        exact add_right_cancel hxy'
      h_holo := by
        intro z hz
        simpa [f] using
          (differentiableOn_const z).add
            (differentiableOn_id.const_mul (a : ℂ))
      U := Set.univ
      hEU := by intro z hz; trivial
      hU_open := isOpen_univ
      h_space_holo := by
        intro t ht
        simpa [f] using
          (differentiableOn_id.add (differentiableOn_const ((a : ℂ) * t))) }
  refine ⟨z₀, w₀, ψ, ε, a, b, H, hw₀, hε, ha, hb,
    ?_, ?_, ?_⟩
  · exact ⟨⟨z₀, Metric.mem_closedBall_self hε.le⟩,
      (convex_closedBall z₀ ε).isPreconnected⟩
  · intro t ht z hz
    have hp : path t z ∈
        {p : ℂ × ℂ |
          ψ (p.1, logSeriesBottcherApprox p.1 p.2) = p} :=
      hball (hpath t ht z hz)
    simpa [path, H, f] using hp
  · have ht : (1 / 2 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
      rw [Metric.mem_ball, dist_zero_right]
      norm_num
    have hneq : z₀ + (a : ℂ) * (1 / 2 : ℂ) ≠ z₀ := by
      intro h
      have hzero : (a : ℂ) * (1 / 2 : ℂ) = 0 := by
        linear_combination h
      have hac : (a : ℂ) ≠ 0 := by
        exact_mod_cast (ne_of_gt ha)
      exact hac (Or.resolve_right (mul_eq_zero.mp hzero) (by norm_num))
    simpa [H, f] using hneq

end

end MLC.Quadratic
