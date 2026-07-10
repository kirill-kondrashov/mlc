import Mlc.Quadratic.Complex.GreenHarmonic

open MLC MLC.Quadratic Complex Filter Topology

namespace MLC.Quadratic

theorem principalPullbackLogSeriesBottcher_modulus_on_basin
    (c z : ℂ) (hz : z ∈ basin_of_infinity c) :
    ‖principalPullbackLogSeriesBottcher c z hz‖ = Real.exp (green_function c z) := by
  set N := basinEscapeTime c z hz with hN
  set w := (MLC.quadratic_map c)^[N] z with hw
  have hwout : ‖w‖ > ‖c‖ + 2 := basinEscapeTime_spec c z hz
  have hnorm := principalPullbackLogSeriesBottcher_norm_eq_rpow_iterateValue c z hz
  simp only at hnorm
  have hlog : green_function c w = Real.log ‖MLC.logSeriesBottcherApprox c w‖ :=
    green_function_eq_log_norm_logSeries_of_outside_open c hwout
  have horbit : green_function c w = (2:ℝ)^N * green_function c z := by
    simpa [hw] using green_function_orbit_eq_local c z N
  have hφpos : 0 < ‖MLC.logSeriesBottcherApprox c w‖ := by
    have := MLC.one_lt_norm_logSeriesBottcherApprox_of_outside_open c hwout
    linarith
  rw [hnorm]
  have hexp : ‖MLC.logSeriesBottcherApprox c w‖ = Real.exp (green_function c w) := by
    rw [hlog, Real.exp_log hφpos]
  rw [hexp, horbit, ← Real.exp_mul]
  have h2 : ((2:ℝ)^N) ≠ 0 := by positivity
  congr 1
  field_simp
  ring

theorem basinLogSeriesExtensionCandidate_modulus_on_basin
    (c z : ℂ) (hz : z ∈ basin_of_infinity c) :
    ‖basinLogSeriesExtensionCandidate c z‖ = Real.exp (green_function c z) := by
  classical
  rw [basinLogSeriesExtensionCandidate]
  simp only [hz, dif_pos]
  exact principalPullbackLogSeriesBottcher_modulus_on_basin c z hz

theorem basinLogSeriesExtensionCandidate_norm_gt_one_on_basin
    (c z : ℂ) (hz : z ∈ basin_of_infinity c) :
    1 < ‖basinLogSeriesExtensionCandidate c z‖ :=
  basinLogSeriesExtensionCandidate_norm_on_basin_of_principalPullback_modulus
    (fun z hz => principalPullbackLogSeriesBottcher_modulus_on_basin c z hz) z hz

theorem basinLogSeriesExtensionCandidate_tendsto_div_atInfinity (c : ℂ) :
    Tendsto (fun z => basinLogSeriesExtensionCandidate c z / z) atInfinity (𝓝 (1 : ℂ)) := by
  refine (Filter.tendsto_congr' ?_).2 (MLC.tendsto_logSeriesBottcherApprox_div_atInfinity c)
  filter_upwards [eventually_atInfinity_norm_gt (‖c‖ + 2)] with z hz
  rw [basinLogSeriesExtensionCandidate_extends_near c z hz]

theorem basinEscapeTime_map_of_pos
    (c z : ℂ) (hz : z ∈ basin_of_infinity c)
    (hfz : MLC.quadratic_map c z ∈ basin_of_infinity c)
    (hN : basinEscapeTime c z hz ≠ 0) :
    basinEscapeTime c (MLC.quadratic_map c z) hfz = basinEscapeTime c z hz - 1 := by
  set N := basinEscapeTime c z hz with hNdef
  have hspecP : ‖(MLC.quadratic_map c)^[N] z‖ > ‖c‖ + 2 := basinEscapeTime_spec c z hz
  have hminP : ∀ m < N, ¬ (‖(MLC.quadratic_map c)^[m] z‖ > ‖c‖ + 2) := by
    intro m hm; exact Nat.find_min _ hm
  rw [basinEscapeTime, Nat.find_eq_iff]
  refine ⟨?_, ?_⟩
  · have h : (MLC.quadratic_map c)^[N - 1] (MLC.quadratic_map c z)
        = (MLC.quadratic_map c)^[N] z := by
      rw [← Function.iterate_succ_apply]; congr 1; omega
    rw [h]; exact hspecP
  · intro k hk
    have hstep : (MLC.quadratic_map c)^[k] (MLC.quadratic_map c z)
        = (MLC.quadratic_map c)^[k+1] z := by
      rw [← Function.iterate_succ_apply]
    rw [hstep]; exact hminP (k+1) (by omega)

theorem cpow_two_eq (x w : ℂ) (hx : x ≠ 0) : (x ^ w) ^ (2:ℕ) = x ^ ((2:ℂ) * w) := by
  rw [pow_two, ← Complex.cpow_add _ _ hx]
  ring_nf

theorem basinLogSeriesExtensionCandidate_conj_on_basin
    (c z : ℂ) (hz : z ∈ basin_of_infinity c) :
    basinLogSeriesExtensionCandidate c (MLC.quadratic_map c z)
      = (basinLogSeriesExtensionCandidate c z) ^ 2 := by
  have hfz : MLC.quadratic_map c z ∈ basin_of_infinity c :=
    basin_of_infinity_forward_invariant c hz
  classical
  rw [basinLogSeriesExtensionCandidate]
  simp only [hfz, dif_pos]
  rw [basinLogSeriesExtensionCandidate]
  simp only [hz, dif_pos]
  rw [principalPullbackLogSeriesBottcher, principalPullbackLogSeriesBottcher]
  by_cases hN0 : basinEscapeTime c z hz = 0
  · have hzout : ‖z‖ > ‖c‖ + 2 := by
      have := basinEscapeTime_spec c z hz
      rw [hN0] at this
      simpa using this
    have hfzout : ‖MLC.quadratic_map c z‖ > ‖c‖ + 2 := quadratic_map_maps_outside_open c hzout
    have hM0 : basinEscapeTime c (MLC.quadratic_map c z) hfz = 0 := by
      rw [basinEscapeTime, Nat.find_eq_iff]
      exact ⟨by simpa using hfzout, by intro k hk; omega⟩
    rw [hN0, hM0]
    simp only [Function.iterate_zero, id_eq, pow_zero, inv_one, Complex.cpow_one]
    exact logSeriesBottcherApprox_conj_of_large_radius c (le_refl _) hzout
  · set N := basinEscapeTime c z hz with hNdef
    have hM : basinEscapeTime c (MLC.quadratic_map c z) hfz = N - 1 :=
      basinEscapeTime_map_of_pos c z hz hfz hN0
    rw [hM]
    have hiter : (MLC.quadratic_map c)^[N - 1] (MLC.quadratic_map c z)
        = (MLC.quadratic_map c)^[N] z := by
      rw [← Function.iterate_succ_apply]
      congr 1
      omega
    rw [hiter]
    have hxne : MLC.logSeriesBottcherApprox c ((MLC.quadratic_map c)^[N] z) ≠ 0 := by
      have := principalPullbackLogSeriesBottcher_iterate_ne_zero c z hz
      rwa [← hNdef] at this
    rw [cpow_two_eq _ _ hxne]
    congr 1
    have h2 : ((2:ℂ)) ^ N = 2 * (2:ℂ) ^ (N - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [h2]
    have hne : ((2:ℂ) ^ (N - 1)) ≠ 0 := pow_ne_zero _ (by norm_num)
    field_simp

 theorem basinLogSeriesExtensionCandidate_basin_of_norm_gt_one (c : ℂ) :
    ∀ z : ℂ, 1 < ‖basinLogSeriesExtensionCandidate c z‖ →
      z ∈ basin_of_infinity c := by
  intro z hz
  by_contra hnb
  rw [basinLogSeriesExtensionCandidate, dif_neg hnb, norm_zero] at hz
  linarith

/-- The principal-pullback coherent-data target reduces to a single explicit
analytic hypothesis: given only holomorphicity of the candidate on the basin,
all seven `PrincipalPullbackCoherentDataFor` fields are discharged. The six
non-holo fields are proven in-repo; `holo_on_basin` is the sole remaining
analytic seam (branch-coherent / monodromy-trivial construction). -/
theorem principalPullbackCoherentData_of_holo (c : ℂ)
    (holo : DifferentiableOn ℂ (basinLogSeriesExtensionCandidate c)
      (basin_of_infinity c)) :
    PrincipalPullbackCoherentDataFor c where
  extends_near := fun z hz => basinLogSeriesExtensionCandidate_extends_near c z hz
  norm_on_basin := fun z hz => basinLogSeriesExtensionCandidate_norm_gt_one_on_basin c z hz
  basin_of_norm_gt_one := basinLogSeriesExtensionCandidate_basin_of_norm_gt_one c
  conj_on_basin := fun z hz => basinLogSeriesExtensionCandidate_conj_on_basin c z hz
  holo_on_basin := holo
  modulus_on_basin := fun z hz => basinLogSeriesExtensionCandidate_modulus_on_basin c z hz
  tendsto_div_atInfinity := basinLogSeriesExtensionCandidate_tendsto_div_atInfinity c

theorem escapeTimeIndependent_value_modulus (c : ℂ)
    (d : EscapeTimeIndependentPullbackDataFor c)
    (z : ℂ) (hz : z ∈ basin_of_infinity c) :
    ‖d.value z hz‖ = Real.exp (green_function c z) := by
  set N := basinEscapeTime c z hz with hN
  set w := (MLC.quadratic_map c)^[N] z with hw
  have hspec : ‖w‖ > ‖c‖ + 2 := basinEscapeTime_spec c z hz
  have hroot : (d.value z hz) ^ (2 ^ N) = MLC.logSeriesBottcherApprox c w :=
    d.compatible_with_every_escape_time z hz N hspec
  have hLpos : (0 : ℝ) < ‖MLC.logSeriesBottcherApprox c w‖ := by
    have := MLC.one_lt_norm_logSeriesBottcherApprox_of_outside_open c hspec
    linarith
  have hnorm : ‖d.value z hz‖ ^ (2 ^ N) = ‖MLC.logSeriesBottcherApprox c w‖ := by
    rw [← norm_pow, hroot]
  have hgw : green_function c w = Real.log ‖MLC.logSeriesBottcherApprox c w‖ :=
    green_function_eq_log_norm_logSeries_of_outside_open c hspec
  have hLexp : ‖MLC.logSeriesBottcherApprox c w‖ = Real.exp (green_function c w) := by
    rw [hgw, Real.exp_log hLpos]
  have horbit : green_function c w = (2:ℝ) ^ N * green_function c z := by
    simpa [hw] using green_function_orbit_eq_local c z N
  have hpow : ‖d.value z hz‖ ^ (2 ^ N)
      = (Real.exp (green_function c z)) ^ (2 ^ N) := by
    rw [hnorm, hLexp, horbit, ← Real.exp_nat_mul]
    congr 1
    push_cast; ring
  have h2 : (2 ^ N : ℕ) ≠ 0 := pow_ne_zero N (by norm_num)
  calc ‖d.value z hz‖
      = (‖d.value z hz‖ ^ (2 ^ N)) ^ (((2 ^ N : ℕ) : ℝ)⁻¹) :=
        (Real.pow_rpow_inv_natCast (norm_nonneg _) h2).symm
    _ = ((Real.exp (green_function c z)) ^ (2 ^ N)) ^ (((2 ^ N : ℕ) : ℝ)⁻¹) := by rw [hpow]
    _ = Real.exp (green_function c z) :=
        Real.pow_rpow_inv_natCast (Real.exp_pos _).le h2

noncomputable def coherentBasinCoordinate {c : ℂ}
    (d : EscapeTimeIndependentPullbackDataFor c) (z : ℂ) : ℂ := by
  classical
  exact if hz : z ∈ basin_of_infinity c then d.value z hz else 0

theorem coherentBasinCoordinate_on_basin {c : ℂ}
    (d : EscapeTimeIndependentPullbackDataFor c) (z : ℂ)
    (hz : z ∈ basin_of_infinity c) :
    coherentBasinCoordinate d z = d.value z hz := by
  simp [coherentBasinCoordinate, hz]

theorem coherentBasinCoordinate_extends_near {c : ℂ}
    (d : EscapeTimeIndependentPullbackDataFor c) (z : ℂ) (hz : ‖z‖ > ‖c‖ + 2) :
    coherentBasinCoordinate d z = MLC.logSeriesBottcherApprox c z := by
  have hbasin : z ∈ basin_of_infinity c :=
    outside_disk_subset_quadratic_basin c (outside_open_subset_outside_disk c hz)
  rw [coherentBasinCoordinate_on_basin d z hbasin]
  exact d.agrees_near_infinity z hbasin hz

theorem coherentBasinCoordinate_modulus {c : ℂ}
    (d : EscapeTimeIndependentPullbackDataFor c) (z : ℂ)
    (hz : z ∈ basin_of_infinity c) :
    ‖coherentBasinCoordinate d z‖ = Real.exp (green_function c z) := by
  rw [coherentBasinCoordinate_on_basin d z hz]
  exact escapeTimeIndependent_value_modulus c d z hz

/-- The genuine Böttcher coordinate-data target for the coherent basin
coordinate reduces to exactly two explicit analytic facts about the
escape-time-independent value: functional-equation `conj` and holomorphicity
`holo`. The remaining five conjuncts (norm, basin characterization, modulus,
continuity, normalization at infinity) are automatic. -/
theorem genuineBottcherCoordinateData_of_escapeTimeIndependent_of_conj_of_holo
    {c : ℂ} (d : EscapeTimeIndependentPullbackDataFor c)
    (hconj : ∀ z : ℂ, z ∈ basin_of_infinity c →
      coherentBasinCoordinate d (MLC.quadratic_map c z)
        = (coherentBasinCoordinate d z) ^ 2)
    (hholo : DifferentiableOn ℂ (coherentBasinCoordinate d)
      (basin_of_infinity c)) :
    GenuineBottcherCoordinateDataFor c (coherentBasinCoordinate d) := by
  refine ⟨?_, ?_, hconj, ?_, hholo, ?_, ?_⟩
  · intro z hz
    rw [coherentBasinCoordinate_modulus d z hz]
    exact Real.one_lt_exp_iff.mpr (green_function_pos_of_basin c z hz)
  · intro z hz
    by_contra hnb
    rw [coherentBasinCoordinate, dif_neg hnb, norm_zero] at hz
    linarith
  · intro z hz
    exact coherentBasinCoordinate_modulus d z hz
  · intro z hz _
    exact (hholo.differentiableAt
      ((basin_of_infinity_isOpen c).mem_nhds hz)).continuousAt
  · refine (Filter.tendsto_congr' ?_).2 (MLC.tendsto_logSeriesBottcherApprox_div_atInfinity c)
    filter_upwards [eventually_atInfinity_norm_gt (‖c‖ + 2)] with z hz
    rw [coherentBasinCoordinate_extends_near d z hz]

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
  have hcoord_an : AnalyticOnNhd ℂ (coherentBasinCoordinate d) s :=
    hholo.analyticOnNhd hsopen
  have hfdiff : DifferentiableOn ℂ (MLC.quadratic_map c) s := by
    intro z _
    apply DifferentiableAt.differentiableWithinAt
    show DifferentiableAt ℂ (fun z => z ^ 2 + c) z
    fun_prop
  have hf_an : AnalyticOnNhd ℂ (MLC.quadratic_map c) s := hfdiff.analyticOnNhd hsopen
  have hmaps : Set.MapsTo (MLC.quadratic_map c) s s := basin_of_infinity_forward_invariant c
  have hf1_an : AnalyticOnNhd ℂ
      (fun z => coherentBasinCoordinate d (MLC.quadratic_map c z)) s :=
    hcoord_an.comp hf_an hmaps
  have hf2_an : AnalyticOnNhd ℂ
      (fun z => (coherentBasinCoordinate d z) ^ 2) s :=
    hcoord_an.pow 2
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

end MLC.Quadratic
