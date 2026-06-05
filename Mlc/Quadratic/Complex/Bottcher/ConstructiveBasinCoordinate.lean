import Mlc.Quadratic.Complex.Bottcher.BottcherOutsidePlan
import Mlc.Quadratic.Complex.Bottcher.BottcherMotion

namespace MLC

open Quadratic Complex Topology Set Filter Metric Real

namespace Quadratic

/-- The explicit proxy has the expected Green-function modulus everywhere. -/
lemma norm_polar_green_map_eq_exp_green (c z : ℂ) :
    ‖polar_green_map c z‖ = Real.exp (green_function c z) := by
  by_cases hz : z = 0
  · simp [polar_green_map, hz, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  · have hnormz : (‖z‖ : ℝ) ≠ 0 := norm_ne_zero_iff.2 hz
    have hdir : ‖z / (‖z‖ : ℂ)‖ = 1 := by
      rw [norm_div, Complex.norm_real, norm_norm, div_self hnormz]
    have hexp :
        ‖(Real.exp (green_function c z) : ℂ)‖ = Real.exp (green_function c z) := by
      simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc
      ‖polar_green_map c z‖
          = ‖(z / (‖z‖ : ℂ)) * (Real.exp (green_function c z) : ℂ)‖ := by
              simp [polar_green_map, hz]
      _ = ‖z / (‖z‖ : ℂ)‖ * ‖(Real.exp (green_function c z) : ℂ)‖ := by
            rw [norm_mul]
      _ = 1 * Real.exp (green_function c z) := by
            rw [hdir, hexp]
      _ = Real.exp (green_function c z) := by ring

/-- On the basin of infinity, the explicit proxy is exterior-valued. -/
lemma one_lt_norm_polar_green_map_of_mem_basin (c z : ℂ)
    (hz : z ∈ basin_of_infinity c) :
    1 < ‖polar_green_map c z‖ := by
  have hgreen_pos : 0 < green_function c z :=
    green_function_pos_of_basin c z hz
  rw [norm_polar_green_map_eq_exp_green]
  simpa using (Real.one_lt_exp_iff.mpr hgreen_pos)

/-- Constructive basin-valued Böttcher coordinate obtained by restricting the
explicit proxy to the basin of infinity. -/
noncomputable def basin_polar_green_map (c : ℂ) :
    {z : ℂ // z ∈ basin_of_infinity c} → {w : ℂ // 1 < ‖w‖} :=
  fun z => ⟨polar_green_map c z.1, one_lt_norm_polar_green_map_of_mem_basin c z.1 z.2⟩

@[simp] lemma basin_polar_green_map_coe (c : ℂ) (z : {z : ℂ // z ∈ basin_of_infinity c}) :
    ((basin_polar_green_map c z : {w : ℂ // 1 < ‖w‖}) : ℂ) = polar_green_map c z := rfl

/-- The basin-valued constructive coordinate has the expected Green-function
modulus. -/
lemma norm_basin_polar_green_map_eq_exp_green (c : ℂ)
    (z : {z : ℂ // z ∈ basin_of_infinity c}) :
    ‖((basin_polar_green_map c z : {w : ℂ // 1 < ‖w‖}) : ℂ)‖ =
      Real.exp (green_function c z) := by
  simpa using norm_polar_green_map_eq_exp_green c z

/-- Continuity of the explicit constructive coordinate away from `0`. -/
lemma polar_green_map_continuousAt_of_ne_zero (c z : ℂ) (hz : z ≠ 0) :
    ContinuousAt (polar_green_map c) z :=
  polar_green_map_continuousAt_of_ne_zero_outsidePlan c z hz

/-- The basin-valued constructive coordinate is continuous away from `0` on the
subspace basin. -/
lemma basin_polar_green_map_continuousAt_of_ne_zero (c : ℂ)
    (z : {z : ℂ // z ∈ basin_of_infinity c}) (hz : (z : ℂ) ≠ 0) :
    ContinuousAt (fun w : {z : ℂ // z ∈ basin_of_infinity c} =>
      (((basin_polar_green_map c w : {u : ℂ // 1 < ‖u‖}) : ℂ))) z := by
  simpa [basin_polar_green_map] using
    (polar_green_map_continuousAt_of_ne_zero c (z : ℂ) hz).comp
      continuous_subtype_val.continuousAt

/-- Exact ray formula for the constructive coordinate. -/
lemma polar_green_map_apply_ray (c u : ℂ) (hu : ‖u‖ = 1) (ρ : ℝ) (hρ : 0 < ρ) :
    polar_green_map c ((ρ : ℂ) * u) =
      u * ↑(Real.exp (green_function c ((ρ : ℂ) * u))) := by
  have hu0 : u ≠ 0 := by
    intro hu'
    simpa [hu'] using hu
  have hρ0 : ((ρ : ℂ)) ≠ 0 := by
    exact_mod_cast (ne_of_gt hρ)
  have hz0 : ((ρ : ℂ) * u) ≠ 0 := mul_ne_zero hρ0 hu0
  have hnorm : ‖((ρ : ℂ) * u)‖ = ρ := by
    calc
      ‖((ρ : ℂ) * u)‖ = ‖((ρ : ℂ))‖ * ‖u‖ := by simpa using norm_mul (ρ : ℂ) u
      _ = |ρ| * 1 := by simp [Complex.norm_real, hu]
      _ = ρ := by simp [abs_of_pos hρ]
  have hnormC : (‖((ρ : ℂ) * u)‖ : ℂ) = (ρ : ℂ) := by
    exact_mod_cast hnorm
  have hdir' : ((ρ : ℂ) * u) / (ρ : ℂ) = u := by
    field_simp [hρ0]
  have hdir : ((ρ : ℂ) * u) / (‖((ρ : ℂ) * u)‖ : ℂ) = u := by
    rw [hnormC]
    exact hdir'
  calc
    polar_green_map c ((ρ : ℂ) * u)
        = ((((ρ : ℂ) * u) / (‖((ρ : ℂ) * u)‖ : ℂ)) *
            ↑(Real.exp (green_function c ((ρ : ℂ) * u)))) := by
              simp [polar_green_map, hz0]
    _ = u * ↑(Real.exp (green_function c ((ρ : ℂ) * u))) := by rw [hdir]

/-- The explicit constructive coordinate is normalized at infinity. -/
lemma tendsto_polar_green_map_div_atInfinity (c : ℂ) :
    Tendsto (fun z => (polar_green_map c z) / z) atInfinity (𝓝 (1 : ℂ)) := by
  have hgreen := tendsto_green_function_minus_log_norm_atInfinity c
  have hExpR :
      Tendsto (fun z => Real.exp (green_function c z - Real.log ‖z‖))
        atInfinity (𝓝 (Real.exp (0 : ℝ))) :=
    (Real.continuous_exp.tendsto (0 : ℝ)).comp hgreen
  have hExpR' :
      Tendsto (fun z => Real.exp (green_function c z - Real.log ‖z‖))
        atInfinity (𝓝 (1 : ℝ)) := by
    simpa using hExpR
  have hExpC :
      Tendsto (fun z => ((Real.exp (green_function c z - Real.log ‖z‖)) : ℂ))
        atInfinity (𝓝 (1 : ℂ)) := by
    exact (Filter.tendsto_ofReal_iff).2 hExpR'
  have hpos : ∀ᶠ z in atInfinity, 0 < ‖z‖ :=
    eventually_atInfinity_norm_gt (0 : ℝ)
  have hratio :
      (fun z => (polar_green_map c z) / z) =ᶠ[atInfinity]
        fun z => ((Real.exp (green_function c z - Real.log ‖z‖)) : ℂ) := by
    refine hpos.mono ?_
    intro z hz
    have hz' : z ≠ 0 := (norm_ne_zero_iff).1 (ne_of_gt hz)
    have hz'' : (‖z‖ : ℝ) ≠ 0 := ne_of_gt hz
    have hz''' : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hz''
    have happly :
        polar_green_map c z = (z / ↑‖z‖) * ↑(Real.exp (green_function c z)) := by
      simp [polar_green_map, hz']
    calc
      (polar_green_map c z) / z
          = ((z / ↑‖z‖) * (Real.exp (green_function c z)) : ℂ) / z := by
              rw [happly]
      _ = ((Real.exp (green_function c z)) : ℂ) / (‖z‖ : ℂ) := by
            field_simp [hz', hz''', mul_comm, mul_left_comm, mul_assoc]
      _ = ((Real.exp (green_function c z - Real.log ‖z‖)) : ℂ) := by
            simp [Real.exp_sub, Real.exp_log hz, div_eq_mul_inv]
  exact (tendsto_congr' hratio).2 hExpC

/-- Optional theorem-facing summary of the constructive basin-valued coordinate
carried by the explicit proxy. -/
def ConstructiveBasinBottcherCoordinateData (c : ℂ) : Prop :=
  ∃ φ : ℂ → ℂ,
    (∀ z, z ∈ basin_of_infinity c → 1 < ‖φ z‖) ∧
    (∀ z, ‖φ z‖ = Real.exp (green_function c z)) ∧
    (∀ z, z ≠ 0 → ContinuousAt φ z) ∧
    Tendsto (fun z => φ z / z) atInfinity (𝓝 (1 : ℂ)) ∧
    (∀ u : ℂ, ‖u‖ = 1 → ∀ ρ : ℝ, 0 < ρ →
      φ ((ρ : ℂ) * u) = u * ↑(Real.exp (green_function c ((ρ : ℂ) * u))))

/-- Phase-1 theorem-facing package for the classical global Böttcher proof:
holomorphic near infinity on the canonical outside-open region, conjugates the
quadratic map there, is exterior-valued there, and is normalized at infinity. -/
def GenuineBottcherNearInfinityDataFor (c : ℂ) (φ : ℂ → ℂ) : Prop :=
  (∀ z, ‖z‖ > ‖c‖ + 2 → 1 < ‖φ z‖) ∧
  (∀ z, ‖z‖ > ‖c‖ + 2 → φ (MLC.quadratic_map c z) = (φ z)^2) ∧
  DifferentiableOn ℂ φ {z : ℂ | ‖z‖ > ‖c‖ + 2} ∧
  Tendsto (fun z => φ z / z) atInfinity (𝓝 (1 : ℂ))

/-- Bundled single-parameter Phase-1 route. -/
def GenuineBottcherNearInfinityRouteFor (c : ℂ) : Prop :=
  ∃ φ : ℂ → ℂ, GenuineBottcherNearInfinityDataFor c φ

/-- Candidate 8/10/11 now supplies the canonical near-infinity Böttcher package:
the logarithmic-series coordinate is exterior-valued and conjugates to squaring
on the canonical outside-open region, is differentiable there, and is normalized
at infinity. -/
theorem genuineBottcherNearInfinityDataFor_logSeriesBottcherApprox (c : ℂ) :
    GenuineBottcherNearInfinityDataFor c (MLC.logSeriesBottcherApprox c) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z hz
    exact MLC.one_lt_norm_logSeriesBottcherApprox_of_outside_open c hz
  · intro z hz
    exact MLC.logSeriesBottcherApprox_conj_of_large_radius c (R := ‖c‖ + 2) le_rfl hz
  · exact MLC.logSeriesBottcherApprox_differentiableOn_large_radius c (R := ‖c‖ + 2) le_rfl
  · exact MLC.tendsto_logSeriesBottcherApprox_div_atInfinity c

/-- Existential near-infinity route supplied by the logarithmic-series
coordinate. -/
theorem genuineBottcherNearInfinityRouteFor_logSeriesBottcherApprox (c : ℂ) :
    GenuineBottcherNearInfinityRouteFor c :=
  ⟨MLC.logSeriesBottcherApprox c,
    genuineBottcherNearInfinityDataFor_logSeriesBottcherApprox c⟩

/-- Every basin point eventually enters the canonical outside-open region. -/
lemma exists_iterate_mem_outside_open_of_mem_basin
    (c z : ℂ) (hz : z ∈ basin_of_infinity c) :
    ∃ n : ℕ, ‖(MLC.quadratic_map c)^[n] z‖ > ‖c‖ + 2 := by
  have htend :
      Tendsto (fun n : ℕ => ‖(MLC.quadratic_map c)^[n] z‖) atTop atTop := by
    simpa [basin_of_infinity, MLC.basin_of_infinity] using hz
  have hevent := (Filter.tendsto_atTop.1 htend) (‖c‖ + 3)
  rcases (Filter.eventually_atTop.1 hevent) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  have hN' : ‖c‖ + 3 ≤ ‖(MLC.quadratic_map c)^[N] z‖ := hN N le_rfl
  linarith

/-- A concrete escape time for basin points. -/
noncomputable def basinEscapeTime (c z : ℂ) (hz : z ∈ basin_of_infinity c) : ℕ :=
  Nat.find (exists_iterate_mem_outside_open_of_mem_basin c z hz)

lemma basinEscapeTime_spec (c z : ℂ) (hz : z ∈ basin_of_infinity c) :
    ‖(MLC.quadratic_map c)^[basinEscapeTime c z hz] z‖ > ‖c‖ + 2 :=
  Nat.find_spec (exists_iterate_mem_outside_open_of_mem_basin c z hz)

/-- If a point is already in the canonical outside-open region, its chosen
escape time is zero. -/
lemma basinEscapeTime_eq_zero_of_outside_open
    (c z : ℂ) (hz : ‖z‖ > ‖c‖ + 2) :
    basinEscapeTime c z
      (outside_disk_subset_quadratic_basin c
        (outside_open_subset_outside_disk c hz)) = 0 := by
  exact (Nat.find_eq_zero _).2 (by simpa using hz)

/-- Principal-branch pullback candidate for extending the near-infinity
logarithmic-series coordinate to a basin point. This is a concrete candidate,
but the principal-root branch still requires independence and holomorphicity
proofs before it can witness the classical theorem. -/
noncomputable def principalPullbackLogSeriesBottcher
    (c z : ℂ) (hz : z ∈ basin_of_infinity c) : ℂ :=
  (MLC.logSeriesBottcherApprox c
      ((MLC.quadratic_map c)^[basinEscapeTime c z hz] z)) ^
    (((2 : ℂ) ^ basinEscapeTime c z hz)⁻¹)

/-- On the canonical outside-open region, the principal pullback agrees with the
near-infinity logarithmic-series coordinate. -/
lemma principalPullbackLogSeriesBottcher_eq_near_of_outside_open
    (c z : ℂ) (hz : ‖z‖ > ‖c‖ + 2) :
    principalPullbackLogSeriesBottcher c z
      (outside_disk_subset_quadratic_basin c
        (outside_open_subset_outside_disk c hz)) =
      MLC.logSeriesBottcherApprox c z := by
  have hesc := basinEscapeTime_eq_zero_of_outside_open c z hz
  simp [principalPullbackLogSeriesBottcher, hesc]

/-- Total basin-extension candidate: use the principal pullback on the basin and
the near-infinity formula off the basin. The off-basin branch is only a totality
convention and is not part of the theorem-facing classical data. -/
noncomputable def basinLogSeriesExtensionCandidate (c z : ℂ) : ℂ :=
  by
    classical
    exact
      if hz : z ∈ basin_of_infinity c then
        principalPullbackLogSeriesBottcher c z hz
      else
        MLC.logSeriesBottcherApprox c z

/-- The total basin-extension candidate agrees with the near-infinity formula on
the canonical outside-open region. This proves the first field of the
Route-A coherent-data target. -/
lemma basinLogSeriesExtensionCandidate_extends_near
    (c z : ℂ) (hz : ‖z‖ > ‖c‖ + 2) :
    basinLogSeriesExtensionCandidate c z = MLC.logSeriesBottcherApprox c z := by
  classical
  let hbasin : z ∈ basin_of_infinity c :=
    outside_disk_subset_quadratic_basin c
      (outside_open_subset_outside_disk c hz)
  simp [basinLogSeriesExtensionCandidate, hbasin,
    principalPullbackLogSeriesBottcher_eq_near_of_outside_open c z hz]

/-- Exact remaining basin-extension seam for the logarithmic-series coordinate.
Supplying this data upgrades the already-checked near-infinity package to the
classical global Böttcher data. -/
structure LogSeriesBasinExtensionDataFor (c : ℂ) where
  phi : ℂ → ℂ
  extends_near :
    ∀ z : ℂ, ‖z‖ > ‖c‖ + 2 → phi z = MLC.logSeriesBottcherApprox c z
  norm_on_basin :
    ∀ z : ℂ, z ∈ basin_of_infinity c → 1 < ‖phi z‖
  basin_of_norm_gt_one :
    ∀ z : ℂ, 1 < ‖phi z‖ → z ∈ basin_of_infinity c
  conj_on_basin :
    ∀ z : ℂ, z ∈ basin_of_infinity c →
      phi (MLC.quadratic_map c z) = (phi z)^2
  holo_on_basin :
    DifferentiableOn ℂ phi (basin_of_infinity c)
  modulus_on_basin :
    ∀ z : ℂ, z ∈ basin_of_infinity c →
      ‖phi z‖ = Real.exp (green_function c z)
  tendsto_div_atInfinity :
    Tendsto (fun z => phi z / z) atInfinity (𝓝 (1 : ℂ))

/-- Route A seam for the principal pullback candidate. These are exactly the
coherent-branch facts still missing after defining
`basinLogSeriesExtensionCandidate`: agreement with the near-infinity formula,
basin exterior-valuedness, basin characterization, semiconjugacy, holomorphicity,
modulus identity, and normalization. -/
structure PrincipalPullbackCoherentDataFor (c : ℂ) where
  extends_near :
    ∀ z : ℂ, ‖z‖ > ‖c‖ + 2 →
      basinLogSeriesExtensionCandidate c z = MLC.logSeriesBottcherApprox c z
  norm_on_basin :
    ∀ z : ℂ, z ∈ basin_of_infinity c →
      1 < ‖basinLogSeriesExtensionCandidate c z‖
  basin_of_norm_gt_one :
    ∀ z : ℂ, 1 < ‖basinLogSeriesExtensionCandidate c z‖ →
      z ∈ basin_of_infinity c
  conj_on_basin :
    ∀ z : ℂ, z ∈ basin_of_infinity c →
      basinLogSeriesExtensionCandidate c (MLC.quadratic_map c z) =
        (basinLogSeriesExtensionCandidate c z)^2
  holo_on_basin :
    DifferentiableOn ℂ (basinLogSeriesExtensionCandidate c) (basin_of_infinity c)
  modulus_on_basin :
    ∀ z : ℂ, z ∈ basin_of_infinity c →
      ‖basinLogSeriesExtensionCandidate c z‖ = Real.exp (green_function c z)
  tendsto_div_atInfinity :
    Tendsto (fun z => basinLogSeriesExtensionCandidate c z / z) atInfinity (𝓝 (1 : ℂ))

/-- Coherent data for the principal pullback candidate is exactly enough to fill
the logarithmic-series basin extension seam. -/
noncomputable def PrincipalPullbackCoherentDataFor.toLogSeriesBasinExtensionDataFor
    {c : ℂ} (h : PrincipalPullbackCoherentDataFor c) :
    LogSeriesBasinExtensionDataFor c where
  phi := basinLogSeriesExtensionCandidate c
  extends_near := h.extends_near
  norm_on_basin := h.norm_on_basin
  basin_of_norm_gt_one := h.basin_of_norm_gt_one
  conj_on_basin := h.conj_on_basin
  holo_on_basin := h.holo_on_basin
  modulus_on_basin := h.modulus_on_basin
  tendsto_div_atInfinity := h.tendsto_div_atInfinity

/-- Candidate 9 works in the inverted coordinate `w = 1 / z`, where infinity
for `z ↦ z^2 + c` becomes the superattracting fixed point `w = 0`. -/
noncomputable def invertedQuadraticMap (c : ℂ) (w : ℂ) : ℂ :=
  w ^ 2 / (1 + c * w ^ 2)

/-- Pull a local Böttcher coordinate at `w = 0` back to a near-infinity
coordinate in the original `z`-plane. -/
noncomputable def infinityCoordinateOfInvertedLocal (ψ : ℂ → ℂ) (z : ℂ) : ℂ :=
  (ψ z⁻¹)⁻¹

/-- The algebraic identity relating the inverted quadratic dynamics to the
original dynamics away from the pole and preimage of zero. -/
lemma invertedQuadraticMap_inv_eq_inv_quadratic
    (c z : ℂ) (hz : z ≠ 0) (hq : MLC.quadratic_map c z ≠ 0) :
    invertedQuadraticMap c z⁻¹ = (MLC.quadratic_map c z)⁻¹ := by
  have hquad_ne : z ^ 2 + c ≠ 0 := by
    simpa [MLC.quadratic_map] using hq
  have hzpow : z ^ 2 ≠ 0 := pow_ne_zero 2 hz
  have hden_eq : 1 + c * z⁻¹ ^ 2 = (z ^ 2 + c) / z ^ 2 := by
    field_simp [hz]
  have hden : 1 + c * z⁻¹ ^ 2 ≠ 0 := by
    rw [hden_eq]
    exact div_ne_zero hquad_ne hzpow
  calc
    invertedQuadraticMap c z⁻¹ = z⁻¹ ^ 2 / (1 + c * z⁻¹ ^ 2) := by
      simp [invertedQuadraticMap]
    _ = (z ^ 2 + c)⁻¹ := by
      rw [hden_eq]
      field_simp [hz, hzpow, hquad_ne]
    _ = (MLC.quadratic_map c z)⁻¹ := by
      simp [MLC.quadratic_map]

/-- The naive local coordinate `ψ(w)=w` does not conjugate the inverted map to
squaring, except at degenerate points. Candidate 9 therefore needs a genuine
local Böttcher correction, not just the inversion coordinate itself. -/
lemma invertedQuadraticMap_ne_sq_of_mul_ne_zero
    {c w : ℂ} (hden : 1 + c * w ^ 2 ≠ 0) (hcw : c * w ^ 4 ≠ 0) :
    invertedQuadraticMap c w ≠ w ^ 2 := by
  intro heq
  have hdiv : w ^ 2 / (1 + c * w ^ 2) = w ^ 2 := by
    simpa [invertedQuadraticMap] using heq
  have hmul : w ^ 2 = w ^ 2 * (1 + c * w ^ 2) := by
    rw [div_eq_iff hden] at hdiv
    exact hdiv
  have hzero : w ^ 2 * (c * w ^ 2) = 0 := by
    calc
      w ^ 2 * (c * w ^ 2)
          = w ^ 2 * (1 + c * w ^ 2) - w ^ 2 := by ring
      _ = 0 := by
          rw [← hmul]
          ring
  have hcw4 : c * w ^ 4 = w ^ 2 * (c * w ^ 2) := by ring
  exact hcw (by simpa [hcw4] using hzero)

/-- Concrete `c = 2` witness that the identity local coordinate fails. -/
lemma invertedQuadraticMap_half_ne_half_sq_two :
    invertedQuadraticMap (2 : ℂ) ((1 : ℂ) / 2) ≠ ((1 : ℂ) / 2) ^ 2 := by
  apply invertedQuadraticMap_ne_sq_of_mul_ne_zero
  · norm_num
  · norm_num

/-- No nonzero scalar-linear local coordinate `ψ(w)=a*w` conjugates the inverted
`c=2` dynamics to squaring on even a small disk. Candidate 9 therefore cannot be
completed by a closed-form linear Laurent coordinate; it needs genuine higher
order local Böttcher coefficients. -/
lemma not_exists_linear_invertedLocalConj_two :
    ¬ ∃ a : ℂ, a ≠ 0 ∧
      (∀ w : ℂ, ‖w‖ < 1 →
        a * invertedQuadraticMap (2 : ℂ) w = (a * w) ^ 2) := by
  rintro ⟨a, ha, hconj⟩
  have hhalf := hconj ((1 : ℂ) / 2) (by norm_num)
  have hthird := hconj ((1 : ℂ) / 3) (by norm_num)
  have ha_half : a = (2 : ℂ) / 3 := by
    norm_num [invertedQuadraticMap, pow_two] at hhalf
    field_simp [ha] at hhalf
    calc
      a = (a * 6) / 6 := by norm_num
      _ = ((2 : ℂ) ^ 2) / 6 := by rw [hhalf]
      _ = (2 : ℂ) / 3 := by norm_num
  have ha_third : a = (9 : ℂ) / 11 := by
    norm_num [invertedQuadraticMap, pow_two] at hthird
    field_simp [ha] at hthird
    calc
      a = (a * 11) / 11 := by norm_num
      _ = ((3 : ℂ) ^ 2) / 11 := by rw [hthird]
      _ = (9 : ℂ) / 11 := by norm_num
  have hneq : ((2 : ℂ) / 3) ≠ (9 : ℂ) / 11 := by norm_num
  exact hneq (ha_half.symm.trans ha_third)

/-- Candidate-9 local theorem surface. This is intentionally local at the
superattracting fixed point of the inverted map. The hard missing theorem is to
construct such data from a local analytic fixed-point/power-series argument. -/
structure InvertedLocalBottcherDataFor (c : ℂ) where
  radius : ℝ
  radius_pos : 0 < radius
  psi : ℂ → ℂ
  exterior_to_local :
    ∀ z : ℂ, ‖z‖ > ‖c‖ + 2 → ‖z⁻¹‖ < radius
  local_nonzero :
    ∀ z : ℂ, ‖z‖ > ‖c‖ + 2 → psi z⁻¹ ≠ 0
  local_maps_unit :
    ∀ z : ℂ, ‖z‖ > ‖c‖ + 2 → ‖psi z⁻¹‖ < 1
  local_conj :
    ∀ w : ℂ, ‖w‖ < radius →
      psi (invertedQuadraticMap c w) = (psi w)^2
  local_differentiable :
    DifferentiableOn ℂ psi (Metric.ball 0 radius)
  normalization_at_zero :
    Tendsto (fun w : ℂ => w / psi w) (𝓝 (0 : ℂ)) (𝓝 (1 : ℂ))

/-- The original-plane coordinate associated to Candidate-9 local data. -/
noncomputable def InvertedLocalBottcherDataFor.nearInfinityPhi
    {c : ℂ} (h : InvertedLocalBottcherDataFor c) : ℂ → ℂ :=
  infinityCoordinateOfInvertedLocal h.psi

/-- Candidate 9 is sufficient for the checked near-infinity Böttcher interface.
This reduction is formalized; what remains missing is the local analytic theorem
constructing `InvertedLocalBottcherDataFor c`. -/
theorem InvertedLocalBottcherDataFor.toGenuineBottcherNearInfinityDataFor
    {c : ℂ} (h : InvertedLocalBottcherDataFor c) :
    GenuineBottcherNearInfinityDataFor c h.nearInfinityPhi := by
  let S : Set ℂ := {z : ℂ | ‖z‖ > ‖c‖ + 2}
  have hzne : ∀ z ∈ S, z ≠ 0 := by
    intro z hz hzero
    have hzgt : ‖z‖ > ‖c‖ + 2 := hz
    have hznorm : ‖z‖ = 0 := by
      simp [hzero]
    have hzpos : 0 < ‖z‖ := by
      have hc_nonneg : 0 ≤ ‖c‖ := norm_nonneg c
      linarith [hzgt, hc_nonneg]
    linarith [hzpos, hznorm]
  have hqne : ∀ z ∈ S, MLC.quadratic_map c z ≠ 0 := by
    intro z hz hzero
    have hzge : ‖z‖ ≥ ‖c‖ + 2 := le_of_lt hz
    have hnorm_ge : ‖MLC.quadratic_map c z‖ ≥ ‖z‖ + 1 :=
      quadratic_map_norm_ge_add_one c z hzge
    have hzpos : 0 < ‖z‖ + 1 := by
      have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
      linarith
    have hnorm_pos : 0 < ‖MLC.quadratic_map c z‖ := lt_of_lt_of_le hzpos hnorm_ge
    simpa [hzero] using hnorm_pos
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z hz
    have hpsi_ne : h.psi z⁻¹ ≠ 0 := h.local_nonzero z hz
    have hpsi_lt : ‖h.psi z⁻¹‖ < 1 := h.local_maps_unit z hz
    have hpsi_pos : 0 < ‖h.psi z⁻¹‖ := norm_pos_iff.2 hpsi_ne
    have hinv_norm : ‖(h.psi z⁻¹)⁻¹‖ = (‖h.psi z⁻¹‖)⁻¹ := norm_inv _
    have hone_lt : 1 < (‖h.psi z⁻¹‖)⁻¹ := by
      rw [one_lt_inv₀ hpsi_pos]
      exact hpsi_lt
    simpa [InvertedLocalBottcherDataFor.nearInfinityPhi,
      infinityCoordinateOfInvertedLocal, hinv_norm] using hone_lt
  · intro z hz
    have hzS : z ∈ S := hz
    have hz_ne : z ≠ 0 := hzne z hzS
    have hq_ne : MLC.quadratic_map c z ≠ 0 := hqne z hzS
    have hzloc : ‖z⁻¹‖ < h.radius := h.exterior_to_local z hz
    have hconj := h.local_conj z⁻¹ hzloc
    have hinv_dyn :
        invertedQuadraticMap c z⁻¹ = (MLC.quadratic_map c z)⁻¹ :=
      invertedQuadraticMap_inv_eq_inv_quadratic c z hz_ne hq_ne
    calc
      h.nearInfinityPhi (MLC.quadratic_map c z)
          = (h.psi (MLC.quadratic_map c z)⁻¹)⁻¹ := by
              rfl
      _ = (h.psi (invertedQuadraticMap c z⁻¹))⁻¹ := by
              rw [hinv_dyn]
      _ = ((h.psi z⁻¹)^2)⁻¹ := by
              rw [hconj]
      _ = ((h.psi z⁻¹)⁻¹)^2 := by
              simp [inv_pow]
      _ = (h.nearInfinityPhi z)^2 := by
              rfl
  · have hinv_diff : DifferentiableOn ℂ (fun z : ℂ => z⁻¹) S := by
      refine (differentiableOn_inv (𝕜 := ℂ) (R := ℂ)).mono ?_
      intro z hz
      exact hzne z hz
    have hcomp :
        DifferentiableOn ℂ (fun z : ℂ => h.psi z⁻¹) S := by
      refine h.local_differentiable.comp hinv_diff ?_
      intro z hz
      simpa [Metric.mem_ball, dist_eq_norm] using h.exterior_to_local z hz
    have hcomp_ne : ∀ z ∈ S, h.psi z⁻¹ ≠ 0 := by
      intro z hz
      exact h.local_nonzero z hz
    exact hcomp.inv hcomp_ne
  · have hinv_tendsto :
        Tendsto (fun z : ℂ => z⁻¹) atInfinity (𝓝 (0 : ℂ)) := by
      simpa using tendsto_atInfinity_inv_pow_zero (k := 1) (by norm_num : 0 < 1)
    have hratio_tendsto :
        Tendsto (fun z : ℂ => z⁻¹ / h.psi z⁻¹) atInfinity (𝓝 (1 : ℂ)) :=
      h.normalization_at_zero.comp hinv_tendsto
    have hzne_eventually : ∀ᶠ z in atInfinity, z ≠ 0 := by
      have hpos : ∀ᶠ z in atInfinity, 0 < ‖z‖ :=
        eventually_atInfinity_norm_gt (0 : ℝ)
      exact hpos.mono (fun _ hz => (norm_ne_zero_iff).1 (ne_of_gt hz))
    have hEq :
        (fun z : ℂ => h.nearInfinityPhi z / z)
          =ᶠ[atInfinity] fun z : ℂ => z⁻¹ / h.psi z⁻¹ := by
      filter_upwards [hzne_eventually] with z hz
      calc
        h.nearInfinityPhi z / z = (h.psi z⁻¹)⁻¹ / z := by
          rfl
        _ = z⁻¹ / h.psi z⁻¹ := by
          field_simp [hz, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    exact (tendsto_congr' hEq).2 hratio_tendsto

/-- Candidate-9 theorem surface: a local inverted Böttcher theorem is enough to
produce the near-infinity phase of the genuine route. -/
def InvertedLocalBottcherTheoremFor (c : ℂ) : Prop :=
  Nonempty (InvertedLocalBottcherDataFor c)

theorem genuineBottcherNearInfinityRouteFor_of_invertedLocalBottcherTheoremFor
    {c : ℂ} (h : InvertedLocalBottcherTheoremFor c) :
    GenuineBottcherNearInfinityRouteFor c := by
  rcases h with ⟨hlocal⟩
  exact ⟨hlocal.nearInfinityPhi,
    hlocal.toGenuineBottcherNearInfinityDataFor⟩

/-- The theorem-facing coordinate package matching the current genuine Böttcher
proof sketch: holomorphic and exterior-valued exactly on the basin, conjugates
the quadratic map to squaring on the basin, has the Green-function modulus
there, is continuous on the basin away from `0`, and is normalized at
infinity. -/
def GenuineBottcherCoordinateDataFor (c : ℂ) (φ : ℂ → ℂ) : Prop :=
  (∀ z, z ∈ basin_of_infinity c → 1 < ‖φ z‖) ∧
  (∀ z, 1 < ‖φ z‖ → z ∈ basin_of_infinity c) ∧
  (∀ z, z ∈ basin_of_infinity c → φ (MLC.quadratic_map c z) = (φ z)^2) ∧
  (∀ z, z ∈ basin_of_infinity c → ‖φ z‖ = Real.exp (green_function c z)) ∧
  DifferentiableOn ℂ φ (basin_of_infinity c) ∧
  (∀ z, z ∈ basin_of_infinity c → z ≠ 0 → ContinuousAt φ z) ∧
  Tendsto (fun z => φ z / z) atInfinity (𝓝 (1 : ℂ))

/-- Theorem-facing inverse-package hypotheses matching the second proof sketch:
surjectivity onto the exterior together with injectivity on the outside-open
region. -/
def GenuineBottcherInversePackageFor (c : ℂ) (φ : ℂ → ℂ) : Prop :=
  (∀ w : ℂ, 1 < ‖w‖ → ∃ z : ℂ, φ z = w) ∧
  Set.InjOn φ {z : ℂ | ‖z‖ > ‖c‖ + 2}

/-- Missing analytic input for upgrading the current theorem-facing
`proxy_bottcher_map := polar_green_map` proxy to a genuine coordinate on the whole
basin: every basin point admits a neighborhood contained in the slit-orbit
domain used by the analytic Böttcher approximants. -/
def BottcherBasinLocalAnalyticityHyp (c : ℂ) : Prop :=
  ∀ z : ℂ, z ∈ basin_of_infinity c → slit_orbit c ∈ 𝓝 z

/-- Bundled theorem-facing route matching the current pair of proof sketches. -/
def GenuineBottcherRouteFor (c : ℂ) : Prop :=
  ∃ φ : ℂ → ℂ,
    GenuineBottcherCoordinateDataFor c φ ∧
    GenuineBottcherInversePackageFor c φ

/-- Maximal honest coordinate-construction theorem currently supported by the
repository: once the current `proxy_bottcher_map` proxy is known to be locally
analytic at every basin point, its already-formalized dynamical/modulus
properties upgrade it to the full theorem-facing genuine-coordinate package. -/
theorem genuineBottcherCoordinateDataFor_bottcherMap_of_basinLocalAnalyticity
    (c : ℂ) (hslit : BottcherBasinLocalAnalyticityHyp c) :
    GenuineBottcherCoordinateDataFor c (proxy_bottcher_map c) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact
      proxy_bottcher_map_norm_gt_one_of_basin c z hz
        (green_function_pos_of_basin c z hz)
  · intro z hz
    exact proxy_bottcher_map_norm_gt_one_implies_basin c hz
  · intro z hz
    exact bottcher_conj_on_basin c z hz
  · intro z _hz
    exact norm_bottcher_eq_exp_green c z
  · intro z hz
    have hana : AnalyticAt ℂ (proxy_bottcher_map c) z :=
      proxy_bottcher_map_analyticAt_of_mem_nhds_slit_basin c z
        (hslit z hz)
        ((basin_of_infinity_isOpen c).mem_nhds hz)
    exact hana.differentiableAt.differentiableWithinAt
  · intro z hz hzne
    exact proxy_bottcher_map_continuousAt_of_ne_zero c z hzne
  · exact tendsto_proxy_bottcher_map_div_atInfinity c

/-- Existential coordinate-construction form of the current maximal honest
theorem: the missing local-analyticity input on the whole basin is enough to
produce some theorem-facing genuine coordinate, namely the current
`proxy_bottcher_map`. -/
theorem exists_genuineBottcherCoordinateDataFor_of_basinLocalAnalyticity
    (c : ℂ) (hslit : BottcherBasinLocalAnalyticityHyp c) :
    ∃ φ : ℂ → ℂ, GenuineBottcherCoordinateDataFor c φ := by
  exact ⟨proxy_bottcher_map c,
    genuineBottcherCoordinateDataFor_bottcherMap_of_basinLocalAnalyticity c hslit⟩

/-- `0` escapes to infinity for `f(z) = z^2 + 2`, hence belongs to the basin. -/
lemma zero_mem_basin_two_constructive :
    (0 : ℂ) ∈ basin_of_infinity (2 : ℂ) := by
  have h6_basin : (6 : ℂ) ∈ basin_of_infinity (2 : ℂ) := by
    have h6_out : (6 : ℂ) ∈ {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2} := by
      norm_num
    exact outside_disk_subset_quadratic_basin (2 : ℂ) <|
      outside_open_subset_outside_disk (2 : ℂ) h6_out
  have h2_basin : (2 : ℂ) ∈ basin_of_infinity (2 : ℂ) := by
    have h2image : quadratic_map (2 : ℂ) (2 : ℂ) = 6 := by
      norm_num [quadratic_map]
    apply (basin_of_infinity_preimage_subset (2 : ℂ))
    simpa [Set.preimage, h2image] using h6_basin
  have h0image : quadratic_map (2 : ℂ) (0 : ℂ) = 2 := by
    norm_num [quadratic_map]
  apply (basin_of_infinity_preimage_subset (2 : ℂ))
  simpa [Set.preimage, h0image] using h2_basin

/-- The principal-slit approximation domain does not even contain `0`, so it
cannot be a neighborhood of every basin point at `c = 2`. -/
lemma zero_not_mem_slit_orbit_two :
    (0 : ℂ) ∉ slit_orbit (2 : ℂ) := by
  intro hzero
  exact Complex.zero_notMem_slitPlane (by simpa using hzero 0)

/-- Therefore the basin-local analyticity hypothesis needed to upgrade the
current proxy to a genuine coordinate is false at `c = 2`. -/
theorem not_bottcherBasinLocalAnalyticityHyp_two :
    ¬ BottcherBasinLocalAnalyticityHyp (2 : ℂ) := by
  intro hslit
  have hnhds : slit_orbit (2 : ℂ) ∈ 𝓝 (0 : ℂ) :=
    hslit 0 zero_mem_basin_two_constructive
  have hmem : (0 : ℂ) ∈ slit_orbit (2 : ℂ) := mem_of_mem_nhds hnhds
  exact zero_not_mem_slit_orbit_two hmem

/-- The current proxy `proxy_bottcher_map = polar_green_map` cannot itself witness the
theorem-facing genuine coordinate package at `c = 2`: differentiability on the
open basin would force continuity at `0`, but the proxy is formally not
continuous there. -/
theorem not_genuineBottcherCoordinateDataFor_bottcherMap_two :
    ¬ GenuineBottcherCoordinateDataFor (2 : ℂ) (proxy_bottcher_map (2 : ℂ)) := by
  intro hcoord
  rcases hcoord with ⟨_, _, _, _, hdiff, _, _⟩
  have h0basin : (0 : ℂ) ∈ basin_of_infinity (2 : ℂ) :=
    zero_mem_basin_two_constructive
  have hcont0 : ContinuousAt (proxy_bottcher_map (2 : ℂ)) 0 := by
    have hdiff0 :
        DifferentiableWithinAt ℂ (proxy_bottcher_map (2 : ℂ))
          (basin_of_infinity (2 : ℂ)) 0 :=
      hdiff 0 h0basin
    exact hdiff0.continuousWithinAt.continuousAt
      ((basin_of_infinity_isOpen (2 : ℂ)).mem_nhds h0basin)
  exact
    polar_green_map_not_continuousAt_zero (2 : ℂ) <|
      by simpa [proxy_bottcher_map] using hcont0

/-- Any function whose pointwise basin values are defined by the existing
principal-branch root sequence must agree with the current proxy on the basin,
since that sequence is already formalized to converge there to
`proxy_bottcher_map`. -/
theorem eq_proxyBottcherMap_on_basin_of_rootSeq_limit
    {c : ℂ} {φ : ℂ → ℂ}
    (hlim : ∀ z : ℂ, z ∈ basin_of_infinity c →
      Tendsto (fun n => bottcher_root_seq c n z) atTop (𝓝 (φ z))) :
    ∀ z : ℂ, z ∈ basin_of_infinity c → φ z = proxy_bottcher_map c z := by
  intro z hz
  exact tendsto_nhds_unique (hlim z hz) (bottcher_root_seq_tendsto_at c hz)

/-- Therefore the current root-sequence limit cannot itself supply a genuine
global coordinate at `c = 2`: it would force continuity of the proxy at `0`,
contradicting the existing obstruction theorem. -/
theorem not_genuineBottcherCoordinateDataFor_of_rootSeq_limit_two
    {φ : ℂ → ℂ}
    (hlim : ∀ z : ℂ, z ∈ basin_of_infinity (2 : ℂ) →
      Tendsto (fun n => bottcher_root_seq (2 : ℂ) n z) atTop (𝓝 (φ z))) :
    ¬ GenuineBottcherCoordinateDataFor (2 : ℂ) φ := by
  intro hcoord
  rcases hcoord with ⟨_, _, _, _, hdiff, _, _⟩
  have h0basin : (0 : ℂ) ∈ basin_of_infinity (2 : ℂ) :=
    zero_mem_basin_two_constructive
  have hcont0 : ContinuousAt φ 0 := by
    have hdiff0 :
        DifferentiableWithinAt ℂ φ (basin_of_infinity (2 : ℂ)) 0 :=
      hdiff 0 h0basin
    exact hdiff0.continuousWithinAt.continuousAt
      ((basin_of_infinity_isOpen (2 : ℂ)).mem_nhds h0basin)
  have hEq :
      φ =ᶠ[𝓝 (0 : ℂ)] proxy_bottcher_map (2 : ℂ) := by
    filter_upwards [(basin_of_infinity_isOpen (2 : ℂ)).mem_nhds h0basin] with z hz
    exact eq_proxyBottcherMap_on_basin_of_rootSeq_limit hlim z hz
  have hproxyCont0 : ContinuousAt (proxy_bottcher_map (2 : ℂ)) 0 :=
    hcont0.congr_of_eventuallyEq hEq.symm
  exact
    polar_green_map_not_continuousAt_zero (2 : ℂ) <|
      by simpa [proxy_bottcher_map] using hproxyCont0

/-- Any full genuine coordinate package restricts to the first near-infinity
phase of the classical proof on the canonical outside-open region. -/
theorem genuineBottcherNearInfinityDataFor_of_genuineBottcherCoordinateDataFor
    {c : ℂ} {φ : ℂ → ℂ}
    (h_coord : GenuineBottcherCoordinateDataFor c φ) :
    GenuineBottcherNearInfinityDataFor c φ := by
  rcases h_coord with
    ⟨h_norm_on_basin, _, h_conj_on_basin, _, h_holo_on_basin, _, h_tendsto⟩
  refine ⟨?_, ?_, ?_, h_tendsto⟩
  · intro z hz
    exact h_norm_on_basin z <|
      outside_disk_subset_quadratic_basin c (outside_open_subset_outside_disk c hz)
  · intro z hz
    exact h_conj_on_basin z <|
      outside_disk_subset_quadratic_basin c (outside_open_subset_outside_disk c hz)
  · refine h_holo_on_basin.mono ?_
    intro z hz
    exact outside_disk_subset_quadratic_basin c (outside_open_subset_outside_disk c hz)

/-- The full genuine Böttcher route automatically contains the Phase-1
near-infinity package. -/
theorem genuineBottcherNearInfinityRouteFor_of_genuineBottcherRouteFor
    {c : ℂ} (h_route : GenuineBottcherRouteFor c) :
    GenuineBottcherNearInfinityRouteFor c := by
  rcases h_route with ⟨φ, h_coord, _h_inv⟩
  exact ⟨φ, genuineBottcherNearInfinityDataFor_of_genuineBottcherCoordinateDataFor h_coord⟩

/-- The missing classical one-parameter global Böttcher theorem should first
produce a near-infinity coordinate on some exterior neighborhood, then extend it
to a global basin coordinate. The existing route consumes only the global
extension, but the exterior witness is recorded here so the formal statement
matches the analytic theorem that still needs to be internalized. -/
structure ClassicalGlobalBottcherDataFor (c : ℂ) where
  R : ℝ
  R_pos : 0 < R
  nearPhi : ℂ → ℂ
  phi : ℂ → ℂ
  norm_on_exterior :
    ∀ z : ℂ, z ∈ exteriorRegion R → 1 < ‖nearPhi z‖
  conj_on_exterior :
    ∀ z : ℂ, z ∈ exteriorRegion R →
      nearPhi (MLC.quadratic_map c z) = (nearPhi z)^2
  near_holo_on_exterior :
    DifferentiableOn ℂ nearPhi (exteriorRegion R)
  extends_nearPhi :
    ∀ z : ℂ, z ∈ exteriorRegion R → phi z = nearPhi z
  norm_on_basin :
    ∀ z : ℂ, z ∈ basin_of_infinity c → 1 < ‖phi z‖
  basin_of_norm_gt_one :
    ∀ z : ℂ, 1 < ‖phi z‖ → z ∈ basin_of_infinity c
  conj_on_basin :
    ∀ z : ℂ, z ∈ basin_of_infinity c →
      phi (MLC.quadratic_map c z) = (phi z)^2
  holo_on_basin :
    DifferentiableOn ℂ phi (basin_of_infinity c)
  modulus_on_basin :
    ∀ z : ℂ, z ∈ basin_of_infinity c →
      ‖phi z‖ = Real.exp (green_function c z)
  tendsto_div_atInfinity :
    Tendsto (fun z => phi z / z) atInfinity (𝓝 (1 : ℂ))

/-- Bundled formulation of the classical global Böttcher theorem at one
parameter. This is now the precise missing analytic theorem for PLAN 06, before
the separate inverse-package step. -/
def ClassicalGlobalBottcherTheoremFor (c : ℂ) : Prop :=
  Nonempty (ClassicalGlobalBottcherDataFor c)

/-- The exact reduction from the remaining logarithmic-series basin-extension
seam to the classical global Böttcher data. -/
noncomputable def LogSeriesBasinExtensionDataFor.toClassicalGlobalBottcherDataFor
    {c : ℂ} (h : LogSeriesBasinExtensionDataFor c) :
    ClassicalGlobalBottcherDataFor c where
  R := ‖c‖ + 2
  R_pos := by
    have hc : 0 ≤ ‖c‖ := norm_nonneg c
    linarith
  nearPhi := MLC.logSeriesBottcherApprox c
  phi := h.phi
  norm_on_exterior := by
    intro z hz
    exact MLC.one_lt_norm_logSeriesBottcherApprox_of_outside_open c (by simpa [exteriorRegion] using hz)
  conj_on_exterior := by
    intro z hz
    exact MLC.logSeriesBottcherApprox_conj_of_large_radius c
      (R := ‖c‖ + 2) le_rfl (by simpa [exteriorRegion] using hz)
  near_holo_on_exterior := by
    simpa [exteriorRegion] using
      MLC.logSeriesBottcherApprox_differentiableOn_large_radius c
        (R := ‖c‖ + 2) le_rfl
  extends_nearPhi := by
    intro z hz
    exact h.extends_near z (by simpa [exteriorRegion] using hz)
  norm_on_basin := h.norm_on_basin
  basin_of_norm_gt_one := h.basin_of_norm_gt_one
  conj_on_basin := h.conj_on_basin
  holo_on_basin := h.holo_on_basin
  modulus_on_basin := h.modulus_on_basin
  tendsto_div_atInfinity := h.tendsto_div_atInfinity

theorem classicalGlobalBottcherTheoremFor_of_logSeriesBasinExtensionData
    {c : ℂ} (h : LogSeriesBasinExtensionDataFor c) :
    ClassicalGlobalBottcherTheoremFor c :=
  ⟨h.toClassicalGlobalBottcherDataFor⟩

theorem classicalGlobalBottcherTheoremFor_of_principalPullbackCoherentData
    {c : ℂ} (h : PrincipalPullbackCoherentDataFor c) :
    ClassicalGlobalBottcherTheoremFor c :=
  classicalGlobalBottcherTheoremFor_of_logSeriesBasinExtensionData
    h.toLogSeriesBasinExtensionDataFor

/-- Basin route B seam: first construct an exterior inverse for the
near-infinity logarithmic-series coordinate, then use inverse dynamics to supply
the global basin extension data. This separates the inverse-package strategy
from the principal-root pullback strategy. -/
structure LogSeriesExteriorInverseBasinExtensionDataFor (c : ℂ) where
  inverseOnExterior : ℂ → ℂ
  extensionData : LogSeriesBasinExtensionDataFor c
  right_inverse :
    ∀ w : ℂ, 1 < ‖w‖ →
      extensionData.phi (inverseOnExterior w) = w
  left_inverse_on_outside :
    ∀ z : ℂ, ‖z‖ > ‖c‖ + 2 →
      inverseOnExterior (MLC.logSeriesBottcherApprox c z) = z

theorem classicalGlobalBottcherTheoremFor_of_logSeriesExteriorInverseBasinExtensionData
    {c : ℂ} (h : LogSeriesExteriorInverseBasinExtensionDataFor c) :
    ClassicalGlobalBottcherTheoremFor c :=
  classicalGlobalBottcherTheoremFor_of_logSeriesBasinExtensionData
    h.extensionData

/-- Basin route C seam: a classical global Böttcher extension theorem can be
used directly once instantiated with the already-proved canonical
near-infinity logarithmic-series coordinate. -/
structure ClassicalGlobalExtensionFromNearInfinityDataFor (c : ℂ) where
  near_data :
    GenuineBottcherNearInfinityDataFor c (MLC.logSeriesBottcherApprox c)
  extensionData : LogSeriesBasinExtensionDataFor c

theorem classicalGlobalBottcherTheoremFor_of_classicalGlobalExtensionFromNearInfinityData
    {c : ℂ} (h : ClassicalGlobalExtensionFromNearInfinityDataFor c) :
    ClassicalGlobalBottcherTheoremFor c :=
  classicalGlobalBottcherTheoremFor_of_logSeriesBasinExtensionData
    h.extensionData

/-- The classical theorem's basin-valued coordinate is automatically nonzero on
the basin since it is exterior-valued there. -/
theorem ClassicalGlobalBottcherDataFor.nonvanishing_on_basin
    {c : ℂ} (h : ClassicalGlobalBottcherDataFor c) :
    ∀ z : ℂ, z ∈ basin_of_infinity c → h.phi z ≠ 0 := by
  intro z hz hzero
  have hnorm : 1 < ‖h.phi z‖ := h.norm_on_basin z hz
  have hnot : ¬ 1 < ‖h.phi z‖ := by simpa [hzero]
  exact hnot hnorm

/-- The classical theorem already contains the theorem-facing global coordinate
package consumed by the current route. -/
theorem ClassicalGlobalBottcherDataFor.toGenuineBottcherCoordinateDataFor
    {c : ℂ} (h : ClassicalGlobalBottcherDataFor c) :
    GenuineBottcherCoordinateDataFor c h.phi := by
  refine
    ⟨h.norm_on_basin, h.basin_of_norm_gt_one, h.conj_on_basin,
      h.modulus_on_basin, h.holo_on_basin, ?_, h.tendsto_div_atInfinity⟩
  intro z hz _hne
  exact
    (h.holo_on_basin z hz).continuousWithinAt.continuousAt
      ((basin_of_infinity_isOpen c).mem_nhds hz)

/-- Hence the classical theorem also contains the already-defined near-infinity
phase on the canonical outside-open region. -/
theorem ClassicalGlobalBottcherDataFor.toGenuineBottcherNearInfinityDataFor
    {c : ℂ} (h : ClassicalGlobalBottcherDataFor c) :
    GenuineBottcherNearInfinityDataFor c h.phi := by
  exact
    genuineBottcherNearInfinityDataFor_of_genuineBottcherCoordinateDataFor
      h.toGenuineBottcherCoordinateDataFor

/-- Once the separate inverse package is supplied for the same global
coordinate, the existing theorem-facing route follows immediately. -/
theorem ClassicalGlobalBottcherDataFor.toGenuineBottcherRouteFor
    {c : ℂ} (h : ClassicalGlobalBottcherDataFor c)
    (h_inv : GenuineBottcherInversePackageFor c h.phi) :
    GenuineBottcherRouteFor c := by
  exact ⟨h.phi, h.toGenuineBottcherCoordinateDataFor, h_inv⟩

/-- In particular, the already-formalized principal-branch root sequence cannot
be used as the witness for the classical global Böttcher theorem at `c = 2`. -/
theorem not_exists_classicalGlobalBottcherDataFor_of_rootSeq_limit_two :
    ¬ ∃ h : ClassicalGlobalBottcherDataFor (2 : ℂ),
        ∀ z : ℂ, z ∈ basin_of_infinity (2 : ℂ) →
          Tendsto (fun n => bottcher_root_seq (2 : ℂ) n z) atTop (𝓝 (h.phi z)) := by
  intro h
  rcases h with ⟨hclassical, hlim⟩
  exact
    not_genuineBottcherCoordinateDataFor_of_rootSeq_limit_two hlim
      hclassical.toGenuineBottcherCoordinateDataFor

/-- Existential coordinate-package consequence of the bundled classical theorem. -/
theorem exists_genuineBottcherCoordinateDataFor_of_classicalGlobalBottcherTheoremFor
    {c : ℂ} (h : ClassicalGlobalBottcherTheoremFor c) :
    ∃ φ : ℂ → ℂ, GenuineBottcherCoordinateDataFor c φ := by
  rcases h with ⟨hclassical⟩
  exact ⟨hclassical.phi, hclassical.toGenuineBottcherCoordinateDataFor⟩

/-- Existential near-infinity consequence of the bundled classical theorem. -/
theorem genuineBottcherNearInfinityRouteFor_of_classicalGlobalBottcherTheoremFor
    {c : ℂ} (h : ClassicalGlobalBottcherTheoremFor c) :
    GenuineBottcherNearInfinityRouteFor c := by
  rcases h with ⟨hclassical⟩
  exact ⟨hclassical.phi, hclassical.toGenuineBottcherNearInfinityDataFor⟩

/-- Any local parameter-family package already contains a uniform near-infinity
parameter family by restricting to a sufficiently large exterior region whose
radius dominates the whole parameter ball around `c₀`. -/
noncomputable def GenuineBottcherLocalParameterFamilyData.toNearInfinityParameterExtensionData
    {c₀ : ℂ} (h : GenuineBottcherLocalParameterFamilyData c₀) :
    GenuineBottcherNearInfinityParameterExtensionData c₀ := by
  refine
    { r := h.r
      R := ‖c₀‖ + h.r + 2
      r_pos := h.r_pos
      R_pos := by
        have hc₀ : 0 ≤ ‖c₀‖ := norm_nonneg c₀
        have hr : 0 < h.r := h.r_pos
        have hsum : 0 < ‖c₀‖ + h.r := by
          linarith
        linarith
      phi := h.phi
      norm_on_exterior := ?_
      conj_on_exterior := ?_
      fiber_holo_on_exterior := ?_
      tendsto_div_atInfinity := h.tendsto_div_atInfinity
      param_holo_on_exterior := ?_
      global := h
      agrees_on_exterior := ?_ }
  · intro c hc z hz
    exact h.norm_on_basin c hc z <| by
      have hc_ball : ‖c - c₀‖ < h.r := by
        simpa [Metric.mem_ball, dist_eq_norm] using hc
      have hcnorm : ‖c‖ < ‖c₀‖ + h.r := by
        have htri : ‖c‖ ≤ ‖c - c₀‖ + ‖c₀‖ := by
          simpa [sub_add_cancel c c₀, add_comm, add_left_comm, add_assoc] using
            (norm_add_le (c - c₀) c₀)
        linarith
      have hz_large : ‖z‖ > ‖c‖ + 2 := by
        have hzR : ‖c₀‖ + h.r + 2 < ‖z‖ := by simpa [exteriorRegion] using hz
        linarith
      exact outside_disk_subset_quadratic_basin c (outside_open_subset_outside_disk c hz_large)
  · intro c hc z hz
    exact h.conj_on_basin c hc z <| by
      have hc_ball : ‖c - c₀‖ < h.r := by
        simpa [Metric.mem_ball, dist_eq_norm] using hc
      have hcnorm : ‖c‖ < ‖c₀‖ + h.r := by
        have htri : ‖c‖ ≤ ‖c - c₀‖ + ‖c₀‖ := by
          simpa [sub_add_cancel c c₀, add_comm, add_left_comm, add_assoc] using
            (norm_add_le (c - c₀) c₀)
        linarith
      have hz_large : ‖z‖ > ‖c‖ + 2 := by
        have hzR : ‖c₀‖ + h.r + 2 < ‖z‖ := by simpa [exteriorRegion] using hz
        linarith
      exact outside_disk_subset_quadratic_basin c (outside_open_subset_outside_disk c hz_large)
  · intro c hc
    refine (h.fiber_holo_on_basin c hc).mono ?_
    intro z hz
    have hc_ball : ‖c - c₀‖ < h.r := by
      simpa [Metric.mem_ball, dist_eq_norm] using hc
    have hcnorm : ‖c‖ < ‖c₀‖ + h.r := by
      have htri : ‖c‖ ≤ ‖c - c₀‖ + ‖c₀‖ := by
        simpa [sub_add_cancel c c₀, add_comm, add_left_comm, add_assoc] using
          (norm_add_le (c - c₀) c₀)
      linarith
    have hz_large : ‖z‖ > ‖c‖ + 2 := by
      have hzR : ‖c₀‖ + h.r + 2 < ‖z‖ := by simpa [exteriorRegion] using hz
      linarith
    exact outside_disk_subset_quadratic_basin c (outside_open_subset_outside_disk c hz_large)
  · intro z _hz
    exact h.param_holo z
  · intro c hc z hz
    rfl

/-- Forget only the global-extension component of the stronger restricted
near-infinity package. -/
noncomputable def GenuineBottcherLocalParameterFamilyData.toNearInfinityParameterFamilyData
    {c₀ : ℂ} (h : GenuineBottcherLocalParameterFamilyData c₀) :
    GenuineBottcherNearInfinityParameterFamilyData c₀ :=
  (h.toNearInfinityParameterExtensionData).toNearInfinityParameterFamilyData

/-- Constructive realization of the missing basin-valued Böttcher coordinate
using the explicit proxy `polar_green_map`. -/
theorem constructive_basin_bottcher_coordinate_data (c : ℂ) :
    ConstructiveBasinBottcherCoordinateData c := by
  refine ⟨polar_green_map c, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact one_lt_norm_polar_green_map_of_mem_basin c z hz
  · intro z
    exact norm_polar_green_map_eq_exp_green c z
  · intro z hz
    exact polar_green_map_continuousAt_of_ne_zero c z hz
  · exact tendsto_polar_green_map_div_atInfinity c
  · intro u hu ρ hρ
    exact polar_green_map_apply_ray c u hu ρ hρ

end Quadratic

end MLC
