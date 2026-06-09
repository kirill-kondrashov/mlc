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

/-!
### Algebraic root-choice torsors

The basin pullback obstruction can be separated into an algebraic finite-level
part and an analytic coherence part. The definitions below formalize the
finite-level group-theoretic picture: roots of a pullback equation form a torsor
under roots of unity, and the Böttcher equation identifies the level-`N` root set
as the compatible subset of the level-`N+1` root set.
-/

/-- The finite group of `n`-th roots of unity, as a set. -/
def rootsOfUnitySet (n : ℕ) : Set ℂ :=
  {ζ : ℂ | ζ ^ n = 1}

/-- `1` is an `n`-th root of unity for every `n`. -/
lemma one_mem_rootsOfUnitySet (n : ℕ) :
    (1 : ℂ) ∈ rootsOfUnitySet n := by
  simp [rootsOfUnitySet]

/-- The finite root set for the pullback equation `w^n = A`. -/
def pullbackRootSet (n : ℕ) (A : ℂ) : Set ℂ :=
  {w : ℂ | w ^ n = A}

/-- Multiplication by an `n`-th root of unity preserves the root set
`{w | w^n = A}`. -/
lemma rootsOfUnity_smul_pullbackRootSet
    {n : ℕ} {A ζ w : ℂ}
    (hζ : ζ ∈ rootsOfUnitySet n) (hw : w ∈ pullbackRootSet n A) :
    ζ * w ∈ pullbackRootSet n A := by
  dsimp [rootsOfUnitySet, pullbackRootSet] at hζ hw ⊢
  rw [mul_pow, hζ, hw, one_mul]

/-- If `A ≠ 0`, any two roots of `w^n = A` differ by an `n`-th root of unity.
This is the algebraic torsor-transitivity statement. -/
lemma pullbackRootSet_torsor_transitive
    {n : ℕ} {A w v : ℂ}
    (hn : n ≠ 0)
    (hw : w ∈ pullbackRootSet n A) (hv : v ∈ pullbackRootSet n A)
    (hA : A ≠ 0) :
    ∃ ζ : ℂ, ζ ∈ rootsOfUnitySet n ∧ v = ζ * w := by
  have hw_ne : w ≠ 0 := by
    intro hzero
    have : A = 0 := by
      simpa [pullbackRootSet, hzero, hn] using hw.symm
    exact hA this
  refine ⟨v / w, ?_, ?_⟩
  · dsimp [rootsOfUnitySet]
    have hw_pow_ne : w ^ n ≠ 0 := by
      rw [show w ^ n = A by simpa [pullbackRootSet] using hw]
      exact hA
    calc
      (v / w) ^ n = v ^ n / w ^ n := by
        simpa using (div_pow v w n)
      _ = A / A := by
        simp [pullbackRootSet] at hw hv
        rw [hv, hw]
      _ = 1 := by
        field_simp [hA]
  · field_simp [hw_ne]

/-- If `B = A^2`, then every root of `w^(2^N)=A` is automatically a compatible
root of `w^(2^(N+1))=B`. This is the finite-level transition map behind
escape-time coherence. -/
lemma pullbackRootSet_subset_next_of_sq
    {N : ℕ} {A B : ℂ} (hB : B = A ^ 2) :
    pullbackRootSet (2 ^ N) A ⊆ pullbackRootSet (2 ^ (N + 1)) B := by
  intro w hw
  dsimp [pullbackRootSet] at hw ⊢
  calc
    w ^ (2 ^ (N + 1)) = (w ^ (2 ^ N)) ^ 2 := by
      simp [pow_mul, pow_succ]
    _ = A ^ 2 := by rw [hw]
    _ = B := hB.symm

/-- For the checked near-infinity coordinate, consecutive orbit values satisfy
the squaring relation whenever the earlier iterate is in the canonical
outside-open region. -/
lemma logSeriesBottcherApprox_iterate_succ_eq_sq
    (c : ℂ) {z : ℂ} {N : ℕ}
    (hN : ‖(MLC.quadratic_map c)^[N] z‖ > ‖c‖ + 2) :
    MLC.logSeriesBottcherApprox c ((MLC.quadratic_map c)^[N + 1] z) =
      (MLC.logSeriesBottcherApprox c ((MLC.quadratic_map c)^[N] z)) ^ 2 := by
  calc
    MLC.logSeriesBottcherApprox c ((MLC.quadratic_map c)^[N + 1] z)
        = MLC.logSeriesBottcherApprox c
            (MLC.quadratic_map c ((MLC.quadratic_map c)^[N] z)) := by
          rw [Function.iterate_succ_apply']
    _ = (MLC.logSeriesBottcherApprox c ((MLC.quadratic_map c)^[N] z)) ^ 2 := by
          exact MLC.logSeriesBottcherApprox_conj_of_large_radius
            c (R := ‖c‖ + 2) le_rfl hN

/-- Concrete root-set transition for the logarithmic-series Böttcher values
along an escaping orbit. -/
lemma logSeries_pullbackRootSet_subset_next
    (c : ℂ) {z : ℂ} {N : ℕ}
    (hN : ‖(MLC.quadratic_map c)^[N] z‖ > ‖c‖ + 2) :
    pullbackRootSet (2 ^ N)
        (MLC.logSeriesBottcherApprox c ((MLC.quadratic_map c)^[N] z))
      ⊆
    pullbackRootSet (2 ^ (N + 1))
        (MLC.logSeriesBottcherApprox c ((MLC.quadratic_map c)^[N + 1] z)) := by
  refine pullbackRootSet_subset_next_of_sq ?_
  exact logSeriesBottcherApprox_iterate_succ_eq_sq c hN

/-- Abstract monodromy representation for pullback root choices. `Loop` is a
placeholder for whatever formal loop/fundamental-group object is eventually used
for the basin. The representation records the root-of-unity multiplier acquired
by analytic continuation of a level-`N` pullback root around a loop. -/
structure PullbackRootMonodromyRepresentation (Loop : Type*) where
  monodromy : ℕ → Loop → ℂ
  monodromy_mem :
    ∀ N γ, monodromy N γ ∈ rootsOfUnitySet (2 ^ N)
  monodromy_compat :
    ∀ N γ, (monodromy (N + 1) γ) ^ 2 = monodromy N γ

/-- Triviality of the pullback-root monodromy representation. -/
def PullbackRootMonodromyRepresentation.Trivial
    {Loop : Type*} (ρ : PullbackRootMonodromyRepresentation Loop) : Prop :=
  ∀ N γ, ρ.monodromy N γ = 1

/-- Monodromy acts on every finite pullback root set by root-of-unity
multiplication. This is the formal version of "continuation around a loop moves
a chosen root to another root in the same torsor." -/
lemma PullbackRootMonodromyRepresentation.smul_pullbackRootSet
    {Loop : Type*} (ρ : PullbackRootMonodromyRepresentation Loop)
    (N : ℕ) (γ : Loop) {A w : ℂ}
    (hw : w ∈ pullbackRootSet (2 ^ N) A) :
    ρ.monodromy N γ * w ∈ pullbackRootSet (2 ^ N) A :=
  rootsOfUnity_smul_pullbackRootSet (ρ.monodromy_mem N γ) hw

/-- If monodromy is trivial, analytic continuation fixes every finite-level
pullback root. This is the algebraic consequence that still has to be supplied
analytically for actual basin loops. -/
lemma PullbackRootMonodromyRepresentation.trivial_smul_eq
    {Loop : Type*} (ρ : PullbackRootMonodromyRepresentation Loop)
    (hρ : ρ.Trivial) (N : ℕ) (γ : Loop) (w : ℂ) :
    ρ.monodromy N γ * w = w := by
  rw [hρ N γ]
  simp

/-- If a compatible monodromy tower is trivial at level `N + d`, then it is
trivial at level `N`. This is the algebraic descent step shown in the PLAN 08
blocker notebook: compatibility says the lower multiplier is the square of the
next one. -/
lemma PullbackRootMonodromyRepresentation.monodromy_eq_one_of_add_eq_one
    {Loop : Type*} (ρ : PullbackRootMonodromyRepresentation Loop)
    (γ : Loop) (N d : ℕ)
    (h : ρ.monodromy (N + d) γ = 1) :
    ρ.monodromy N γ = 1 := by
  induction d with
  | zero =>
      simpa using h
  | succ d ih =>
      have htop : ρ.monodromy (N + d + 1) γ = 1 := by
        simpa [Nat.add_assoc] using h
      have hprev : ρ.monodromy (N + d) γ = 1 := by
        calc
          ρ.monodromy (N + d) γ = (ρ.monodromy ((N + d) + 1) γ) ^ 2 := by
            exact (ρ.monodromy_compat (N + d) γ).symm
          _ = 1 := by rw [htop]; norm_num
      exact ih hprev

lemma PullbackRootMonodromyRepresentation.monodromy_eq_one_of_le_of_top_eq_one
    {Loop : Type*} (ρ : PullbackRootMonodromyRepresentation Loop)
    {γ : Loop} {N K : ℕ}
    (hNK : N ≤ K) (hK : ρ.monodromy K γ = 1) :
    ρ.monodromy N γ = 1 := by
  rcases Nat.exists_eq_add_of_le hNK with ⟨d, rfl⟩
  exact ρ.monodromy_eq_one_of_add_eq_one γ N d hK

/-- Triviality at arbitrarily high levels implies full triviality of a compatible
monodromy representation. One high trivial level only descends to lower levels;
to cover every requested level `N`, we need a trivial level `K ≥ N`. -/
lemma PullbackRootMonodromyRepresentation.trivial_of_arbitrarily_high_trivial
    {Loop : Type*} (ρ : PullbackRootMonodromyRepresentation Loop)
    (hhigh : ∀ (N : ℕ) (γ : Loop),
      ∃ K : ℕ, N ≤ K ∧ ρ.monodromy K γ = 1) :
    ρ.Trivial := by
  intro N γ
  rcases hhigh N γ with ⟨K, hNK, hK⟩
  exact ρ.monodromy_eq_one_of_le_of_top_eq_one hNK hK

/-- Data expressing the analytic consequence that a basin pullback value is
independent of which escaping iterate is used. This is the root-level part of
the coherent pullback theorem, before differentiability and modulus are added. -/
structure EscapeTimeIndependentPullbackDataFor (c : ℂ) where
  value :
    ∀ z : ℂ, z ∈ basin_of_infinity c → ℂ
  compatible_with_every_escape_time :
    ∀ z (hz : z ∈ basin_of_infinity c) (N : ℕ),
      ‖(MLC.quadratic_map c)^[N] z‖ > ‖c‖ + 2 →
        value z hz ∈
          pullbackRootSet (2 ^ N)
            (MLC.logSeriesBottcherApprox c ((MLC.quadratic_map c)^[N] z))
  agrees_near_infinity :
    ∀ z (hz : z ∈ basin_of_infinity c),
      ‖z‖ > ‖c‖ + 2 →
        value z hz = MLC.logSeriesBottcherApprox c z

/-- PLAN 07 theorem surface: a monodromy representation together with a proof
that its analytic monodromy is trivial should yield escape-time-independent
pullback values. The final analytic work is to construct this data for the basin
loops of `c = 2`. -/
structure MonodromyTrivialPullbackDataFor (c : ℂ) where
  Loop : Type
  representation : PullbackRootMonodromyRepresentation Loop
  trivial_monodromy : representation.Trivial
  escape_time_independent : EscapeTimeIndependentPullbackDataFor c

/-- A concrete loop in the basin of infinity, based at `z₀`. This is the first
PLAN 08 replacement for the earlier abstract `Loop : Type` placeholder. -/
structure BasinLoop (c z₀ : ℂ) where
  path : ℝ → ℂ
  continuousOn_path : ContinuousOn path (Set.Icc (0 : ℝ) 1)
  source : path 0 = z₀
  target : path 1 = z₀
  maps_to_basin : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → path t ∈ basin_of_infinity c

/-- The constant basin loop based at a basin point. -/
def BasinLoop.constant (c z₀ : ℂ) (hz₀ : z₀ ∈ basin_of_infinity c) :
    BasinLoop c z₀ where
  path := fun _ => z₀
  continuousOn_path := continuousOn_const
  source := rfl
  target := rfl
  maps_to_basin := by
    intro _t _ht
    exact hz₀

/-- Local holomorphic branch of a finite pullback root equation near a basin
point. This is a theorem surface for the local analytic branch data required by
PLAN 08. -/
structure LocalPullbackRootBranchData (c : ℂ) (N : ℕ) (z₀ : ℂ) where
  center_mem_basin : z₀ ∈ basin_of_infinity c
  U : Set ℂ
  U_mem_nhds : U ∈ 𝓝 z₀
  branch : ℂ → ℂ
  branch_differentiableOn : DifferentiableOn ℂ branch U
  root_eq :
    ∀ z : ℂ, z ∈ U →
      (branch z) ^ (2 ^ N) =
        MLC.logSeriesBottcherApprox c ((MLC.quadratic_map c)^[N] z)
  center_value_mem_rootSet :
    branch z₀ ∈
      pullbackRootSet (2 ^ N)
        (MLC.logSeriesBottcherApprox c ((MLC.quadratic_map c)^[N] z₀))

/-- Local zero-free chart carrying a logarithm branch and therefore a local
`2^N`-root branch. This is the local building block in PLAN 08's chart-based
monodromy proof template. -/
structure ZeroFreeChartRootBranchData (N : ℕ) where
  chart : Set ℂ
  chart_zero_free : (0 : ℂ) ∉ chart
  logBranch : ℂ → ℂ
  logBranch_exp :
    ∀ w : ℂ, w ∈ chart → Complex.exp (logBranch w) = w
  rootBranch : ℂ → ℂ
  rootBranch_eq :
    ∀ w : ℂ, w ∈ chart →
      rootBranch w = Complex.exp (((2 : ℂ) ^ N)⁻¹ * logBranch w)
  rootBranch_pow :
    ∀ w : ℂ, w ∈ chart → (rootBranch w) ^ (2 ^ N) = w

/-- A zero-free chart whose logarithm branch is analytic on a connected open
domain. This is the exact local package needed by the notebook's identity
principle argument: once two branch systems agree on a neighborhood of one
point in such a chart, they agree on the whole chart. -/
structure ConnectedAnalyticZeroFreeChartRootBranchData (N : ℕ)
    extends ZeroFreeChartRootBranchData N where
  chart_isOpen : IsOpen chart
  chart_isPreconnected : IsPreconnected chart
  logBranch_analyticOn : AnalyticOnNhd ℂ logBranch chart

lemma ConnectedAnalyticZeroFreeChartRootBranchData.logBranch_eqOn_of_eventuallyEq
    {N : ℕ} (left right : ConnectedAnalyticZeroFreeChartRootBranchData N)
    (hsame_chart : left.chart = right.chart)
    {w₀ : ℂ} (hw₀ : w₀ ∈ left.chart)
    (heq : left.logBranch =ᶠ[𝓝 w₀] right.logBranch) :
    EqOn left.logBranch right.logBranch left.chart := by
  have hright_analytic : AnalyticOnNhd ℂ right.logBranch left.chart := by
    simpa [hsame_chart] using right.logBranch_analyticOn
  exact left.logBranch_analyticOn.eqOn_of_preconnected_of_eventuallyEq
    hright_analytic left.chart_isPreconnected hw₀ heq

lemma ConnectedAnalyticZeroFreeChartRootBranchData.rootBranch_eq_of_eventuallyEq
    {N : ℕ} (left right : ConnectedAnalyticZeroFreeChartRootBranchData N)
    (hsame_chart : left.chart = right.chart)
    {w₀ : ℂ} (hw₀ : w₀ ∈ left.chart)
    (heq : left.logBranch =ᶠ[𝓝 w₀] right.logBranch) :
    left.rootBranch w₀ = right.rootBranch w₀ := by
  have hw₀_right : w₀ ∈ right.chart := by
    simpa [hsame_chart] using hw₀
  have hlog : left.logBranch w₀ = right.logBranch w₀ := heq.eq_of_nhds
  rw [left.rootBranch_eq w₀ hw₀, right.rootBranch_eq w₀ hw₀_right, hlog]

/-- Two holomorphic logarithm branches on the same connected zero-free chart are
equal on the whole chart once they agree at one point. This is the base step in
the frontier notebook's rigorous proof: the difference has exponential equal to
`1`, hence takes values in the discrete set `2π i ℤ`, so connectedness forces
it to be constant. -/
lemma ConnectedAnalyticZeroFreeChartRootBranchData.logBranch_eqOn_of_eqAt
    {N : ℕ} (left right : ConnectedAnalyticZeroFreeChartRootBranchData N)
    (hsame_chart : left.chart = right.chart)
    {w₀ : ℂ} (hw₀ : w₀ ∈ left.chart)
    (hlog : left.logBranch w₀ = right.logBranch w₀) :
    EqOn left.logBranch right.logBranch left.chart := by
  let d : ℂ → ℂ := fun w => left.logBranch w - right.logBranch w
  have hright_analytic : AnalyticOnNhd ℂ right.logBranch left.chart := by
    simpa [hsame_chart] using right.logBranch_analyticOn
  have hcont_d : ContinuousOn d left.chart := by
    exact left.logBranch_analyticOn.continuousOn.sub hright_analytic.continuousOn
  have hpre_d : IsPreconnected (d '' left.chart) :=
    left.chart_isPreconnected.image d hcont_d
  have hsubset :
      d '' left.chart ⊆ Set.range (fun n : ℤ => n * (2 * π * Complex.I)) := by
    intro z hz
    rcases hz with ⟨w, hw, rfl⟩
    have hw_right : w ∈ right.chart := by
      simpa [hsame_chart] using hw
    have hw_ne : w ≠ 0 := by
      intro hw_zero
      exact left.chart_zero_free (by simpa [hw_zero] using hw)
    have hexp_one : Complex.exp (d w) = 1 := by
      dsimp [d]
      rw [Complex.exp_sub, left.logBranch_exp w hw, right.logBranch_exp w hw_right, div_self hw_ne]
    rcases Complex.exp_eq_one_iff.mp hexp_one with ⟨n, hn⟩
    exact ⟨n, hn.symm⟩
  have hcount :
      (Set.range (fun n : ℤ => n * (2 * π * Complex.I))).Countable :=
    Set.countable_range _
  have himage_subsingleton : (d '' left.chart).Subsingleton :=
    (Set.Countable.isTotallyDisconnected hcount) _ hsubset hpre_d
  intro w hw
  have hw_image : d w ∈ d '' left.chart := ⟨w, hw, rfl⟩
  have hw₀_image : d w₀ ∈ d '' left.chart := ⟨w₀, hw₀, rfl⟩
  have hd_eq : d w = d w₀ := himage_subsingleton hw_image hw₀_image
  have hd_zero : d w = 0 := by
    calc
      d w = d w₀ := hd_eq
      _ = 0 := by simpa [d, hlog]
  exact sub_eq_zero.mp (by simpa [d] using hd_zero)

/-- Root-branch version of
`ConnectedAnalyticZeroFreeChartRootBranchData.logBranch_eqOn_of_eqAt`. -/
lemma ConnectedAnalyticZeroFreeChartRootBranchData.rootBranch_eq_of_eqAt
    {N : ℕ} (left right : ConnectedAnalyticZeroFreeChartRootBranchData N)
    (hsame_chart : left.chart = right.chart)
    {w₀ : ℂ} (hw₀ : w₀ ∈ left.chart)
    (hlog : left.logBranch w₀ = right.logBranch w₀) :
    left.rootBranch w₀ = right.rootBranch w₀ := by
  have hw₀_right : w₀ ∈ right.chart := by
    simpa [hsame_chart] using hw₀
  rw [left.rootBranch_eq w₀ hw₀, right.rootBranch_eq w₀ hw₀_right]
  exact congrArg (fun z => Complex.exp (((2 : ℂ) ^ N)⁻¹ * z)) hlog

/-- If two logarithm branches agree on a set, then the induced local root branches
agree on that set as well. This is the direct root-level clause in the weakened
frontier notebook theorem. -/
lemma ZeroFreeChartRootBranchData.rootBranch_eqOn_of_logBranch_eqOn
    {N : ℕ} (left right : ZeroFreeChartRootBranchData N)
    {s : Set ℂ}
    (hleft : s ⊆ left.chart)
    (hright : s ⊆ right.chart)
    (hlog : EqOn left.logBranch right.logBranch s) :
    EqOn left.rootBranch right.rootBranch s := by
  intro w hw
  rw [left.rootBranch_eq w (hleft hw), right.rootBranch_eq w (hright hw), hlog hw]

/-- Abstract chain comparison theorem formalizing the frontier notebook's
rigorous proof. Two systems of holomorphic logarithm branches on the same
finite connected chart chain agree on every chart if:
1. they agree at one starting point on the first chart; and
2. each system is internally compatible across consecutive overlaps. -/
lemma logBranch_eqOn_of_chain_initialEq
    {N m : ℕ}
    (act can : ℕ → ConnectedAnalyticZeroFreeChartRootBranchData N)
    (hsame_chart : ∀ j, j ≤ m → (act j).chart = (can j).chart)
    (wStart : ℂ) (hwStart : wStart ∈ (act 0).chart)
    (hstart_eq : (act 0).logBranch wStart = (can 0).logBranch wStart)
    (overlapPoint : ℕ → ℂ)
    (hoverlap_mem_left : ∀ j, j < m → overlapPoint j ∈ (act j).chart)
    (hoverlap_mem_right : ∀ j, j < m → overlapPoint j ∈ (act (j + 1)).chart)
    (hact :
      ∀ j, j < m →
        (act (j + 1)).logBranch =ᶠ[𝓝 (overlapPoint j)] (act j).logBranch)
    (hcan :
      ∀ j, j < m →
        (can (j + 1)).logBranch =ᶠ[𝓝 (overlapPoint j)] (can j).logBranch) :
    ∀ j, j ≤ m → EqOn (act j).logBranch (can j).logBranch (act j).chart := by
  refine Nat.rec ?_ ?_
  · intro _hj
    exact
      ConnectedAnalyticZeroFreeChartRootBranchData.logBranch_eqOn_of_eqAt
        (act 0) (can 0) (hsame_chart 0 (Nat.zero_le m)) hwStart hstart_eq
  · intro j ih hj_succ
    have hj : j ≤ m := Nat.le_of_succ_le hj_succ
    have hj_lt : j < m := lt_of_lt_of_le (Nat.lt_succ_self j) hj_succ
    have hprev_eqOn : EqOn (act j).logBranch (can j).logBranch (act j).chart := ih hj
    have hp_left : overlapPoint j ∈ (act j).chart := hoverlap_mem_left j hj_lt
    have hp_right : overlapPoint j ∈ (act (j + 1)).chart := hoverlap_mem_right j hj_lt
    have hprev_eventuallyEq :
        (act j).logBranch =ᶠ[𝓝 (overlapPoint j)] (can j).logBranch := by
      filter_upwards [(act j).chart_isOpen.mem_nhds hp_left] with z hz
      exact hprev_eqOn hz
    have hnext_eventuallyEq :
        (act (j + 1)).logBranch =ᶠ[𝓝 (overlapPoint j)] (can (j + 1)).logBranch :=
      (hact j hj_lt).trans <| hprev_eventuallyEq.trans <| (hcan j hj_lt).symm
    exact
      ConnectedAnalyticZeroFreeChartRootBranchData.logBranch_eqOn_of_eventuallyEq
        (act (j + 1)) (can (j + 1)) (hsame_chart (j + 1) hj_succ) hp_right
        hnext_eventuallyEq

/-- Endpoint value corollary of `logBranch_eqOn_of_chain_initialEq`. -/
lemma logBranch_eq_of_chain_initialEq
    {N m j : ℕ}
    (act can : ℕ → ConnectedAnalyticZeroFreeChartRootBranchData N)
    (hsame_chart : ∀ k, k ≤ m → (act k).chart = (can k).chart)
    (wStart : ℂ) (hwStart : wStart ∈ (act 0).chart)
    (hstart_eq : (act 0).logBranch wStart = (can 0).logBranch wStart)
    (overlapPoint : ℕ → ℂ)
    (hoverlap_mem_left : ∀ k, k < m → overlapPoint k ∈ (act k).chart)
    (hoverlap_mem_right : ∀ k, k < m → overlapPoint k ∈ (act (k + 1)).chart)
    (hact :
      ∀ k, k < m →
        (act (k + 1)).logBranch =ᶠ[𝓝 (overlapPoint k)] (act k).logBranch)
    (hcan :
      ∀ k, k < m →
        (can (k + 1)).logBranch =ᶠ[𝓝 (overlapPoint k)] (can k).logBranch)
    (hj : j ≤ m) {w : ℂ} (hw : w ∈ (act j).chart) :
    (act j).logBranch w = (can j).logBranch w :=
  logBranch_eqOn_of_chain_initialEq act can hsame_chart
    wStart hwStart hstart_eq overlapPoint hoverlap_mem_left hoverlap_mem_right hact hcan j hj hw

/-- The right half-plane, used in the explicit family of high-level comparison
examples. It is zero-free and carries the principal logarithm. -/
def complexRightHalfPlane : Set ℂ :=
  {w : ℂ | 0 < w.re}

/-- The punctured plane carries the principal logarithm as a pointwise logarithm
branch. This gives a canonical zero-free chart whenever the loop image is known
not to hit `0`. -/
noncomputable def puncturedPlaneZeroFreeChartRootBranchData
    (N : ℕ) : ZeroFreeChartRootBranchData N where
  chart := {w : ℂ | w ≠ 0}
  chart_zero_free := by simp
  logBranch := Complex.log
  logBranch_exp := by
    intro w hw
    exact Complex.exp_log hw
  rootBranch := fun w => Complex.exp (((2 : ℂ) ^ N)⁻¹ * Complex.log w)
  rootBranch_eq := by
    intro w _hw
    rfl
  rootBranch_pow := by
    intro w hw
    rw [← Complex.exp_nat_mul]
    have hpow_ne : ((2 : ℂ) ^ N) ≠ 0 :=
      pow_ne_zero _ (by norm_num : (2 : ℂ) ≠ 0)
    have hcast : ((2 ^ N : ℕ) : ℂ) = (2 : ℂ) ^ N := by
      norm_num
    have hmul :
        ((2 ^ N : ℕ) : ℂ) * (((2 : ℂ) ^ N)⁻¹ * Complex.log w) =
          Complex.log w := by
      rw [hcast]
      field_simp [hpow_ne]
    rw [hmul, Complex.exp_log hw]

/-- The right half-plane carries the principal logarithm as a zero-free chart.
This is the formal global chart used by the generalized special case in the
PLAN 08 blocker notebook. -/
noncomputable def rightHalfPlaneZeroFreeChartRootBranchData
    (N : ℕ) : ZeroFreeChartRootBranchData N where
  chart := complexRightHalfPlane
  chart_zero_free := by
    simp [complexRightHalfPlane]
  logBranch := Complex.log
  logBranch_exp := by
    intro w hw
    exact Complex.exp_log (by
      intro hzero
      simp [complexRightHalfPlane, hzero] at hw)
  rootBranch := fun w => Complex.exp (((2 : ℂ) ^ N)⁻¹ * Complex.log w)
  rootBranch_eq := by
    intro w _hw
    rfl
  rootBranch_pow := by
    intro w hw
    rw [← Complex.exp_nat_mul]
    have hpow_ne : ((2 : ℂ) ^ N) ≠ 0 :=
      pow_ne_zero _ (by norm_num : (2 : ℂ) ≠ 0)
    have hcast : ((2 ^ N : ℕ) : ℂ) = (2 : ℂ) ^ N := by
      norm_num
    have hmul :
        ((2 ^ N : ℕ) : ℂ) * (((2 : ℂ) ^ N)⁻¹ * Complex.log w) =
          Complex.log w := by
      rw [hcast]
      field_simp [hpow_ne]
    have hw_ne : w ≠ 0 := by
      intro hzero
      simp [complexRightHalfPlane, hzero] at hw
    rw [hmul, Complex.exp_log hw_ne]

/-- At `c = 2`, the second iterate has the polynomial form used in the
generalized special-case proof. -/
lemma quadraticMap_two_second_iterate_eq (z : ℂ) :
    (MLC.quadratic_map (2 : ℂ))^[2] z = 6 + 4 * z^2 + z^4 := by
  norm_num [Function.iterate_succ_apply', Function.iterate_zero_apply,
    MLC.quadratic_map]
  ring

/-- Generalized radius-family estimate from the notebook. If `‖z‖ = r`, then
the real part of the second iterate is bounded below by `6 - 4*r^2 - r^4`. -/
lemma quadraticMap_two_second_iterate_re_lower_bound
    (z : ℂ) (r : ℝ) (hr : ‖z‖ = r) :
    6 - 4 * r^2 - r^4 ≤
      ((MLC.quadratic_map (2 : ℂ))^[2] z).re := by
  let u : ℂ := z^2
  have hiter :
      (MLC.quadratic_map (2 : ℂ))^[2] z = 6 + 4 * u + u^2 := by
    dsimp [u]
    norm_num [Function.iterate_succ_apply', Function.iterate_zero_apply,
      MLC.quadratic_map]
    ring
  have hre_u : -‖u‖ ≤ u.re :=
    (abs_le.mp (Complex.abs_re_le_norm u)).1
  have hre_u2 : -‖u^2‖ ≤ (u^2).re :=
    (abs_le.mp (Complex.abs_re_le_norm (u^2))).1
  have hnorm_u : ‖u‖ = r^2 := by
    dsimp [u]
    rw [norm_pow, hr]
  have hnorm_u2 : ‖u^2‖ = r^4 := by
    rw [norm_pow, hnorm_u]
    ring
  have hcalc : 6 - 4 * ‖u‖ - ‖u^2‖ ≤ (6 + 4 * u + u^2).re := by
    have h4 : -4 * ‖u‖ ≤ 4 * u.re := by nlinarith
    have hmain :
        6 + (-4 * ‖u‖) + (-‖u^2‖) ≤
          6 + 4 * u.re + (u^2).re := by
      nlinarith
    simpa [Complex.add_re, Complex.mul_re, Complex.ofReal_re] using hmain
  have hleft : 6 - 4 * r^2 - r^4 = 6 - 4 * ‖u‖ - ‖u^2‖ := by
    rw [hnorm_u, hnorm_u2]
  rw [hiter, hleft]
  exact hcalc

/-- If the generalized radius-family inequality is positive, the second iterate
lies in the right half-plane. For the circle family in the notebook this applies
whenever `r < sqrt (-2 + sqrt 10)`, expressed here through the equivalent
sufficient inequality `0 < 6 - 4*r^2 - r^4`. -/
lemma quadraticMap_two_second_iterate_mem_rightHalfPlane_of_norm
    (z : ℂ) {r : ℝ}
    (hr : ‖z‖ = r) (hpos : 0 < 6 - 4 * r^2 - r^4) :
    (MLC.quadratic_map (2 : ℂ))^[2] z ∈ complexRightHalfPlane := by
  exact lt_of_lt_of_le hpos
    (quadraticMap_two_second_iterate_re_lower_bound z r hr)

/-- If two local root branches solve the same equation on an overlap, then at a
point of the overlap they differ by a `2^N`-th root of unity. This is the
overlap-multiplier step in the PLAN 08 proof template. -/
lemma overlap_root_multiplier_exists
    {N : ℕ} {A w₁ w₂ : ℂ}
    (hN : 2 ^ N ≠ 0)
    (hA : A ≠ 0)
    (hw₁ : w₁ ∈ pullbackRootSet (2 ^ N) A)
    (hw₂ : w₂ ∈ pullbackRootSet (2 ^ N) A) :
    ∃ ζ : ℂ, ζ ∈ rootsOfUnitySet (2 ^ N) ∧ w₂ = ζ * w₁ :=
  pullbackRootSet_torsor_transitive hN hw₁ hw₂ hA

/-- Products of finite lists of `n`-th roots of unity are again `n`-th roots of
unity. This is the algebraic engine behind multiplying overlap factors around a
chart chain. -/
lemma rootsOfUnitySet_list_prod
    {n : ℕ} (L : List ℂ)
    (hL : ∀ ζ : ℂ, ζ ∈ L → ζ ∈ rootsOfUnitySet n) :
    L.prod ∈ rootsOfUnitySet n := by
  induction L with
  | nil =>
      simpa using one_mem_rootsOfUnitySet n
  | cons ζ L ih =>
      have hζ : ζ ∈ rootsOfUnitySet n := hL ζ (by simp)
      have hL' : ∀ η : ℂ, η ∈ L → η ∈ rootsOfUnitySet n := by
        intro η hη
        exact hL η (by simp [hη])
      have ih' : L.prod ∈ rootsOfUnitySet n := ih hL'
      dsimp [rootsOfUnitySet] at hζ ih' ⊢
      simp [mul_pow, hζ, ih']

/-- Abstract overlap multiplier data for adjacent zero-free charts in a
continued root construction. A product of these multipliers around a closed loop
is the monodromy element. -/
structure OverlapRootMultiplierData (N : ℕ) where
  index : Type
  multiplier : index → ℂ
  multiplier_mem :
    ∀ i, multiplier i ∈ rootsOfUnitySet (2 ^ N)
  monodromyProduct : ℂ
  product_mem :
    monodromyProduct ∈ rootsOfUnitySet (2 ^ N)

/-- The level-`N` value whose `2^N`-th roots are continued along a basin loop. -/
noncomputable def basinLoopRootEquationValue
    (c : ℂ) (N : ℕ) {z₀ : ℂ} (γ : BasinLoop c z₀) (t : ℝ) : ℂ :=
  MLC.logSeriesBottcherApprox c ((MLC.quadratic_map c)^[N] (γ.path t))

/-- A loop level is escaping if the whole level-`N` loop image lies in the
canonical outside-open region where the logarithmic-series coordinate is already
known to be exterior-valued. -/
def BasinLoopLevelEscapes (c : ℂ) (N : ℕ) {z₀ : ℂ}
    (γ : BasinLoop c z₀) : Prop :=
  ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
    ‖(MLC.quadratic_map c)^[N] (γ.path t)‖ > ‖c‖ + 2

/-- Once a loop level is in the outside-open region, every later level is also
outside-open by forward invariance. -/
lemma BasinLoopLevelEscapes.mono
    {c : ℂ} {K L : ℕ} {z₀ : ℂ} {γ : BasinLoop c z₀}
    (hKL : K ≤ L) (hesc : BasinLoopLevelEscapes c K γ) :
    BasinLoopLevelEscapes c L γ := by
  rcases Nat.exists_eq_add_of_le hKL with ⟨d, rfl⟩
  intro t ht
  have hK := hesc t ht
  have hd := MLC.quadratic_map_iter_maps_outside_open c hK d
  rw [Nat.add_comm K d]
  simpa [Function.iterate_add, Function.comp_apply] using hd

/-- At an escaping level, the corresponding root-equation value is nonzero. -/
lemma basinLoopRootEquationValue_ne_zero_of_outside_open
    {c : ℂ} {N : ℕ} {z₀ : ℂ} {γ : BasinLoop c z₀} {t : ℝ}
    (houtside :
      ‖(MLC.quadratic_map c)^[N] (γ.path t)‖ > ‖c‖ + 2) :
    basinLoopRootEquationValue c N γ t ≠ 0 := by
  have hnorm :
      1 <
        ‖MLC.logSeriesBottcherApprox c
          ((MLC.quadratic_map c)^[N] (γ.path t))‖ :=
    MLC.one_lt_norm_logSeriesBottcherApprox_of_outside_open c houtside
  intro hzero
  have hzero' :
      MLC.logSeriesBottcherApprox c ((MLC.quadratic_map c)^[N] (γ.path t)) = 0 := by
    simpa [basinLoopRootEquationValue] using hzero
  have hnorm_zero :
      ‖MLC.logSeriesBottcherApprox c ((MLC.quadratic_map c)^[N] (γ.path t))‖ = 0 := by
    simp [hzero']
  have : ¬ (1 : ℝ) < 0 := by norm_num
  exact this (by simpa [hnorm_zero] using hnorm)

lemma basinLoopRootEquationValue_ne_zero_of_level_escapes
    {c : ℂ} {N : ℕ} {z₀ : ℂ} {γ : BasinLoop c z₀}
    (hesc : BasinLoopLevelEscapes c N γ) :
    ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      basinLoopRootEquationValue c N γ t ≠ 0 := by
  intro t ht
  exact basinLoopRootEquationValue_ne_zero_of_outside_open (hesc t ht)

/-- One chart cell in a finite chart-chain cover of a basin loop. It records an
interval of loop time and a zero-free chart containing the corresponding
level-`N` Böttcher values. -/
structure BasinLoopChartCell
    (c : ℂ) (N : ℕ) (z₀ : ℂ) (γ : BasinLoop c z₀) where
  tStart : ℝ
  tEnd : ℝ
  tStart_mem : tStart ∈ Set.Icc (0 : ℝ) 1
  tEnd_mem : tEnd ∈ Set.Icc (0 : ℝ) 1
  ordered : tStart ≤ tEnd
  chart : ZeroFreeChartRootBranchData N
  image_mem_chart :
    ∀ t : ℝ, t ∈ Set.Icc tStart tEnd →
      basinLoopRootEquationValue c N γ t ∈ chart.chart

/-- An adjacent-chart overlap step. The multiplier records how the right local
root branch compares with the left one on the overlap value. -/
structure BasinLoopChartOverlapStep
    (c : ℂ) (N : ℕ) (z₀ : ℂ) (γ : BasinLoop c z₀) where
  left : BasinLoopChartCell c N z₀ γ
  right : BasinLoopChartCell c N z₀ γ
  overlapTime : ℝ
  overlapTime_mem_left : overlapTime ∈ Set.Icc left.tStart left.tEnd
  overlapTime_mem_right : overlapTime ∈ Set.Icc right.tStart right.tEnd
  value_mem_left_chart :
    basinLoopRootEquationValue c N γ overlapTime ∈ left.chart.chart
  value_mem_right_chart :
    basinLoopRootEquationValue c N γ overlapTime ∈ right.chart.chart
  multiplier : ℂ
  multiplier_mem : multiplier ∈ rootsOfUnitySet (2 ^ N)
  rootBranch_overlap :
    right.chart.rootBranch (basinLoopRootEquationValue c N γ overlapTime) =
      multiplier * left.chart.rootBranch (basinLoopRootEquationValue c N γ overlapTime)

lemma BasinLoopChartOverlapStep.multiplier_eq_one_of_logBranch_eq
    {c : ℂ} {N : ℕ} {z₀ : ℂ} {γ : BasinLoop c z₀}
    (step : BasinLoopChartOverlapStep c N z₀ γ)
    (hlog :
      step.left.chart.logBranch
          (basinLoopRootEquationValue c N γ step.overlapTime) =
        step.right.chart.logBranch
          (basinLoopRootEquationValue c N γ step.overlapTime)) :
    step.multiplier = 1 := by
  let A : ℂ := basinLoopRootEquationValue c N γ step.overlapTime
  have hleft_right :
      step.left.chart.rootBranch A = step.right.chart.rootBranch A := by
    rw [step.left.chart.rootBranch_eq A step.value_mem_left_chart,
      step.right.chart.rootBranch_eq A step.value_mem_right_chart, hlog]
  have hA_ne : A ≠ 0 := by
    intro hA0
    exact step.left.chart.chart_zero_free (by simpa [A, hA0] using step.value_mem_left_chart)
  have hroot_ne : step.left.chart.rootBranch A ≠ 0 := by
    intro hroot0
    have hpow_ne : 2 ^ N ≠ 0 := pow_ne_zero N (by norm_num : (2 : ℕ) ≠ 0)
    have hA0 : A = 0 := by
      simpa [hroot0, hpow_ne] using
        (step.left.chart.rootBranch_pow A step.value_mem_left_chart).symm
    exact hA_ne hA0
  have hmul :
      step.multiplier * step.left.chart.rootBranch A =
        1 * step.left.chart.rootBranch A := by
    calc
      step.multiplier * step.left.chart.rootBranch A =
          step.right.chart.rootBranch A := by
            simpa [A] using step.rootBranch_overlap.symm
      _ = step.left.chart.rootBranch A := hleft_right.symm
      _ = 1 * step.left.chart.rootBranch A := by simp
  exact mul_right_cancel₀ hroot_ne hmul

lemma BasinLoopChartOverlapStep.multiplier_eq_one_of_eventuallyEq
    {c : ℂ} {N : ℕ} {z₀ : ℂ} {γ : BasinLoop c z₀}
    (step : BasinLoopChartOverlapStep c N z₀ γ)
    (heq :
      step.left.chart.logBranch =ᶠ[𝓝 (basinLoopRootEquationValue c N γ step.overlapTime)]
        step.right.chart.logBranch) :
    step.multiplier = 1 :=
  step.multiplier_eq_one_of_logBranch_eq heq.eq_of_nhds

/-- Set-level version of `BasinLoopChartOverlapStep.multiplier_eq_one_of_logBranch_eq`:
if the neighboring logarithm branches agree on a neighborhood set containing the
overlap value, then the overlap multiplier is trivial. -/
lemma BasinLoopChartOverlapStep.multiplier_eq_one_of_eqOn
    {c : ℂ} {N : ℕ} {z₀ : ℂ} {γ : BasinLoop c z₀}
    (step : BasinLoopChartOverlapStep c N z₀ γ)
    {s : Set ℂ}
    (hoverlap : basinLoopRootEquationValue c N γ step.overlapTime ∈ s)
    (hlog : EqOn step.left.chart.logBranch step.right.chart.logBranch s) :
    step.multiplier = 1 :=
  step.multiplier_eq_one_of_logBranch_eq (hlog hoverlap)

/-- A finite chart chain along a concrete basin loop. The cells cover the loop in
time, and the overlap steps carry the root-of-unity transition multipliers. -/
structure BasinLoopChartChain
    (c : ℂ) (N : ℕ) (z₀ : ℂ) (γ : BasinLoop c z₀) where
  cells : List (BasinLoopChartCell c N z₀ γ)
  covers_loop :
    ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      ∃ cell ∈ cells, t ∈ Set.Icc cell.tStart cell.tEnd
  overlaps : List (BasinLoopChartOverlapStep c N z₀ γ)

/-- Local logarithm branches in a chart chain are restrictions of one global
zero-free logarithm branch along all overlap values. This is the formal
special-case comparison input from the notebook: if every local branch is
obtained by restricting the same logarithm, no overlap can acquire a nontrivial
root-of-unity multiplier. -/
structure ChartChainLocalLogsRestrictGlobal
    {c : ℂ} {N : ℕ} {z₀ : ℂ} {γ : BasinLoop c z₀}
    (chain : BasinLoopChartChain c N z₀ γ)
    (globalChart : ZeroFreeChartRootBranchData N) where
  overlap_value_mem_global :
    ∀ step ∈ chain.overlaps,
      basinLoopRootEquationValue c N γ step.overlapTime ∈ globalChart.chart
  left_logBranch_eq_global :
    ∀ step (_hstep : step ∈ chain.overlaps),
      step.left.chart.logBranch
          (basinLoopRootEquationValue c N γ step.overlapTime) =
        globalChart.logBranch
          (basinLoopRootEquationValue c N γ step.overlapTime)
  right_logBranch_eq_global :
    ∀ step (_hstep : step ∈ chain.overlaps),
      step.right.chart.logBranch
          (basinLoopRootEquationValue c N γ step.overlapTime) =
        globalChart.logBranch
          (basinLoopRootEquationValue c N γ step.overlapTime)

/-- If the level-`N` loop image avoids `0`, the whole loop is covered by the
single punctured-plane chart and has no overlap multipliers. -/
noncomputable def BasinLoopChartChain.of_nonzero_values
    {c : ℂ} {N : ℕ} {z₀ : ℂ} (γ : BasinLoop c z₀)
    (hnonzero :
      ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
        basinLoopRootEquationValue c N γ t ≠ 0) :
    BasinLoopChartChain c N z₀ γ :=
  let cell : BasinLoopChartCell c N z₀ γ :=
    { tStart := 0
      tEnd := 1
      tStart_mem := by simp
      tEnd_mem := by simp
      ordered := by norm_num
      chart := puncturedPlaneZeroFreeChartRootBranchData N
      image_mem_chart := by
        intro t ht
        exact hnonzero t ht }
  { cells := [cell]
    covers_loop := by
      intro t ht
      exact ⟨cell, by simp, ht⟩
    overlaps := [] }

/-- Escaping levels have a canonical one-chart chain: the near-infinity value is
exterior-valued, hence nonzero, so the punctured-plane chart applies. -/
noncomputable def BasinLoopChartChain.of_escaping_level
    {c : ℂ} {N : ℕ} {z₀ : ℂ} (γ : BasinLoop c z₀)
    (hesc : BasinLoopLevelEscapes c N γ) :
    BasinLoopChartChain c N z₀ γ :=
  BasinLoopChartChain.of_nonzero_values γ
    (basinLoopRootEquationValue_ne_zero_of_level_escapes hesc)

/-- The ordered list of overlap multipliers carried by a chart chain. -/
def BasinLoopChartChain.overlapMultipliers
    {c : ℂ} {N : ℕ} {z₀ : ℂ} {γ : BasinLoop c z₀}
    (chain : BasinLoopChartChain c N z₀ γ) : List ℂ :=
  chain.overlaps.map (fun step => step.multiplier)

lemma BasinLoopChartChain.overlapMultipliers_mem
    {c : ℂ} {N : ℕ} {z₀ : ℂ} {γ : BasinLoop c z₀}
    (chain : BasinLoopChartChain c N z₀ γ) :
    ∀ ζ : ℂ, ζ ∈ chain.overlapMultipliers → ζ ∈ rootsOfUnitySet (2 ^ N) := by
  intro ζ hζ
  rcases List.mem_map.1 hζ with ⟨step, hstep, rfl⟩
  exact step.multiplier_mem

/-- The product of all adjacent-chart overlap multipliers. This is the concrete
finite-chain monodromy element at level `N`. -/
def BasinLoopChartChain.monodromyProduct
    {c : ℂ} {N : ℕ} {z₀ : ℂ} {γ : BasinLoop c z₀}
    (chain : BasinLoopChartChain c N z₀ γ) : ℂ :=
  chain.overlapMultipliers.prod

lemma BasinLoopChartChain.monodromyProduct_mem
    {c : ℂ} {N : ℕ} {z₀ : ℂ} {γ : BasinLoop c z₀}
    (chain : BasinLoopChartChain c N z₀ γ) :
    chain.monodromyProduct ∈ rootsOfUnitySet (2 ^ N) :=
  rootsOfUnitySet_list_prod chain.overlapMultipliers chain.overlapMultipliers_mem

lemma overlapMultiplier_list_prod_eq_one
    {c : ℂ} {N : ℕ} {z₀ : ℂ} {γ : BasinLoop c z₀}
    (L : List (BasinLoopChartOverlapStep c N z₀ γ))
    (hL : ∀ step ∈ L, step.multiplier = 1) :
    (L.map (fun step => step.multiplier)).prod = 1 := by
  induction L with
  | nil =>
      simp
  | cons step rest ih =>
      have hstep : step.multiplier = 1 := hL step (by simp)
      have hrest : ∀ step ∈ rest, step.multiplier = 1 := by
        intro step' hstep'
        exact hL step' (by simp [hstep'])
      simp [hstep, ih hrest]

lemma ChartChainLocalLogsRestrictGlobal.overlap_multiplier_eq_one
    {c : ℂ} {N : ℕ} {z₀ : ℂ} {γ : BasinLoop c z₀}
    {chain : BasinLoopChartChain c N z₀ γ}
    {globalChart : ZeroFreeChartRootBranchData N}
    (hrestrict : ChartChainLocalLogsRestrictGlobal chain globalChart)
    (step : BasinLoopChartOverlapStep c N z₀ γ)
    (hstep : step ∈ chain.overlaps) :
    step.multiplier = 1 := by
  let A : ℂ := basinLoopRootEquationValue c N γ step.overlapTime
  have hA_global : A ∈ globalChart.chart :=
    hrestrict.overlap_value_mem_global step hstep
  have hleft :
      step.left.chart.rootBranch A = globalChart.rootBranch A := by
    calc
      step.left.chart.rootBranch A =
          Complex.exp (((2 : ℂ) ^ N)⁻¹ * step.left.chart.logBranch A) := by
            rw [step.left.chart.rootBranch_eq A step.value_mem_left_chart]
      _ = Complex.exp (((2 : ℂ) ^ N)⁻¹ * globalChart.logBranch A) := by
            rw [hrestrict.left_logBranch_eq_global step hstep]
      _ = globalChart.rootBranch A := by
            rw [globalChart.rootBranch_eq A hA_global]
  have hright :
      step.right.chart.rootBranch A = globalChart.rootBranch A := by
    calc
      step.right.chart.rootBranch A =
          Complex.exp (((2 : ℂ) ^ N)⁻¹ * step.right.chart.logBranch A) := by
            rw [step.right.chart.rootBranch_eq A step.value_mem_right_chart]
      _ = Complex.exp (((2 : ℂ) ^ N)⁻¹ * globalChart.logBranch A) := by
            rw [hrestrict.right_logBranch_eq_global step hstep]
      _ = globalChart.rootBranch A := by
            rw [globalChart.rootBranch_eq A hA_global]
  have hA_ne : A ≠ 0 := by
    intro hA0
    exact globalChart.chart_zero_free (by simpa [hA0] using hA_global)
  have hroot_ne : globalChart.rootBranch A ≠ 0 := by
    intro hroot0
    have hpow_ne : 2 ^ N ≠ 0 := pow_ne_zero N (by norm_num : (2 : ℕ) ≠ 0)
    have hA0 : A = 0 := by
      simpa [hroot0, hpow_ne] using (globalChart.rootBranch_pow A hA_global).symm
    exact hA_ne hA0
  have hsame :
      globalChart.rootBranch A = step.multiplier * globalChart.rootBranch A := by
    calc
      globalChart.rootBranch A = step.right.chart.rootBranch A := hright.symm
      _ = step.multiplier * step.left.chart.rootBranch A := step.rootBranch_overlap
      _ = step.multiplier * globalChart.rootBranch A := by rw [hleft]
  have hmul :
      step.multiplier * globalChart.rootBranch A =
        1 * globalChart.rootBranch A := by
    rw [one_mul]
    exact hsame.symm
  exact mul_right_cancel₀ hroot_ne hmul

lemma ChartChainLocalLogsRestrictGlobal.monodromyProduct_eq_one
    {c : ℂ} {N : ℕ} {z₀ : ℂ} {γ : BasinLoop c z₀}
    {chain : BasinLoopChartChain c N z₀ γ}
    {globalChart : ZeroFreeChartRootBranchData N}
    (hrestrict : ChartChainLocalLogsRestrictGlobal chain globalChart) :
    chain.monodromyProduct = 1 := by
  dsimp [BasinLoopChartChain.monodromyProduct,
    BasinLoopChartChain.overlapMultipliers]
  exact overlapMultiplier_list_prod_eq_one chain.overlaps
    (fun step hstep => hrestrict.overlap_multiplier_eq_one step hstep)

/-- Abstract overlap input for the generalized analytic theorem from the
notebook: at every adjacent overlap value, the left and right local logarithm
branches agree on a whole neighborhood of that value. Combined with the
identity-principle chart lemma above, this is the local hypothesis that forces
all overlap multipliers to be trivial. -/
structure ChartChainLocalLogsEventuallyEqAtOverlaps
    {c : ℂ} {N : ℕ} {z₀ : ℂ} {γ : BasinLoop c z₀}
    (chain : BasinLoopChartChain c N z₀ γ) where
  overlap_eventuallyEq :
    ∀ step (_hstep : step ∈ chain.overlaps),
      step.left.chart.logBranch =ᶠ[𝓝 (basinLoopRootEquationValue c N γ step.overlapTime)]
        step.right.chart.logBranch

/-- The weakened frontier notebook theorem packages open-set overlap equalities of
local logarithm branches into the eventual-equality structure used by the
formalized monodromy theorem. -/
def ChartChainLocalLogsEventuallyEqAtOverlaps.of_open_eqOn
    {c : ℂ} {N : ℕ} {z₀ : ℂ} {γ : BasinLoop c z₀}
    {chain : BasinLoopChartChain c N z₀ γ}
    (hoverlap_eqOn :
      ∀ step ∈ chain.overlaps,
        ∃ V : Set ℂ, IsOpen V ∧
          basinLoopRootEquationValue c N γ step.overlapTime ∈ V ∧
          EqOn step.left.chart.logBranch step.right.chart.logBranch V) :
    ChartChainLocalLogsEventuallyEqAtOverlaps chain where
  overlap_eventuallyEq := by
    intro step hstep
    rcases hoverlap_eqOn step hstep with ⟨V, hVopen, hVmem, hVeq⟩
    filter_upwards [hVopen.mem_nhds hVmem] with w hw
    exact hVeq hw

lemma ChartChainLocalLogsEventuallyEqAtOverlaps.monodromyProduct_eq_one
    {c : ℂ} {N : ℕ} {z₀ : ℂ} {γ : BasinLoop c z₀}
    {chain : BasinLoopChartChain c N z₀ γ}
    (heq : ChartChainLocalLogsEventuallyEqAtOverlaps chain) :
    chain.monodromyProduct = 1 := by
  dsimp [BasinLoopChartChain.monodromyProduct,
    BasinLoopChartChain.overlapMultipliers]
  exact overlapMultiplier_list_prod_eq_one chain.overlaps
    (fun step hstep =>
      step.multiplier_eq_one_of_eventuallyEq (heq.overlap_eventuallyEq step hstep))

/-- Direct local-chart-chain version of the weakened frontier notebook proof:
open overlap neighborhoods on which adjacent logarithm branches agree force every
overlap multiplier, and hence the whole monodromy product, to be `1`. -/
lemma BasinLoopChartChain.monodromyProduct_eq_one_of_open_eqOn
    {c : ℂ} {N : ℕ} {z₀ : ℂ} {γ : BasinLoop c z₀}
    {chain : BasinLoopChartChain c N z₀ γ}
    (hoverlap_eqOn :
      ∀ step ∈ chain.overlaps,
        ∃ V : Set ℂ, IsOpen V ∧
          basinLoopRootEquationValue c N γ step.overlapTime ∈ V ∧
          EqOn step.left.chart.logBranch step.right.chart.logBranch V) :
    chain.monodromyProduct = 1 :=
  (ChartChainLocalLogsEventuallyEqAtOverlaps.of_open_eqOn hoverlap_eqOn).monodromyProduct_eq_one

lemma BasinLoopChartChain.monodromyProduct_of_nonzero_values
    {c : ℂ} {N : ℕ} {z₀ : ℂ} (γ : BasinLoop c z₀)
    (hnonzero :
      ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
        basinLoopRootEquationValue c N γ t ≠ 0) :
    (BasinLoopChartChain.of_nonzero_values γ hnonzero).monodromyProduct = 1 := by
  simp [BasinLoopChartChain.of_nonzero_values, BasinLoopChartChain.monodromyProduct,
    BasinLoopChartChain.overlapMultipliers]

lemma BasinLoopChartChain.monodromyProduct_of_escaping_level
    {c : ℂ} {N : ℕ} {z₀ : ℂ} (γ : BasinLoop c z₀)
    (hesc : BasinLoopLevelEscapes c N γ) :
    (BasinLoopChartChain.of_escaping_level γ hesc).monodromyProduct = 1 := by
  simp [BasinLoopChartChain.of_escaping_level,
    BasinLoopChartChain.monodromyProduct_of_nonzero_values]

/-- A concrete finite chart chain supplies the earlier abstract overlap
multiplier surface, with the monodromy product computed as the list product of
its actual adjacent overlap multipliers. -/
noncomputable def BasinLoopChartChain.toOverlapRootMultiplierData
    {c : ℂ} {N : ℕ} {z₀ : ℂ} {γ : BasinLoop c z₀}
    (chain : BasinLoopChartChain c N z₀ γ) :
    OverlapRootMultiplierData N where
  index := {ζ : ℂ // ζ ∈ chain.overlapMultipliers}
  multiplier := fun ζ => ζ.1
  multiplier_mem := fun ζ => chain.overlapMultipliers_mem ζ.1 ζ.2
  monodromyProduct := chain.monodromyProduct
  product_mem := chain.monodromyProduct_mem

/-- Analytic continuation of a local pullback root branch around a basin loop.
The output branch may differ from the input branch by a root-of-unity multiplier;
that multiplier is the monodromy element. -/
structure AnalyticContinuationAlongBasinLoop
    (c : ℂ) (N : ℕ) (z₀ : ℂ)
    (γ : BasinLoop c z₀)
    (start_branch : LocalPullbackRootBranchData c N z₀) where
  end_branch : LocalPullbackRootBranchData c N z₀
  multiplier : ℂ
  multiplier_mem : multiplier ∈ rootsOfUnitySet (2 ^ N)
  continued_center_value :
    end_branch.branch z₀ = multiplier * start_branch.branch z₀

/-- Local trivial monodromy: if a continuation stays in one chart/one chosen
branch, the endpoint branch is the starting branch and the monodromy multiplier
is `1`. This is the local zero-free-chart case in PLAN 08; global monodromy is
obtained only after chaining such local continuations and controlling the
overlap multipliers. -/
noncomputable def AnalyticContinuationAlongBasinLoop.trivial
    {c : ℂ} {N : ℕ} {z₀ : ℂ}
    (γ : BasinLoop c z₀)
    (start_branch : LocalPullbackRootBranchData c N z₀) :
    AnalyticContinuationAlongBasinLoop c N z₀ γ start_branch where
  end_branch := start_branch
  multiplier := 1
  multiplier_mem := one_mem_rootsOfUnitySet (2 ^ N)
  continued_center_value := by simp

/-- The monodromy multiplier of the same-chart continuation is trivial. -/
lemma AnalyticContinuationAlongBasinLoop.trivial_multiplier
    {c : ℂ} {N : ℕ} {z₀ : ℂ}
    (γ : BasinLoop c z₀)
    (start_branch : LocalPullbackRootBranchData c N z₀) :
    (AnalyticContinuationAlongBasinLoop.trivial γ start_branch).multiplier = 1 := rfl

/-- A zero-free chart supplies the same local trivial continuation: inside one
fixed chart with one fixed logarithm branch, no root-of-unity factor is acquired.
The chart argument is included to make the PLAN 08 local step explicit; the
remaining global work is to pass between many such charts and multiply overlap
factors. -/
noncomputable def ZeroFreeChartRootBranchData.trivialContinuation
    {c : ℂ} {N : ℕ} {z₀ : ℂ}
    (_chart : ZeroFreeChartRootBranchData N)
    (γ : BasinLoop c z₀)
    (start_branch : LocalPullbackRootBranchData c N z₀) :
    AnalyticContinuationAlongBasinLoop c N z₀ γ start_branch :=
  AnalyticContinuationAlongBasinLoop.trivial γ start_branch

lemma ZeroFreeChartRootBranchData.trivialContinuation_multiplier
    {c : ℂ} {N : ℕ} {z₀ : ℂ}
    (chart : ZeroFreeChartRootBranchData N)
    (γ : BasinLoop c z₀)
    (start_branch : LocalPullbackRootBranchData c N z₀) :
    (chart.trivialContinuation γ start_branch).multiplier = 1 := rfl

/-- Continuation data obtained by following an actual finite chart chain. The
endpoint branch is required to differ from the start branch by the product of the
recorded overlap multipliers. -/
structure ChartChainContinuationData
    (c : ℂ) (N : ℕ) (z₀ : ℂ)
    (γ : BasinLoop c z₀)
    (start_branch : LocalPullbackRootBranchData c N z₀) where
  chain : BasinLoopChartChain c N z₀ γ
  end_branch : LocalPullbackRootBranchData c N z₀
  continued_center_value :
    end_branch.branch z₀ = chain.monodromyProduct * start_branch.branch z₀

/-- A chart-chain continuation is an analytic continuation whose multiplier is
the finite product of adjacent overlap multipliers. -/
noncomputable def ChartChainContinuationData.toAnalyticContinuation
    {c : ℂ} {N : ℕ} {z₀ : ℂ} {γ : BasinLoop c z₀}
    {start_branch : LocalPullbackRootBranchData c N z₀}
    (h : ChartChainContinuationData c N z₀ γ start_branch) :
    AnalyticContinuationAlongBasinLoop c N z₀ γ start_branch where
  end_branch := h.end_branch
  multiplier := h.chain.monodromyProduct
  multiplier_mem := h.chain.monodromyProduct_mem
  continued_center_value := h.continued_center_value

lemma ChartChainContinuationData.toAnalyticContinuation_multiplier
    {c : ℂ} {N : ℕ} {z₀ : ℂ} {γ : BasinLoop c z₀}
    {start_branch : LocalPullbackRootBranchData c N z₀}
    (h : ChartChainContinuationData c N z₀ γ start_branch) :
    h.toAnalyticContinuation.multiplier = h.chain.monodromyProduct := rfl

/-- Actual monodromy representation for basin loops based at `z₀`. This is the
PLAN 08 target replacing the abstract `PullbackRootMonodromyRepresentation Loop`
with the concrete loop type `BasinLoop c z₀`. -/
structure BasinLoopPullbackRootMonodromyData (c z₀ : ℂ) where
  base_mem_basin : z₀ ∈ basin_of_infinity c
  representation : PullbackRootMonodromyRepresentation (BasinLoop c z₀)
  realized_by_continuation :
    ∀ (N : ℕ) (γ : BasinLoop c z₀)
      (start_branch : LocalPullbackRootBranchData c N z₀),
      ∃ cont : AnalyticContinuationAlongBasinLoop c N z₀ γ start_branch,
        cont.multiplier = representation.monodromy N γ

/-- If actual basin-loop monodromy data is available and its monodromy is
trivial, then it supplies the abstract monodromy representation surface from
PLAN 07. The remaining hard input is still the escape-time-independent pullback
data. -/
noncomputable def BasinLoopPullbackRootMonodromyData.toMonodromyTrivialPullbackDataFor
    {c z₀ : ℂ}
    (h : BasinLoopPullbackRootMonodromyData c z₀)
    (htriv : h.representation.Trivial)
    (hind : EscapeTimeIndependentPullbackDataFor c) :
    MonodromyTrivialPullbackDataFor c where
  Loop := BasinLoop c z₀
  representation := h.representation
  trivial_monodromy := htriv
  escape_time_independent := hind

/-- Chart-chain monodromy data for every concrete basin loop based at `z₀`.
This is the global PLAN 08 layer immediately after the same-chart local step:
each loop receives actual finite chart-chain data, the representation is the
product of its overlap multipliers, and compatibility across levels is recorded
as the expected squaring relation. -/
structure BasinLoopChartChainMonodromyData (c z₀ : ℂ) where
  base_mem_basin : z₀ ∈ basin_of_infinity c
  chain :
    ∀ (N : ℕ) (γ : BasinLoop c z₀), BasinLoopChartChain c N z₀ γ
  monodromy_compat :
    ∀ (N : ℕ) (γ : BasinLoop c z₀),
      ((chain (N + 1) γ).monodromyProduct) ^ 2 =
        (chain N γ).monodromyProduct
  continued_branch :
    ∀ (N : ℕ) (_γ : BasinLoop c z₀)
      (_start_branch : LocalPullbackRootBranchData c N z₀),
      LocalPullbackRootBranchData c N z₀
  continued_center_value :
    ∀ (N : ℕ) (γ : BasinLoop c z₀)
      (start_branch : LocalPullbackRootBranchData c N z₀),
      (continued_branch N γ start_branch).branch z₀ =
        (chain N γ).monodromyProduct * start_branch.branch z₀

/-- The monodromy representation encoded by chart-chain overlap products. -/
noncomputable def BasinLoopChartChainMonodromyData.representation
    {c z₀ : ℂ} (h : BasinLoopChartChainMonodromyData c z₀) :
    PullbackRootMonodromyRepresentation (BasinLoop c z₀) where
  monodromy := fun N γ => (h.chain N γ).monodromyProduct
  monodromy_mem := fun N γ => (h.chain N γ).monodromyProduct_mem
  monodromy_compat := h.monodromy_compat

/-- Chart-chain monodromy data realizes the concrete basin-loop monodromy data
required by PLAN 08. -/
noncomputable def BasinLoopChartChainMonodromyData.toBasinLoopPullbackRootMonodromyData
    {c z₀ : ℂ} (h : BasinLoopChartChainMonodromyData c z₀) :
    BasinLoopPullbackRootMonodromyData c z₀ where
  base_mem_basin := h.base_mem_basin
  representation := h.representation
  realized_by_continuation := by
    intro N γ start_branch
    refine ⟨?_, ?_⟩
    · exact
      { end_branch := h.continued_branch N γ start_branch
        multiplier := (h.chain N γ).monodromyProduct
        multiplier_mem := (h.chain N γ).monodromyProduct_mem
        continued_center_value := h.continued_center_value N γ start_branch }
    · simp [BasinLoopChartChainMonodromyData.representation]

/-- Triviality criterion for the chart-chain representation: if every finite
overlap product is `1`, the induced basin-loop monodromy representation is
trivial. -/
lemma BasinLoopChartChainMonodromyData.representation_trivial_of_products
    {c z₀ : ℂ} (h : BasinLoopChartChainMonodromyData c z₀)
    (hprod : ∀ (N : ℕ) (γ : BasinLoop c z₀),
      (h.chain N γ).monodromyProduct = 1) :
    h.representation.Trivial := by
  intro N γ
  exact hprod N γ

/-- Chart-chain version of descent: if for every requested level `N` and loop
there is a higher level `K ≥ N` whose overlap product is already trivial, then
the induced compatible monodromy representation is trivial at every level. -/
lemma BasinLoopChartChainMonodromyData.representation_trivial_of_arbitrarily_high_products
    {c z₀ : ℂ} (h : BasinLoopChartChainMonodromyData c z₀)
    (hprod : ∀ (N : ℕ) (γ : BasinLoop c z₀),
      ∃ K : ℕ, N ≤ K ∧ (h.chain K γ).monodromyProduct = 1) :
    h.representation.Trivial := by
  exact h.representation.trivial_of_arbitrarily_high_trivial hprod

/-- Conditional construction of the PLAN 08 chart-chain monodromy data. If every
level-`N` loop image avoids `0`, the punctured-plane chart gives a one-chart
chain for every loop; all overlap products are empty products, hence compatible
and trivial. The missing theorem for `c = 2` is precisely the supplied
nonvanishing hypothesis. -/
noncomputable def BasinLoopChartChainMonodromyData.of_nonzero_values_two
    {z₀ : ℂ}
    (hz₀ : z₀ ∈ basin_of_infinity (2 : ℂ))
    (hnonzero :
      ∀ (N : ℕ) (γ : BasinLoop (2 : ℂ) z₀) (t : ℝ),
        t ∈ Set.Icc (0 : ℝ) 1 →
          basinLoopRootEquationValue (2 : ℂ) N γ t ≠ 0) :
    BasinLoopChartChainMonodromyData (2 : ℂ) z₀ where
  base_mem_basin := hz₀
  chain := fun N γ =>
    BasinLoopChartChain.of_nonzero_values γ (hnonzero N γ)
  monodromy_compat := by
    intro N γ
    simp [BasinLoopChartChain.monodromyProduct_of_nonzero_values]
  continued_branch := fun _N _γ start_branch => start_branch
  continued_center_value := by
    intro N γ start_branch
    simp [BasinLoopChartChain.monodromyProduct_of_nonzero_values]

lemma BasinLoopChartChainMonodromyData.of_nonzero_values_two_products
    {z₀ : ℂ}
    (hz₀ : z₀ ∈ basin_of_infinity (2 : ℂ))
    (hnonzero :
      ∀ (N : ℕ) (γ : BasinLoop (2 : ℂ) z₀) (t : ℝ),
        t ∈ Set.Icc (0 : ℝ) 1 →
          basinLoopRootEquationValue (2 : ℂ) N γ t ≠ 0)
    (N : ℕ) (γ : BasinLoop (2 : ℂ) z₀) :
    ((BasinLoopChartChainMonodromyData.of_nonzero_values_two hz₀ hnonzero).chain
      N γ).monodromyProduct = 1 := by
  simp [BasinLoopChartChainMonodromyData.of_nonzero_values_two,
    BasinLoopChartChain.monodromyProduct_of_nonzero_values]

/-- Escaping-level replacement for the all-level chart-chain interface. Instead
of requiring a chart chain at every early level, it records for each basin loop a
single escaping level, the one-chart chain there, and the resulting trivial
overlap product. A future descent/comparison theorem should transport this data
back to the all-level interface when needed. -/
structure EscapingLevelBasinLoopChartChainMonodromyData (c z₀ : ℂ) where
  base_mem_basin : z₀ ∈ basin_of_infinity c
  level : BasinLoop c z₀ → ℕ
  level_escapes :
    ∀ γ : BasinLoop c z₀, BasinLoopLevelEscapes c (level γ) γ
  chain :
    ∀ γ : BasinLoop c z₀, BasinLoopChartChain c (level γ) z₀ γ
  product_trivial :
    ∀ γ : BasinLoop c z₀, (chain γ).monodromyProduct = 1

/-- If a loop-wise escaping level is supplied, the escaping-level chart-chain
monodromy data is automatic by the punctured-plane one-chart construction. -/
noncomputable def EscapingLevelBasinLoopChartChainMonodromyData.of_level_escapes
    {c z₀ : ℂ}
    (hz₀ : z₀ ∈ basin_of_infinity c)
    (level : BasinLoop c z₀ → ℕ)
    (hesc : ∀ γ : BasinLoop c z₀, BasinLoopLevelEscapes c (level γ) γ) :
    EscapingLevelBasinLoopChartChainMonodromyData c z₀ where
  base_mem_basin := hz₀
  level := level
  level_escapes := hesc
  chain := fun γ => BasinLoopChartChain.of_escaping_level γ (hesc γ)
  product_trivial := by
    intro γ
    exact BasinLoopChartChain.monodromyProduct_of_escaping_level γ (hesc γ)

/-- `c = 2` specialization of the escaping-level replacement interface. -/
noncomputable def EscapingLevelBasinLoopChartChainMonodromyData.of_level_escapes_two
    {z₀ : ℂ}
    (hz₀ : z₀ ∈ basin_of_infinity (2 : ℂ))
    (level : BasinLoop (2 : ℂ) z₀ → ℕ)
    (hesc : ∀ γ : BasinLoop (2 : ℂ) z₀,
      BasinLoopLevelEscapes (2 : ℂ) (level γ) γ) :
    EscapingLevelBasinLoopChartChainMonodromyData (2 : ℂ) z₀ :=
  EscapingLevelBasinLoopChartChainMonodromyData.of_level_escapes hz₀ level hesc

/-- Stronger escaping-level replacement matching the descent theorem: for every
requested lower level `N₀` and every loop, record a higher escaping level `K ≥ N₀`
with its canonical one-chart chain. This is the formal version of taking a
sampled maximum in the notebook, but over the continuum loop and above an
arbitrary requested lower level. -/
structure ArbitrarilyHighEscapingLevelBasinLoopChartChainData (c z₀ : ℂ) where
  base_mem_basin : z₀ ∈ basin_of_infinity c
  levelAbove : BasinLoop c z₀ → ℕ → ℕ
  levelAbove_ge :
    ∀ (γ : BasinLoop c z₀) (N₀ : ℕ), N₀ ≤ levelAbove γ N₀
  levelAbove_escapes :
    ∀ (γ : BasinLoop c z₀) (N₀ : ℕ),
      BasinLoopLevelEscapes c (levelAbove γ N₀) γ
  chainAbove :
    ∀ (γ : BasinLoop c z₀) (N₀ : ℕ),
      BasinLoopChartChain c (levelAbove γ N₀) z₀ γ
  productAbove_trivial :
    ∀ (γ : BasinLoop c z₀) (N₀ : ℕ),
      (chainAbove γ N₀).monodromyProduct = 1

/-- Once arbitrarily high escaping levels are supplied, the corresponding
one-chart chains and trivial products are automatic. -/
noncomputable def ArbitrarilyHighEscapingLevelBasinLoopChartChainData.of_levelAbove_escapes
    {c z₀ : ℂ}
    (hz₀ : z₀ ∈ basin_of_infinity c)
    (levelAbove : BasinLoop c z₀ → ℕ → ℕ)
    (hge : ∀ (γ : BasinLoop c z₀) (N₀ : ℕ), N₀ ≤ levelAbove γ N₀)
    (hesc : ∀ (γ : BasinLoop c z₀) (N₀ : ℕ),
      BasinLoopLevelEscapes c (levelAbove γ N₀) γ) :
    ArbitrarilyHighEscapingLevelBasinLoopChartChainData c z₀ where
  base_mem_basin := hz₀
  levelAbove := levelAbove
  levelAbove_ge := hge
  levelAbove_escapes := hesc
  chainAbove := fun γ N₀ =>
    BasinLoopChartChain.of_escaping_level γ (hesc γ N₀)
  productAbove_trivial := by
    intro γ N₀
    exact BasinLoopChartChain.monodromyProduct_of_escaping_level γ (hesc γ N₀)

/-- A single uniform escaping level for each loop automatically gives
arbitrarily high escaping levels: for a requested lower level `N₀`, use
`max N₀ (level γ)`. -/
noncomputable def ArbitrarilyHighEscapingLevelBasinLoopChartChainData.of_eventual_level_escapes
    {c z₀ : ℂ}
    (hz₀ : z₀ ∈ basin_of_infinity c)
    (level : BasinLoop c z₀ → ℕ)
    (hesc : ∀ γ : BasinLoop c z₀, BasinLoopLevelEscapes c (level γ) γ) :
    ArbitrarilyHighEscapingLevelBasinLoopChartChainData c z₀ :=
  ArbitrarilyHighEscapingLevelBasinLoopChartChainData.of_levelAbove_escapes
    hz₀
    (fun γ N₀ => max N₀ (level γ))
    (fun _γ N₀ => le_max_left N₀ _)
    (fun γ N₀ =>
      BasinLoopLevelEscapes.mono (le_max_right N₀ (level γ)) (hesc γ))

/-- The one-level escaping replacement data can be upgraded to the
arbitrarily-high version needed by descent. -/
noncomputable def EscapingLevelBasinLoopChartChainMonodromyData.toArbitrarilyHigh
    {c z₀ : ℂ} (E : EscapingLevelBasinLoopChartChainMonodromyData c z₀) :
    ArbitrarilyHighEscapingLevelBasinLoopChartChainData c z₀ :=
  ArbitrarilyHighEscapingLevelBasinLoopChartChainData.of_eventual_level_escapes
    E.base_mem_basin E.level E.level_escapes

/-- `c = 2` specialization of the arbitrarily-high escaping-level replacement. -/
noncomputable def ArbitrarilyHighEscapingLevelBasinLoopChartChainData.of_levelAbove_escapes_two
    {z₀ : ℂ}
    (hz₀ : z₀ ∈ basin_of_infinity (2 : ℂ))
    (levelAbove : BasinLoop (2 : ℂ) z₀ → ℕ → ℕ)
    (hge : ∀ (γ : BasinLoop (2 : ℂ) z₀) (N₀ : ℕ), N₀ ≤ levelAbove γ N₀)
    (hesc : ∀ (γ : BasinLoop (2 : ℂ) z₀) (N₀ : ℕ),
      BasinLoopLevelEscapes (2 : ℂ) (levelAbove γ N₀) γ) :
    ArbitrarilyHighEscapingLevelBasinLoopChartChainData (2 : ℂ) z₀ :=
  ArbitrarilyHighEscapingLevelBasinLoopChartChainData.of_levelAbove_escapes
    hz₀ levelAbove hge hesc

/-- Arbitrarily high escaping-level chain data supplies exactly the high-level
trivial products needed by the chart-chain descent lemma, provided the all-level
chart-chain monodromy data is available for comparison. The remaining analytic
descent/comparison task is to relate these high-level chains to the all-level
chain family in `BasinLoopChartChainMonodromyData`; this lemma packages the
algebraic endpoint once that comparison is known. -/
lemma BasinLoopChartChainMonodromyData.representation_trivial_of_high_escaping_comparison
    {c z₀ : ℂ}
    (h : BasinLoopChartChainMonodromyData c z₀)
    (E : ArbitrarilyHighEscapingLevelBasinLoopChartChainData c z₀)
    (hcompare : ∀ (N : ℕ) (γ : BasinLoop c z₀),
      (h.chain (E.levelAbove γ N) γ).monodromyProduct =
        (E.chainAbove γ N).monodromyProduct) :
    h.representation.Trivial := by
  apply h.representation_trivial_of_arbitrarily_high_products
  intro N γ
  refine ⟨E.levelAbove γ N, E.levelAbove_ge γ N, ?_⟩
  rw [hcompare N γ]
  exact E.productAbove_trivial γ N

/-- Product-comparison data between an actual family of high escaping chart
chains and the canonical one-chart chains available at arbitrarily high
escaping levels. This is the step-13 target in the current PLAN 08 interface:
it does not assume that an all-level `BasinLoopChartChainMonodromyData` has
already been constructed. -/
structure HighEscapingActualChartChainsProductComparisonData
    {c z₀ : ℂ}
    (E : ArbitrarilyHighEscapingLevelBasinLoopChartChainData c z₀) where
  actualChain :
    ∀ (N : ℕ) (γ : BasinLoop c z₀),
      BasinLoopChartChain c (E.levelAbove γ N) z₀ γ
  product_eq :
    ∀ (N : ℕ) (γ : BasinLoop c z₀),
      (actualChain N γ).monodromyProduct =
        (E.chainAbove γ N).monodromyProduct

/-- Step-13 wrapper for the generalized overlap-equality theorem at high
escaping levels: for each requested lower level and loop, the actual high-level
chart chain is supplied directly, together with the overlap-neighborhood
equality hypotheses forcing its monodromy product to be trivial. This avoids
prematurely requiring an all-level
`BasinLoopChartChainMonodromyData`. -/
structure HighEscapingActualChartChainsEventuallyEqAtOverlapsData
    {c z₀ : ℂ}
    (E : ArbitrarilyHighEscapingLevelBasinLoopChartChainData c z₀) where
  actualChain :
    ∀ (N : ℕ) (γ : BasinLoop c z₀),
      BasinLoopChartChain c (E.levelAbove γ N) z₀ γ
  localLogs_eventuallyEq :
    ∀ (N : ℕ) (γ : BasinLoop c z₀),
      ChartChainLocalLogsEventuallyEqAtOverlaps (actualChain N γ)

/-- The high-level overlap-equality wrapper already suffices to compare the
actual chain products with the canonical one-chart products. -/
def HighEscapingActualChartChainsEventuallyEqAtOverlapsData.toProductComparisonData
    {c z₀ : ℂ}
    {E : ArbitrarilyHighEscapingLevelBasinLoopChartChainData c z₀}
    (A : HighEscapingActualChartChainsEventuallyEqAtOverlapsData E) :
    HighEscapingActualChartChainsProductComparisonData E where
  actualChain := A.actualChain
  product_eq := by
    intro N γ
    calc
      (A.actualChain N γ).monodromyProduct = 1 :=
        (A.localLogs_eventuallyEq N γ).monodromyProduct_eq_one
      _ = (E.chainAbove γ N).monodromyProduct := by
        exact (E.productAbove_trivial γ N).symm

/-- Special-case high-level comparison data: at every high escaping level, all
local logs in the actual chart chain are restrictions of a single global
zero-free logarithm branch. This packages the notebook's global-log route
without requiring an all-level chart-chain monodromy object first. -/
structure HighEscapingActualChartChainsLocalLogsRestrictGlobalData
    {c z₀ : ℂ}
    (E : ArbitrarilyHighEscapingLevelBasinLoopChartChainData c z₀) where
  actualChain :
    ∀ (N : ℕ) (γ : BasinLoop c z₀),
      BasinLoopChartChain c (E.levelAbove γ N) z₀ γ
  globalChart :
    ∀ (N : ℕ) (γ : BasinLoop c z₀),
      ZeroFreeChartRootBranchData (E.levelAbove γ N)
  localLogs_restrict :
    ∀ (N : ℕ) (γ : BasinLoop c z₀),
      ChartChainLocalLogsRestrictGlobal
        (actualChain N γ)
        (globalChart N γ)

/-- If all local logs in the actual high chains are restrictions of a common
global log branch, then the required high escaping product comparison follows. -/
def HighEscapingActualChartChainsLocalLogsRestrictGlobalData.toProductComparisonData
    {c z₀ : ℂ}
    {E : ArbitrarilyHighEscapingLevelBasinLoopChartChainData c z₀}
    (R : HighEscapingActualChartChainsLocalLogsRestrictGlobalData E) :
    HighEscapingActualChartChainsProductComparisonData E where
  actualChain := R.actualChain
  product_eq := by
    intro N γ
    calc
      (R.actualChain N γ).monodromyProduct = 1 :=
        (R.localLogs_restrict N γ).monodromyProduct_eq_one
      _ = (E.chainAbove γ N).monodromyProduct := by
        exact (E.productAbove_trivial γ N).symm

/-- Product-comparison data between an all-level chart-chain monodromy package
and the canonical one-chart chains available at arbitrarily high escaping
levels. This is the bridge form used once a high-level actual chain family has
been identified with the corresponding levels of an all-level
`BasinLoopChartChainMonodromyData`. -/
structure HighEscapingChartChainProductComparisonData
    {c z₀ : ℂ}
    (h : BasinLoopChartChainMonodromyData c z₀)
    (E : ArbitrarilyHighEscapingLevelBasinLoopChartChainData c z₀) where
  product_eq :
    ∀ (N : ℕ) (γ : BasinLoop c z₀),
      (h.chain (E.levelAbove γ N) γ).monodromyProduct =
        (E.chainAbove γ N).monodromyProduct

/-- Once a high-level actual comparison package has been connected to the
all-level chart family, it yields the earlier bridge-style comparison data. -/
def HighEscapingActualChartChainsProductComparisonData.toAllLevelProductComparisonData
    {c z₀ : ℂ}
    {E : ArbitrarilyHighEscapingLevelBasinLoopChartChainData c z₀}
    {h : BasinLoopChartChainMonodromyData c z₀}
    (C : HighEscapingActualChartChainsProductComparisonData E)
    (hchain : ∀ (N : ℕ) (γ : BasinLoop c z₀),
      h.chain (E.levelAbove γ N) γ = C.actualChain N γ) :
    HighEscapingChartChainProductComparisonData h E where
  product_eq := by
    intro N γ
    rw [hchain N γ]
    exact C.product_eq N γ

/-- Special-case analytic comparison data: at every high escaping level, all
local logs in the all-level chain are restrictions of a single global zero-free
logarithm branch. This is the formal version of the notebook's
"local logs are restrictions" proof: the all-level high product is forced to be
`1`, hence agrees with the canonical one-chart high product. -/
structure HighEscapingChartChainLocalLogsRestrictGlobalData
    {c z₀ : ℂ}
    (h : BasinLoopChartChainMonodromyData c z₀)
    (E : ArbitrarilyHighEscapingLevelBasinLoopChartChainData c z₀) where
  globalChart :
    ∀ (N : ℕ) (γ : BasinLoop c z₀),
      ZeroFreeChartRootBranchData (E.levelAbove γ N)
  localLogs_restrict :
    ∀ (N : ℕ) (γ : BasinLoop c z₀),
      ChartChainLocalLogsRestrictGlobal
        (h.chain (E.levelAbove γ N) γ)
        (globalChart N γ)

/-- If all local logs in the all-level high chains are restrictions of a common
global log branch, then the required high escaping product comparison follows. -/
noncomputable def HighEscapingChartChainLocalLogsRestrictGlobalData.toProductComparisonData
    {c z₀ : ℂ}
    {h : BasinLoopChartChainMonodromyData c z₀}
    {E : ArbitrarilyHighEscapingLevelBasinLoopChartChainData c z₀}
    (R : HighEscapingChartChainLocalLogsRestrictGlobalData h E) :
    HighEscapingChartChainProductComparisonData h E where
  product_eq := by
    intro N γ
    calc
      (h.chain (E.levelAbove γ N) γ).monodromyProduct = 1 :=
        (R.localLogs_restrict N γ).monodromyProduct_eq_one
      _ = (E.chainAbove γ N).monodromyProduct := by
        exact (E.productAbove_trivial γ N).symm

/-- Special case of comparison: if the all-level high chain is literally the
same chain as the canonical escaping one-chart chain, then their products agree.
The notebook's one-chart/refinement picture is a geometric generalization of
this exact-chain case. -/
noncomputable def HighEscapingChartChainProductComparisonData.of_chain_eq
    {c z₀ : ℂ}
    {h : BasinLoopChartChainMonodromyData c z₀}
    {E : ArbitrarilyHighEscapingLevelBasinLoopChartChainData c z₀}
    (hchain : ∀ (N : ℕ) (γ : BasinLoop c z₀),
      h.chain (E.levelAbove γ N) γ = E.chainAbove γ N) :
    HighEscapingChartChainProductComparisonData h E where
  product_eq := by
    intro N γ
    rw [hchain N γ]

/-- Once the analytic product comparison is available, the all-level monodromy
representation is trivial. -/
lemma HighEscapingChartChainProductComparisonData.representation_trivial
    {c z₀ : ℂ}
    {h : BasinLoopChartChainMonodromyData c z₀}
    {E : ArbitrarilyHighEscapingLevelBasinLoopChartChainData c z₀}
    (C : HighEscapingChartChainProductComparisonData h E) :
    h.representation.Trivial :=
  h.representation_trivial_of_high_escaping_comparison E C.product_eq

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

/-- Uniform escape over a continuous basin loop. Pointwise basin escape gives an
open cover of the compact interval by level-escape sets; a finite subcover and
forward invariance of the outside-open region give one level that works for the
whole loop. This is the compactness step isolated in the PLAN 08 blocker
notebook. -/
lemma BasinLoop.exists_levelEscapes
    {c z₀ : ℂ} (γ : BasinLoop c z₀) :
    ∃ N : ℕ, BasinLoopLevelEscapes c N γ := by
  let I : Set ℝ := Set.Icc (0 : ℝ) 1
  let U : ℕ → Set {t : ℝ // t ∈ I} := fun N =>
    {t : {t : ℝ // t ∈ I} |
      ‖(MLC.quadratic_map c)^[N] (γ.path t.1)‖ > ‖c‖ + 2}
  have hUo : ∀ N, IsOpen (U N) := by
    intro N
    have hcont_path : Continuous (fun t : {t : ℝ // t ∈ I} => γ.path t.1) := by
      exact (continuousOn_iff_continuous_restrict).1 (by
        simpa [I] using γ.continuousOn_path)
    have hcont_iter :
        Continuous (fun t : {t : ℝ // t ∈ I} =>
          (MLC.quadratic_map c)^[N] (γ.path t.1)) :=
      ((continuous_quadratic_map c).iterate N).comp hcont_path
    have hcont_norm :
        Continuous (fun t : {t : ℝ // t ∈ I} =>
          ‖(MLC.quadratic_map c)^[N] (γ.path t.1)‖) :=
      continuous_norm.comp hcont_iter
    simpa [U] using isOpen_lt continuous_const hcont_norm
  have hcover : Set.univ ⊆ ⋃ N, U N := by
    intro t _ht
    have hbasin : γ.path t.1 ∈ basin_of_infinity c :=
      γ.maps_to_basin t.1 (by simp [I] at t ⊢)
    rcases exists_iterate_mem_outside_open_of_mem_basin c (γ.path t.1) hbasin with
      ⟨N, hN⟩
    exact Set.mem_iUnion.2 ⟨N, hN⟩
  rcases isCompact_univ.elim_finite_subcover U hUo hcover with ⟨S, hS⟩
  let K : ℕ := S.sup id
  refine ⟨K, ?_⟩
  intro t ht
  have htcover :
      (⟨t, by simpa [I] using ht⟩ : {t : ℝ // t ∈ I}) ∈ ⋃ N ∈ S, U N :=
    hS (by simp)
  rcases Set.mem_iUnion.1 htcover with ⟨N, hNmem⟩
  rcases Set.mem_iUnion.1 hNmem with ⟨hNS, hNU⟩
  have hNK : N ≤ K := by
    dsimp [K]
    exact Finset.le_sup (f := id) hNS
  rcases Nat.exists_eq_add_of_le hNK with ⟨d, hKd⟩
  rw [hKd]
  have hd := MLC.quadratic_map_iter_maps_outside_open c hNU d
  rw [Nat.add_comm N d]
  simpa [Function.iterate_add, Function.comp_apply] using hd

/-- The compactness theorem supplies the loop-wise escaping level required by the
escaping-level chart-chain data. -/
noncomputable def EscapingLevelBasinLoopChartChainMonodromyData.of_uniform_escape
    {c z₀ : ℂ} (hz₀ : z₀ ∈ basin_of_infinity c) :
    EscapingLevelBasinLoopChartChainMonodromyData c z₀ :=
  EscapingLevelBasinLoopChartChainMonodromyData.of_level_escapes
    hz₀
    (fun γ => Classical.choose γ.exists_levelEscapes)
    (fun γ => Classical.choose_spec γ.exists_levelEscapes)

/-- `c = 2` specialization of the uniform-escape constructor. -/
noncomputable def EscapingLevelBasinLoopChartChainMonodromyData.of_uniform_escape_two
    {z₀ : ℂ} (hz₀ : z₀ ∈ basin_of_infinity (2 : ℂ)) :
    EscapingLevelBasinLoopChartChainMonodromyData (2 : ℂ) z₀ :=
  EscapingLevelBasinLoopChartChainMonodromyData.of_uniform_escape hz₀

/-- Uniform escape also supplies the arbitrarily-high escaping levels needed by
the algebraic descent theorem. -/
noncomputable def ArbitrarilyHighEscapingLevelBasinLoopChartChainData.of_uniform_escape
    {c z₀ : ℂ} (hz₀ : z₀ ∈ basin_of_infinity c) :
    ArbitrarilyHighEscapingLevelBasinLoopChartChainData c z₀ :=
  (EscapingLevelBasinLoopChartChainMonodromyData.of_uniform_escape hz₀).toArbitrarilyHigh

/-- `c = 2` specialization of arbitrarily-high escaping levels from uniform
escape over loops. -/
noncomputable def ArbitrarilyHighEscapingLevelBasinLoopChartChainData.of_uniform_escape_two
    {z₀ : ℂ} (hz₀ : z₀ ∈ basin_of_infinity (2 : ℂ)) :
    ArbitrarilyHighEscapingLevelBasinLoopChartChainData (2 : ℂ) z₀ :=
  ArbitrarilyHighEscapingLevelBasinLoopChartChainData.of_uniform_escape hz₀

/-- Uniform-escape specialization of the comparison endpoint: after the compact
uniform escape theorem, the only remaining input is product comparison with the
uniformly chosen high one-chart chains. -/
lemma BasinLoopChartChainMonodromyData.representation_trivial_of_uniform_escape_comparison
    {c z₀ : ℂ}
    (h : BasinLoopChartChainMonodromyData c z₀)
    (hcompare : ∀ (N : ℕ) (γ : BasinLoop c z₀),
      (h.chain
          ((ArbitrarilyHighEscapingLevelBasinLoopChartChainData.of_uniform_escape
            h.base_mem_basin).levelAbove γ N) γ).monodromyProduct =
        ((ArbitrarilyHighEscapingLevelBasinLoopChartChainData.of_uniform_escape
            h.base_mem_basin).chainAbove γ N).monodromyProduct) :
    h.representation.Trivial :=
  h.representation_trivial_of_high_escaping_comparison
    (ArbitrarilyHighEscapingLevelBasinLoopChartChainData.of_uniform_escape
      h.base_mem_basin)
    hcompare

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

/-- The logarithmic-series coordinate vanishes at `0` by definition. -/
lemma logSeriesBottcherApprox_zero (c : ℂ) :
    MLC.logSeriesBottcherApprox c 0 = 0 := by
  simp [MLC.logSeriesBottcherApprox]

/-- The all-level nonvanishing input from the first notebook option is false for
the current all-level interface: at `c = 2`, the constant basin loop based at
`0` has level-`0` root-equation value equal to `0`. This is why PLAN 08 needs
the escaping-level reformulation rather than chart chains at every early level. -/
lemma not_forall_basinLoopRootEquationValue_ne_zero_two_zero :
    ¬ (∀ (N : ℕ) (γ : BasinLoop (2 : ℂ) (0 : ℂ)) (t : ℝ),
      t ∈ Set.Icc (0 : ℝ) 1 →
        basinLoopRootEquationValue (2 : ℂ) N γ t ≠ 0) := by
  intro hnonzero
  let γ : BasinLoop (2 : ℂ) (0 : ℂ) :=
    BasinLoop.constant (2 : ℂ) (0 : ℂ) zero_mem_basin_two_constructive
  have hneq := hnonzero 0 γ 0 (by simp)
  have hval : basinLoopRootEquationValue (2 : ℂ) 0 γ 0 = 0 := by
    simp [γ, BasinLoop.constant, basinLoopRootEquationValue, logSeriesBottcherApprox_zero]
  exact hneq hval

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

/-- Cover-strategy seam: construct the coherent pullback on a cover where
monodromy is trivial, prove that the lifted coordinate is constant on fibers
(deck-invariant), and descend it to a basin coordinate with the required
properties. This is the Lean form of the group-theoretic cover strategy. -/
structure MonodromyTrivializingCoverBasinExtensionDataFor (c : ℂ) where
  Cover : Type
  projection : Cover → ℂ
  liftedPhi : Cover → ℂ
  phi : ℂ → ℂ
  projection_maps_basin :
    ∀ x : Cover, projection x ∈ basin_of_infinity c
  covers_basin :
    ∀ z : ℂ, z ∈ basin_of_infinity c → ∃ x : Cover, projection x = z
  same_fiber_liftedPhi :
    ∀ x y : Cover, projection x = projection y → liftedPhi x = liftedPhi y
  descends_to_phi :
    ∀ x : Cover, phi (projection x) = liftedPhi x
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

/-- A monodromy-trivializing cover with deck-invariant lifted coordinate gives
the logarithmic-series basin extension data. -/
noncomputable def MonodromyTrivializingCoverBasinExtensionDataFor.toLogSeriesBasinExtensionDataFor
    {c : ℂ} (h : MonodromyTrivializingCoverBasinExtensionDataFor c) :
    LogSeriesBasinExtensionDataFor c where
  phi := h.phi
  extends_near := h.extends_near
  norm_on_basin := h.norm_on_basin
  basin_of_norm_gt_one := h.basin_of_norm_gt_one
  conj_on_basin := h.conj_on_basin
  holo_on_basin := h.holo_on_basin
  modulus_on_basin := h.modulus_on_basin
  tendsto_div_atInfinity := h.tendsto_div_atInfinity

theorem classicalGlobalBottcherTheoremFor_of_monodromyTrivializingCoverData
    {c : ℂ} (h : MonodromyTrivializingCoverBasinExtensionDataFor c) :
    ClassicalGlobalBottcherTheoremFor c :=
  classicalGlobalBottcherTheoremFor_of_logSeriesBasinExtensionData
    h.toLogSeriesBasinExtensionDataFor

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
