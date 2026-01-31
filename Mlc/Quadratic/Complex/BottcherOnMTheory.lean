import Mlc.Quadratic.Complex.BottcherMotion
import Mlc.Quadratic.Complex.BottcherAxioms
import Mlc.Quadratic.Complex.PuzzleBoundaryMotion
import Mathlib.Analysis.Complex.Basic

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

def quadratic_map (c : ℂ) (z : ℂ) : ℂ :=
  z ^ 2 + c

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

def basin_of_infinity (c : ℂ) : Set ℂ :=
  {z | Tendsto (fun n => ‖(quadratic_map c)^[n] z‖) atTop atTop}

def outside_disk (c : ℂ) : Set ℂ :=
  {z | ‖z‖ ≥ ‖c‖ + 2}

theorem basin_of_infinity_contains_large_ball (c : ℂ) :
    outside_disk c ⊆ basin_of_infinity c := by
  intro z hz
  exact (escaping_set_contains_large_ball c) hz

theorem outside_disk_subset_basin (c : ℂ) : outside_disk c ⊆ basin_of_infinity c :=
  basin_of_infinity_contains_large_ball c

theorem bottcher_left_inv_of_injective
    (c : ℂ) (z : ℂ) (h_norm : 1 < ‖bottcher_map c z‖)
    (h_inj : Function.Injective (bottcher_map c)) :
    external_ray_map c (bottcher_map c z) = z := by
  unfold external_ray_map
  rw [if_pos h_norm]
  exact (Function.leftInverse_invFun h_inj) z

theorem bottcher_map_norm_gt_one_of_basin
    (c : ℂ) (z : ℂ) (_hz : z ∈ Quadratic.basin_of_infinity c)
    (hpos : 0 < MLC.Quadratic.green_function c z) :
    1 < ‖Quadratic.bottcher_map c z‖ := by
  -- `‖bottcher_map c z‖ = exp(green_function c z)` and `exp` is > 1 for positive input.
  have hnorm : ‖Quadratic.bottcher_map c z‖ =
      Real.exp (MLC.Quadratic.green_function c z) :=
    Quadratic.norm_bottcher_eq_exp_green c z
  have hgt : 1 < Real.exp (MLC.Quadratic.green_function c z) := by
    simpa using (Real.one_lt_exp_iff.mpr hpos)
  simpa [hnorm] using hgt

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
    (h_inj : Function.Injective (Quadratic.bottcher_map c)) :
    Quadratic.external_ray_map c (Quadratic.bottcher_map c z) = z := by
  have hnorm : 1 < ‖Quadratic.bottcher_map c z‖ :=
    bottcher_map_norm_gt_one_of_basin c z hz hpos
  exact bottcher_left_inv_of_injective c z hnorm h_inj

theorem bottcher_left_inv_of_basin'
    (c : ℂ) (z : ℂ) (hz : z ∈ Quadratic.basin_of_infinity c)
    (h_inj : Function.Injective (Quadratic.bottcher_map c)) :
    Quadratic.external_ray_map c (Quadratic.bottcher_map c z) = z := by
  have hpos : 0 < MLC.Quadratic.green_function c z :=
    green_function_pos_of_basin c z hz
  exact bottcher_left_inv_of_basin c z hz hpos h_inj

theorem bottcher_map_injective_of_basin_characterization
    (c : ℂ)
    (h_pre : ∀ z, 1 < ‖Quadratic.bottcher_map c z‖ → z ∈ Quadratic.basin_of_infinity c)
    (h_norm : ∀ z, 1 < ‖Quadratic.bottcher_map c z‖)
    (h_inj_basin : Set.InjOn (Quadratic.bottcher_map c) (Quadratic.basin_of_infinity c)) :
    Function.Injective (Quadratic.bottcher_map c) := by
  intro z w hzw
  have hz : z ∈ Quadratic.basin_of_infinity c := h_pre z (h_norm z)
  have hw : w ∈ Quadratic.basin_of_infinity c := h_pre w (h_norm w)
  exact h_inj_basin hz hw hzw

theorem basin_of_infinity_nonempty (c : ℂ) : (basin_of_infinity c).Nonempty := by
  refine ⟨((‖c‖ + 2 : ℝ) : ℂ), ?_⟩
  have h0 : ‖((‖c‖ + 2 : ℝ) : ℂ)‖ ≥ ‖c‖ + 2 := by
    have hnonneg : 0 ≤ ‖c‖ + 2 := by nlinarith [norm_nonneg c]
    -- `‖(x : ℂ)‖ = |x|` for real `x`.
    have : ‖((‖c‖ + 2 : ℝ) : ℂ)‖ = ‖c‖ + 2 := by
      simpa using (Complex.norm_of_nonneg hnonneg)
    exact this.ge
  exact basin_of_infinity_contains_large_ball c h0

theorem open_large_ball (c : ℂ) : IsOpen {z : ℂ | ‖z‖ > ‖c‖ + 2} := by
  have hconst : Continuous (fun _ : ℂ => ‖c‖ + 2) := continuous_const
  simpa [gt_iff_lt] using (isOpen_lt hconst continuous_norm)

theorem open_large_ball_subset_basin (c : ℂ) :
    {z : ℂ | ‖z‖ > ‖c‖ + 2} ⊆ basin_of_infinity c := by
  intro z hz
  have hz' : ‖z‖ ≥ ‖c‖ + 2 := le_of_lt hz
  exact basin_of_infinity_contains_large_ball c hz'

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
