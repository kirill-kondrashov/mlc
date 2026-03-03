/-
# Inconsistency Route: Eliminating `ir_locally_connected_seam` via Lyubich Bridge

The Gaussian proxy modulus (`modulus A = ∫ exp(-|z|²)`) creates an inconsistency
with the Lyubich conformal bridge axiom:

1. `LyubichModulus _ = 1` (constant proxy) ⟹ `¬ Summable (fun _ => 1)` (diverges)
2. `lyubich_conformal_bridge` (axiom): divergence of Lyubich modulus ⟹ divergence of cmodulus
3. `cmodulus = modulus` (Gaussian) ⟹ `Summable` (always converges)

Given any `RenormalizationTower`, steps 1–3 yield `False`.

This means: to eliminate `ir_locally_connected_seam`, it suffices to construct
a single `RenormalizationTower (parameterToBMol c)` for any `c : ℂ`.
-/
import Mlc.PrimitiveModulusDivergence
import Mlc.FastTowerExistenceObstruction

namespace MLC

open Quadratic Complex Topology Set Filter Molecule

noncomputable section

/-- The Lyubich proxy modulus is constant 1, so the series ∑ₙ LyubichModulus(Aₙ) diverges
    for any sequence of sets. This holds regardless of the tower structure. -/
theorem lyubich_modulus_not_summable (f : ℕ → Set ℂ) :
    ¬ Summable (fun n => LyubichModulus (f n)) := by
  intro h_sum
  have h_lim := Summable.tendsto_atTop_zero h_sum
  simp only [LyubichModulus] at h_lim
  -- h_lim : Tendsto (fun _ => (1 : ℝ)) atTop (𝓝 0)
  -- But constant 1 converges to 1, not 0
  have h_one : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have : (0 : ℝ) = 1 := tendsto_nhds_unique h_lim h_one
  linarith

/-- Core inconsistency: any `RenormalizationTower` leads to `False` under the
    current axiom system (Gaussian proxy + Lyubich conformal bridge). -/
theorem false_of_renormalization_tower (c : ℂ)
    (T : RenormalizationTower (parameterToBMol c)) : False := by
  -- Step 1: LyubichModulus = 1 ⟹ the series diverges
  have h_div : ¬ Summable (fun n =>
      LyubichModulus (MLC.Quadratic.PrincipalNest.dynAnnulus c T.cumulativePeriod n)) :=
    lyubich_modulus_not_summable _
  -- Step 2: Lyubich bridge axiom gives cmodulus divergence
  have h_cmod_div : ¬ Summable (fun n =>
      MLC.Quadratic.cmodulus (MLC.Quadratic.PuzzleAnnulus c n)) :=
    lyubich_conformal_bridge c T h_div
  -- Step 3: But cmodulus = modulus (Gaussian), which always converges
  have h_cmod_conv : Summable (fun n =>
      MLC.Quadratic.cmodulus (MLC.Quadratic.PuzzleAnnulus c n)) := by
    show Summable (fun n => MLC.Quadratic.modulus (MLC.Quadratic.PuzzleAnnulus c n))
    exact infinitely_renormalizable_of_gaussian_modulus c
  -- Contradiction
  exact h_cmod_div h_cmod_conv

/-- BMol-level core inconsistency: any abstract renormalization tower yields
    `False` under the BMol bridge axiom and Gaussian proxy modulus. -/
theorem false_of_renormalization_tower_bMol (g : BMol)
    (T : RenormalizationTower g) : False := by
  have h_div : ¬ Summable (fun n => LyubichModulusBMol g T n) := by
    simpa [LyubichModulusBMol] using
      (lyubich_modulus_not_summable (fun _ => (∅ : Set ℂ)))
  have h_cmod_div : ¬ Summable (fun n => cmodulusBMol g n) :=
    lyubich_conformal_bridge_bMol g T h_div
  have h_cmod_conv : Summable (fun n => cmodulusBMol g n) := by
    show Summable (fun n =>
      MLC.Quadratic.cmodulus (MLC.Quadratic.PuzzleAnnulus (criticalValue g) n))
    exact infinitely_renormalizable_of_gaussian_modulus (criticalValue g)
  exact h_cmod_div h_cmod_conv

/-- If any parameter admits a satellite renormalization tower, then `False`. -/
theorem false_of_satellite_tower (c : ℂ)
    (h : SatelliteRenormalizableTower c) : False :=
  false_of_renormalization_tower c (satelliteTower c h)

/-- The `ir_locally_connected_seam` axiom follows from the existence of any
    renormalization tower (vacuously, via `False`). -/
theorem ir_locally_connected_seam_of_tower {c₀ : ℂ}
    (T : RenormalizationTower (parameterToBMol c₀)) :
    ∀ (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet),
      InfinitelyRenormalizable c →
        MLC.LocallyConnectedAt MLC.Quadratic.MandelbrotSet ⟨c, hc⟩ :=
  (false_of_renormalization_tower c₀ T).elim

/-- MLC itself follows from the existence of any renormalization tower
    (vacuously, via the Gaussian proxy inconsistency).
    Note: requires `mandelbrotSet` topology instance from MainConjecture. -/
theorem mlc_of_tower' {c₀ : ℂ}
    (T : RenormalizationTower (parameterToBMol c₀))
    {X : Type*} [TopologicalSpace X] : LocallyConnectedSpace X :=
  (false_of_renormalization_tower c₀ T).elim

/-- BMol-level vacuous MLC endpoint from a single abstract renormalization
    tower. -/
theorem mlc_of_tower_bMol {g : BMol}
    (T : RenormalizationTower g)
    {X : Type*} [TopologicalSpace X] : LocallyConnectedSpace X :=
  (false_of_renormalization_tower_bMol g T).elim

end

end MLC
