import Mlc.RenormalizationTypes
import Mlc.MoleculeRenormalizationTower
import Mlc.Quadratic.Complex.PrincipalNestShrink
import Mlc.Quadratic.Complex.ConformalGroetzsch
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.Linarith

namespace MLC

open Quadratic Complex Topology Set Filter Molecule

/-- 
A priori bounds for primitive renormalization.
According to Lyubich's theory, primitive renormalization steps yield annuli in the 
principal nest with conformal modulus bounded away from zero.

This relies on the fact that primitive renormalizations are "simple" and do not 
involve parabolic or Siegel degenerations (which are handled by the satellite case).

References:
* Lyubich, M. "Dynamics of quadratic polynomials I-II", Acta Math. 178 (1997).
* The Pacman Renormalization paper (Dudko-Lyubich-Selinger) focuses on the satellite case
  but builds upon the quadratic-like (primitive) theory.
-/
lemma primitive_step_modulus_bound (c : ℂ) (T : RenormalizationTower (parameterToBMol c)) :
    ∃ μ > 0, ∀ n, IsPrimitive (T.rel n) → 
      MLC.Quadratic.modulus (MLC.Quadratic.PrincipalNest.dynAnnulus c T.cumulativePeriod n) ≥ μ := by
  -- This statement assumes `modulus` behaves like conformal modulus.
  -- With Gaussian modulus, this is false for large n as the annuli shrink in size.
  -- We leave this as a sorry to indicate the missing Conformal Modulus formalization.
  sorry

/-- Divergence of moduli for primitive renormalization towers (Lyubich's Theorem).
    This requires the conformal modulus and the fact that primitive renormalizations
    yield definite moduli. In the current formalization, `modulus` is Gaussian
    (summable), so this step cannot be proved without the conformal theory. -/
lemma primitive_modulus_divergence (c : ℂ) (T : RenormalizationTower (parameterToBMol c))
    (h_inf_prim : {n | IsPrimitive (T.rel n)}.Infinite) :
    ¬ Summable (fun n => MLC.Quadratic.modulus (MLC.Quadratic.PrincipalNest.dynAnnulus c T.cumulativePeriod n)) := by
  -- Obtain the a priori bound
  obtain ⟨μ, hμ_pos, h_bound⟩ := primitive_step_modulus_bound c T
  
  -- If the sum were summable, the terms must tend to zero.
  intro h_summable
  have h_to_zero : Filter.Tendsto (fun n => MLC.Quadratic.modulus (MLC.Quadratic.PrincipalNest.dynAnnulus c T.cumulativePeriod n)) Filter.atTop (nhds 0) :=
    Summable.tendsto_atTop_zero h_summable
  
  -- But we have infinitely many terms ≥ μ > 0.
  -- This contradicts Tendsto ... 0.
  
  -- We use the fact that the set of primitive indices is infinite to find large indices.
  -- Since μ > 0, the interval (-μ, μ) is a neighborhood of 0.
  -- h_to_zero implies eventually all terms are in (-μ, μ).
  rw [Metric.tendsto_atTop] at h_to_zero
  specialize h_to_zero μ hμ_pos
  rcases h_to_zero with ⟨N, hN⟩
  
  -- Find a primitive step n ≥ N
  rcases Set.Infinite.exists_gt h_inf_prim N with ⟨n, hn_prim, hn_ge⟩
  
  -- For this n, modulus ≥ μ
  have h_mod_ge : MLC.Quadratic.modulus (MLC.Quadratic.PrincipalNest.dynAnnulus c T.cumulativePeriod n) ≥ μ :=
    h_bound n hn_prim
    
  -- But n ≥ N implies modulus < μ
  have h_mod_lt : MLC.Quadratic.modulus (MLC.Quadratic.PrincipalNest.dynAnnulus c T.cumulativePeriod n) < μ := by
    have h_mem := hN n (le_of_lt hn_ge)
    rw [dist_zero_right, Real.norm_eq_abs] at h_mem
    -- Modulus is non-negative
    have h_nonneg := MLC.Quadratic.modulus_nonneg (MLC.Quadratic.PrincipalNest.dynAnnulus c T.cumulativePeriod n)
    rw [abs_eq_self.mpr h_nonneg] at h_mem
    exact h_mem

  -- Contradiction
  linarith

end MLC