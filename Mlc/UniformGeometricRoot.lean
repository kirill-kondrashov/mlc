import Mlc.RetractionLocalConnectivity
import Mlc.UniformGeometricApproximation
import Mlc.UniformGeometricDomain

/-!
# Conditional MLC theorem from uniform geometric estimates

The hypothesis is a tower of finite-stage maps with explicit adjacent
displacement, outer-proximity, and fixing bounds. The continuous limit and
local connectedness follow from those bounds; tower existence is not asserted.
-/

namespace MLC.UniformGeometry

theorem mandelbrot_locallyConnected_of_orbitRetractionTower
    {K : Set ℂ} (hcompact : IsCompact K) (hconvex : Convex ℝ K)
    (hMK : MLC.mandelbrotSet ⊆ K) (T : OrbitRetractionTower K) :
    LocallyConnectedSpace MLC.mandelbrotSet := by
  obtain ⟨r, _, _, hrange, hfix⟩ := exists_continuous_retraction hcompact hMK T
  have hrM : ∀ x, r x ∈ MLC.mandelbrotSet := by
    intro x
    change r x ∈ MLC.Categorical.Mandelbrot.set
    rw [← hrange]
    exact Set.mem_range_self x
  exact mandelbrot_locallyConnected_of_retraction hconvex hMK r r.continuous
    hrM (fun c hc => hfix ⟨c, hMK hc⟩ hc)

theorem mandelbrot_locallyConnected_of_squareTower
    (T : OrbitRetractionTower parameterSquare) :
    LocallyConnectedSpace MLC.mandelbrotSet :=
  mandelbrot_locallyConnected_of_orbitRetractionTower isCompact_parameterSquare
    convex_parameterSquare mandelbrot_subset_parameterSquare T

theorem categorical_mlc_of_squareTower
    (T : OrbitRetractionTower parameterSquare) :
    MLC.Categorical.MLCConjecture :=
  mandelbrot_locallyConnected_of_squareTower T

/-- Straight-line interpolation to the tower's limit fixes the Mandelbrot set
at all times and has terminal image equal to it. -/
theorem exists_squareTower_strongDeformation
    (T : OrbitRetractionTower parameterSquare) :
    ∃ H : parameterSquare × Set.Icc (0 : ℝ) 1 → parameterSquare,
      Continuous H ∧
      (∀ x, H (x, ⟨0, by norm_num⟩) = x) ∧
      Set.range (fun x => (H (x, ⟨1, by norm_num⟩)).1) = MLC.mandelbrotSet ∧
      ∀ c (hc : c ∈ MLC.mandelbrotSet) t,
        H (⟨c, mandelbrot_subset_parameterSquare hc⟩, t) =
          ⟨c, mandelbrot_subset_parameterSquare hc⟩ := by
  obtain ⟨r, _, _, hrange, hfix⟩ := exists_continuous_retraction
    isCompact_parameterSquare mandelbrot_subset_parameterSquare T
  have hrM : ∀ x, r x ∈ MLC.mandelbrotSet := by
    intro x
    change r x ∈ MLC.Categorical.Mandelbrot.set
    rw [← hrange]
    exact Set.mem_range_self x
  obtain ⟨H, hcont, hzero, hone, hfixed⟩ :=
    mandelbrot_strongDeformationRetract_of_retraction convex_parameterSquare
      mandelbrot_subset_parameterSquare r r.continuous hrM
      (fun c hc => hfix ⟨c, mandelbrot_subset_parameterSquare hc⟩ hc)
  refine ⟨H, hcont, hzero, ?_, hfixed⟩
  have heq : (fun x => (H (x, ⟨1, by norm_num⟩)).1) = r := funext hone
  rw [heq]
  exact hrange

end MLC.UniformGeometry
