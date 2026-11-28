import Mlc.ProgrammeRoot
import Mlc.Research.Stacking
import Mlc.Research.CollarCriterion

/-!
# The geometric form of the programme

`Mlc/ProgrammeRoot.lean` decomposes Problems 4.3 and 4.4 into sixteen abstract lemmas about a
dictionary `Geometry`, whose towers carry abstract widths. This module states four of them, and the
phase–parameter transfer, as geometric statements about the level sets of the towers, and derives
the abstract fields from them.

* **Structure `LevelGeometry`**: a `Geometry` together with the level towers (`LevelTower`) behind
  its towers, `levels c` for the tower of `c` and `vlevels c` for its virtual tower, that is, with
  the filled sets and the range domains of the levels, such that the widths are the ones of the
  dictionary. As `Geometry` is, it is a parameter of the statements: that the sets are the filled
  Julia sets and the range domains of quadratic-like restrictions of `f_c` is the faithfulness of the
  dictionary, which the structure does not contain (every width tower is realized by round levels,
  `RoundTower.lean`).
* **`LevelGeometry.UnboundedCollars`, `LevelGeometry.VirtualCollars`**: Lemma G in collar form, for
  the tower of unbounded satellite type and for the virtual near-neutral tower: collars of bounded
  dilatation and definite modulus at the jumps at the levels of large relative period
  (`LevelTower.largePeriodJumpCap_of_collars`).
* **`LevelGeometry.UnboundedStacked`, `LevelGeometry.VirtualStacked`**: Lemma D in the form of stacked
  annuli (`LevelTower.StackedAnnuli`, `LevelTower.linearDichotomy_of_stacked`).
* **`LevelGeometry.Comparison`**: the phase–parameter comparison of the moduli of the levels of the
  dictionary with the moduli of a nest in `M` (`Geometry.transfer_of_comparison`).
* **Theorem `MLC.mlc_of_levelGeometry`**: MLC from the six published lemmas, the Teichmüller
  contraction for the pseudo-Siegel and for the virtual levels (TC′, VT1), the virtual Julia set (VJ),
  the dichotomy for the virtual bounded type (VD1), the virtual transfer (VT), and the five geometric
  statements above. None of them is proved here.
-/

namespace MLC.Research

open MeasureTheory ENNReal Set Real

noncomputable section

/-- **A dictionary with the level sets of its towers.** The level towers `levels c` and `vlevels c`
carry, with the widths of `tower c` and `vtower c`, the filled sets and the range domains of the
levels. -/
structure LevelGeometry extends Geometry where
  levels : ℂ → Option LevelTower
  vlevels : ℂ → Option LevelTower
  tower_eq : ∀ c, tower c = (levels c).map LevelTower.toWidthTower
  vtower_eq : ∀ c, vtower c = (vlevels c).map LevelTower.toWidthTower

namespace LevelGeometry

variable (LG : LevelGeometry)

/-- **Lemma G in collar form (Problem 4.3).** At a parameter of unbounded satellite type, the
annulus of the level that follows a jump by the factor `C₀` at a level of relative period above
`P₀` has a collar of dilatation at most `K₀` and modulus at least `μ₀ / 2π`. -/
def UnboundedCollars : Prop :=
  ∀ c ∈ MLC.Quadratic.MandelbrotSet, c ∉ interior MLC.Quadratic.MandelbrotSet →
    LG.toGeometry.cls c = .unboundedSatellite → ∃ L : LevelTower, LG.levels c = some L ∧
      ∃ (P₀ : ℕ) (C₀ K₀ μ₀ : ℝ), 0 < C₀ ∧ 0 < K₀ ∧ 0 < μ₀ ∧
        ∀ m, P₀ < L.rel m → L.Jumps C₀ m → ∃ Kd r R : ℝ, Kd ≤ K₀ ∧
          μ₀ ≤ Real.log (R / r) ∧ IsCollar (L.filled (m + 1)) (L.target (m + 1)) Kd r R

/-- **Lemma D in the form of stacked annuli (Problem 4.3).** At a parameter of unbounded satellite
type, the levels have stacked annuli for every threshold. -/
def UnboundedStacked : Prop :=
  ∀ c ∈ MLC.Quadratic.MandelbrotSet, c ∉ interior MLC.Quadratic.MandelbrotSet →
    LG.toGeometry.cls c = .unboundedSatellite → ∃ L : LevelTower, LG.levels c = some L ∧
      ∀ C : ℝ, 0 < C → ∃ c' : ℝ, 0 < c' ∧ ∃ A' : ℝ, 0 ≤ A' ∧ L.StackedAnnuli C c' A'

/-- **Lemma VG2 in collar form (Problem 4.4, virtual near-neutral).** -/
def VirtualCollars : Prop :=
  ∀ c ∈ MLC.Quadratic.MandelbrotSet, c ∉ interior MLC.Quadratic.MandelbrotSet →
    LG.toGeometry.cls c = .virtualNearNeutral → ∃ L : LevelTower, LG.vlevels c = some L ∧
      ∃ (P₀ : ℕ) (C₀ K₀ μ₀ : ℝ), 0 < C₀ ∧ 0 < K₀ ∧ 0 < μ₀ ∧
        ∀ m, P₀ < L.rel m → L.Jumps C₀ m → ∃ Kd r R : ℝ, Kd ≤ K₀ ∧
          μ₀ ≤ Real.log (R / r) ∧ IsCollar (L.filled (m + 1)) (L.target (m + 1)) Kd r R

/-- **Lemma VD2 in the form of stacked annuli (Problem 4.4, virtual near-neutral).** -/
def VirtualStacked : Prop :=
  ∀ c ∈ MLC.Quadratic.MandelbrotSet, c ∉ interior MLC.Quadratic.MandelbrotSet →
    LG.toGeometry.cls c = .virtualNearNeutral → ∃ L : LevelTower, LG.vlevels c = some L ∧
      ∀ C : ℝ, 0 < C → ∃ c' : ℝ, 0 < c' ∧ ∃ A' : ℝ, 0 ≤ A' ∧ L.StackedAnnuli C c' A'

/-- **The phase–parameter comparison for the level sets of the dictionary.** An a priori bound on the
degeneration of the tower of `c` gives a connected nest in `M` around `c` such that the modulus of
the annulus of each level is at most a fixed multiple `Kd` of the modulus of the corresponding
annulus of the nest. -/
def Comparison : Prop :=
  ∀ c ∈ MLC.Quadratic.MandelbrotSet, ∀ (B : ℝ), 0 < B → LG.toGeometry.HasBound c B →
    ∃ L : LevelTower, LG.levels c = some L ∧
      ∃ (D : ConnectedNest MLC.Quadratic.MandelbrotSet c) (Kd : ℝ), 0 < Kd ∧
        ∀ k, L.modulus k ≤ ENNReal.ofReal Kd * extWidth volume (D.loops k)

/-- Collars at the large-period jumps give Lemma G. -/
theorem unboundedJumpCap (h : LG.UnboundedCollars) : LG.toGeometry.UnboundedJumpCap := by
  intro c hc hi hcls
  obtain ⟨L, hL, P₀, C₀, K₀, μ₀, hC₀, hK₀, hμ₀, hcol⟩ := h c hc hi hcls
  exact ⟨L.toWidthTower, by rw [LG.tower_eq c, hL]; rfl, P₀, C₀, 2 * π * K₀ / μ₀, hC₀,
    L.largePeriodJumpCap_of_collars hK₀ hμ₀ hcol⟩

/-- Stacked annuli give Lemma D. -/
theorem unboundedDichotomy (h : LG.UnboundedStacked) : LG.toGeometry.UnboundedDichotomy := by
  intro c hc hi hcls
  obtain ⟨L, hL, hst⟩ := h c hc hi hcls
  exact ⟨L.toWidthTower, by rw [LG.tower_eq c, hL]; rfl, L.linearDichotomy_of_stacked hst⟩

/-- Collars at the large-period jumps of the virtual levels give Lemma VG2. -/
theorem virtualJumpCap (h : LG.VirtualCollars) : LG.toGeometry.VirtualJumpCap := by
  intro c hc hi hcls
  obtain ⟨L, hL, P₀, C₀, K₀, μ₀, hC₀, hK₀, hμ₀, hcol⟩ := h c hc hi hcls
  exact ⟨L.toWidthTower, by rw [LG.vtower_eq c, hL]; rfl, P₀, C₀, 2 * π * K₀ / μ₀, hC₀,
    L.largePeriodJumpCap_of_collars hK₀ hμ₀ hcol⟩

/-- Stacked annuli of the virtual levels give Lemma VD2. -/
theorem virtualLinearDichotomy (h : LG.VirtualStacked) :
    LG.toGeometry.VirtualLinearDichotomy := by
  intro c hc hi hcls
  obtain ⟨L, hL, hst⟩ := h c hc hi hcls
  exact ⟨L.toWidthTower, by rw [LG.vtower_eq c, hL]; rfl, L.linearDichotomy_of_stacked hst⟩

/-- The comparison for the level sets of the dictionary gives Lemma T. -/
theorem transfer (h : LG.Comparison) : LG.toGeometry.Transfer := by
  refine LG.toGeometry.transfer_of_comparison ?_
  intro c hc B hB hbound
  obtain ⟨L, hL, D, Kd, hKd, hcmp⟩ := h c hc B hB hbound
  exact ⟨L, D, Kd, hKd, by rw [LG.tower_eq c, hL]; rfl, hcmp⟩

end LevelGeometry

end

end MLC.Research

namespace MLC

open Research

/-- **MLC from the geometric form of the programme.** For a dictionary with the level sets of its
towers, MLC follows from the six published lemmas, the Teichmüller contraction for the
pseudo-Siegel and for the virtual levels, the virtual Julia sets, the dichotomy for the virtual bounded
type, the virtual transfer, and five geometric statements about the level sets: collars at the
large-period jumps and stacked annuli, for the unbounded satellite tower and for the virtual
near-neutral tower, and the phase–parameter comparison of moduli. None of the hypotheses is
proved. -/
theorem mlc_of_levelGeometry (LG : LevelGeometry) (hcomp : LG.Comparison)
    (hy : LG.toGeometry.Yoccoz) (hT : LG.toGeometry.TeichmullerContraction)
    (hB : LG.toGeometry.BoundedTypeInputs) (hA : LG.toGeometry.AntiMoleculeInputs)
    (hN : LG.toGeometry.Neutral) (hQ : LG.toGeometry.QuadraticGrowth)
    (hTC : LG.toGeometry.UnboundedTeichmuller) (hGc : LG.UnboundedCollars)
    (hDs : LG.UnboundedStacked) (hVJ : LG.toGeometry.VirtualJulia)
    (hVT1 : LG.toGeometry.VirtualTeichmuller) (hVD1 : LG.toGeometry.VirtualDichotomy)
    (hVGc : LG.VirtualCollars) (hVDs : LG.VirtualStacked)
    (hVT : LG.toGeometry.VirtualTransfer) :
    LocallyConnectedSpace mandelbrotSet :=
  mlc_of_programme (G := LG.toGeometry)
    { transfer := LG.transfer hcomp
      yoccoz := hy
      teichmuller := hT
      boundedType := hB
      antiMolecule := hA
      neutral := hN
      quadraticGrowth := hQ
      unboundedTeichmuller := hTC
      unboundedJumpCap := LG.unboundedJumpCap hGc
      unboundedDichotomy := LG.unboundedDichotomy hDs
      virtualJulia := hVJ
      virtualTeichmuller := hVT1
      virtualDichotomy := hVD1
      virtualJumpCap := LG.virtualJumpCap hVGc
      virtualLinearDichotomy := LG.virtualLinearDichotomy hVDs
      virtualTransfer := hVT }

end MLC
