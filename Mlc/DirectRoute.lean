import Mlc.MainConjecture

/-!
# Direct MLC Proof Route (Bypassing `external_ray_map_exists`)

This file provides infrastructure for proving `mlc_conjecture` via the
strategy decomposition (`mlc_strategy_of_branchLocalData`), bypassing the
vacuous `False.elim` chain through `BottcherSurjOnExterior(2)`.

## Architecture

The direct route needs three components:
1. **FR branch**: `PuzzleBoundaryMotionHyp` (or equivalently, puzzle piece
   connectivity on M)
2. **IR classification**: `IRClassificationData`
3. **Satellite bridge**: `MoleculeConjectureRefined` → satellite LC

## Current status

  (proved in this file). Both reduce to:
  `∀ c ∈ M, ∀ n, IsConnected (ParaPuzzlePieceAt c n ∩ M)`
- This connectivity still has an axiom-backed local provider
  (`para_puzzle_piece_inter_mandelbrot_connected`), but after the genuine
  Böttcher root cutover it is no longer on the checked root frontier for
  `MLC.mlc_conjecture`.
- The IR branch components are also unproved.
-/

namespace MLC

open Quadratic Complex Topology Set

noncomputable section

/-! ### Equivalence: `PuzzleBoundaryMotionHyp` ↔ connectivity axiom

The `motion_preserves_para_piece` predicate has phantom parameters
(`_r`, `E`, `_h`) that are unused. So `PuzzleBoundaryMotionHyp` is
logically equivalent to the connectivity of `ParaPuzzlePieceAt c n ∩ M`.
-/

/-- `PuzzleBoundaryMotionHyp` follows from the connectivity of puzzle piece
    intersections with M. The holomorphic motion parameters are phantom. -/
theorem puzzleBoundaryMotionHyp_of_connected
    (h_conn : ParaPuzzlePieceInterMandelbrotConnectedData) :
    PuzzleBoundaryMotionHyp :=
  Quadratic.puzzleBoundaryMotionHyp_of_connected_data h_conn

/-- Conversely, `PuzzleBoundaryMotionHyp` implies the connectivity condition. -/
theorem connected_of_puzzleBoundaryMotionHyp
    (h_motion : PuzzleBoundaryMotionHyp) :
    ParaPuzzlePieceInterMandelbrotConnectedData := by
  intro c hc n
  exact finite_connectedAt_provider_of_motionHyp h_motion c hc n

/-- `PuzzleBoundaryMotionHyp` is equivalent to puzzle piece connectivity on M. -/
theorem puzzleBoundaryMotionHyp_iff_connected :
    PuzzleBoundaryMotionHyp ↔ ParaPuzzlePieceInterMandelbrotConnectedData :=
  ⟨connected_of_puzzleBoundaryMotionHyp, puzzleBoundaryMotionHyp_of_connected⟩

/-! ### Direct proof skeleton

Wire `mlc_conjecture` through the real mathematical route.
This makes the remaining gaps explicit.
-/

/-! ### Simplified reduction

The legacy direct seam route uses two axioms:
1. `para_puzzle_piece_inter_mandelbrot_connected` (FR branch)
2. `ir_locally_connected_seam` (IR branch)

The `DirectMLCData` structure below shows the finer three-component
decomposition of the IR branch, which `ir_locally_connected_seam` subsumes.
The checked root now bypasses this route through the genuine Böttcher kernel.
-/

/-- The three components needed for the direct proof of MLC (fine-grained). -/
structure DirectMLCData : Prop where
  /-- For all c ∈ M and all n, the parameter puzzle piece at c intersected
      with M is connected. -/
  puzzle_connected : ParaPuzzlePieceInterMandelbrotConnectedData
  /-- Every infinitely renormalizable parameter in M is either primitive
      or a satellite tower. -/
  ir_classification : IRClassificationData
  /-- The molecule conjecture implies LC at satellite tower parameters. -/
  satellite_bridge :
    MoleculeConjectureRefined →
    ∀ (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet)
      (_h : SatelliteRenormalizableTower c),
      MLC.LocallyConnectedAt MLC.Quadratic.MandelbrotSet ⟨c, hc⟩

/-- Characterization of fine-grained direct-route payload. -/
theorem directMLCData_iff :
    DirectMLCData ↔
      ParaPuzzlePieceInterMandelbrotConnectedData ∧ IRClassifyBridgeData := by
  constructor
  · intro h
    exact ⟨h.puzzle_connected,
      irClassifyBridgeData_of_classify_bridge_data h.ir_classification h.satellite_bridge⟩
  · intro h
    exact
      { puzzle_connected := h.1
        ir_classification := h.2.classify
        satellite_bridge := h.2.bridge }

/-- Packaged direct-route payload alias: FR connectedness + packaged IR
    classify/bridge data. -/
abbrev DirectMLCPackagedData : Prop := MLCClassifyBridgeSeamData

/-- Packaged direct-route payload using boundary-motion finite-branch data
    and packaged IR classify/bridge data. -/
structure DirectMotionIRPackagedData : Prop where
  motion : PuzzleBoundaryMotionHyp
  ir : IRClassifyBridgeData

/-- Characterization of motion-based packaged direct-route payload. -/
theorem directMotionIRPackagedData_iff :
    DirectMotionIRPackagedData ↔ PuzzleBoundaryMotionHyp ∧ IRClassifyBridgeData := by
  constructor
  · intro h
    exact ⟨h.motion, h.ir⟩
  · intro h
    exact ⟨h.1, h.2⟩

/-- Extract packaged IR classify/bridge payload from `DirectMLCData`. -/
def irClassifyBridgeData_of_directMLCData
    (h : DirectMLCData) :
    IRClassifyBridgeData :=
  irClassifyBridgeData_of_classify_bridge_data
    h.ir_classification
    h.satellite_bridge

/-- Convert fine-grained direct-route data to the packaged payload. -/
def directMLCPackagedData_of_directMLCData
    (h : DirectMLCData) :
    DirectMLCPackagedData :=
  mlcClassifyBridgeSeamData_of_paraPuzzleConnectedData_irClassifyBridgeData
    h.puzzle_connected
    (irClassifyBridgeData_of_directMLCData h)

/-- Convert motion-based packaged direct-route data to the canonical packaged
    seam payload. -/
def directMLCPackagedData_of_directMotionIRPackagedData
    (h : DirectMotionIRPackagedData) :
    DirectMLCPackagedData :=
  mlcClassifyBridgeSeamData_of_motionHyp_irClassifyBridgeData
    h.motion
    h.ir

/-- Convert canonical packaged seam payload to motion-based packaged direct-route
    data. -/
def directMotionIRPackagedData_of_directMLCPackagedData
    (h : DirectMLCPackagedData) :
    DirectMotionIRPackagedData where
  motion := puzzleBoundaryMotionHyp_of_connected h.puzzle_connected
  ir := h.ir

/-- Convert fine-grained direct-route data to motion-based packaged payload. -/
def directMotionIRPackagedData_of_directMLCData
    (h : DirectMLCData) :
    DirectMotionIRPackagedData where
  motion := puzzleBoundaryMotionHyp_of_connected h.puzzle_connected
  ir := irClassifyBridgeData_of_directMLCData h

/-- Motion-based and canonical packaged direct-route payloads are equivalent. -/
theorem directMotionIRPackagedData_iff_directMLCPackagedData :
    DirectMotionIRPackagedData ↔ DirectMLCPackagedData := by
  constructor
  · intro h
    exact directMLCPackagedData_of_directMotionIRPackagedData h
  · intro h
    exact directMotionIRPackagedData_of_directMLCPackagedData h

/-- Convert packaged direct-route data back to fine-grained data. -/
def directMLCData_of_directMLCPackagedData
    (h : DirectMLCPackagedData) :
    DirectMLCData where
  puzzle_connected := h.puzzle_connected
  ir_classification := h.ir.classify
  satellite_bridge := h.ir.bridge

/-- Fine-grained and packaged direct-route payloads are equivalent. -/
theorem directMLCPackagedData_iff_directMLCData :
    DirectMLCPackagedData ↔ DirectMLCData := by
  constructor
  · intro h
    exact directMLCData_of_directMLCPackagedData h
  · intro h
    exact directMLCPackagedData_of_directMLCData h

/-- Motion-based packaged and fine-grained direct-route payloads are
    equivalent. -/
theorem directMotionIRPackagedData_iff_directMLCData :
    DirectMotionIRPackagedData ↔ DirectMLCData := by
  constructor
  · intro h
    exact directMLCData_of_directMLCPackagedData
      (directMLCPackagedData_of_directMotionIRPackagedData h)
  · intro h
    exact directMotionIRPackagedData_of_directMLCData h

/-- MLC follows from `DirectMLCPackagedData`. -/
theorem mlc_conjecture_of_directMLCPackagedData
    (h : DirectMLCPackagedData) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_MLCClassifyBridgeSeamData h

/-- MLC follows from motion-based packaged direct-route data. -/
theorem mlc_conjecture_of_directMotionIRPackagedData
    (h : DirectMotionIRPackagedData) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_directMLCPackagedData
    (directMLCPackagedData_of_directMotionIRPackagedData h)

/-- MLC follows from `DirectMLCData` — no axioms beyond core needed. -/
theorem mlc_conjecture_of_directMLCData
    (h : DirectMLCData) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_directMotionIRPackagedData
    (directMotionIRPackagedData_of_directMLCData h)

/-! ### Non-motion bridge wrappers

These wrappers expose the IR/tower bridge routes from `MainConjecture` through
the direct-route API surface.
-/

/-- Direct-route wrapper: one renormalization tower implies MLC. -/
theorem mlc_conjecture_of_directTower {c₀ : ℂ}
    (T : RenormalizationTower (parameterToBMol c₀)) :
    LocallyConnectedSpace mandelbrotSet :=
  mlc_conjecture_of_tower T

/-- Direct-route wrapper: existence of one renormalization tower implies MLC. -/
theorem mlc_conjecture_of_directExistsTower
    (h_exists : ∃ c₀ : ℂ, Nonempty (RenormalizationTower (parameterToBMol c₀))) :
    LocallyConnectedSpace mandelbrotSet :=
  mlc_conjecture_of_exists_tower h_exists

/-- Direct-route wrapper: Molecule fixed-point hypotheses plus fixed-point
    parameter lift data imply MLC. -/
theorem mlc_conjecture_of_directMoleculeRenormalizableFixedPointData
    (h_mol : MoleculeRenormalizableFixedPointData)
    (h_lift : ParameterToBMolFixedPointLiftData) :
    LocallyConnectedSpace mandelbrotSet :=
  mlc_conjecture_of_moleculeRenormalizableFixedPointData h_mol h_lift

/-- Direct-route wrapper: model-data variant of the Molecule fixed-point
    bridge. -/
theorem mlc_conjecture_of_directMoleculeRenormalizableFixedPointDataOfFixedPointParameterModelData
    (h_mol : MoleculeRenormalizableFixedPointData)
    (h_model : FixedPointParameterModelData) :
    LocallyConnectedSpace mandelbrotSet :=
  mlc_conjecture_of_moleculeRenormalizableFixedPointData_of_fixedPointParameterModelData
    h_mol h_model

/-- Direct-route wrapper: existence of a parameter-level fast-renormalizable
    fixed point of `Rfast` implies MLC. -/
theorem mlc_conjecture_of_directExistsParameterRfastFixedPoint
    (h_exists :
      ∃ c : ℂ, Molecule.IsFastRenormalizable (parameterToBMol c) ∧
        Molecule.Rfast (parameterToBMol c) = parameterToBMol c) :
    LocallyConnectedSpace mandelbrotSet :=
  mlc_conjecture_of_exists_parameter_rfast_fixed_point h_exists

/-- Direct-route wrapper: existence of a satellite renormalization tower
    implies MLC. -/
theorem mlc_conjecture_of_directExistsSatelliteTower
    (h_exists : ∃ c : ℂ, SatelliteRenormalizableTower c) :
    LocallyConnectedSpace mandelbrotSet :=
  mlc_conjecture_of_exists_satellite_tower h_exists

/-- Direct-route wrapper: explicit IR classification with the strong molecule
    bridge target implies MLC. -/
theorem mlc_conjecture_of_directClassifyMoleculeBridgeTargetData
    (h_classify_ir : IRClassificationData)
    (h_target : MoleculeBridgeTarget.MoleculeImpliesSatellitePrincipalNestData) :
    LocallyConnectedSpace mandelbrotSet :=
  mlc_conjecture_of_classify_moleculeBridgeTarget_data h_classify_ir h_target

/-- Direct-route wrapper: explicit IR classification with the uniform conformal
    molecule bridge target implies MLC. -/
theorem mlc_conjecture_of_directClassifyMoleculeUniformBridgeTargetData
    (h_classify_ir : IRClassificationData)
    (h_uniform : MoleculeBridgeTarget.MoleculeImpliesUniformConformalLowerBoundTarget) :
    LocallyConnectedSpace mandelbrotSet :=
  mlc_conjecture_of_classify_moleculeUniformBridgeTarget_data h_classify_ir h_uniform

/-- Direct-route wrapper: global IR→tower bridge data with the strong molecule
    bridge target implies MLC. -/
theorem mlc_conjecture_of_directInfinitelyRenormalizableHasTowerDataMoleculeBridgeTarget
    (h_tower_data : InfinitelyRenormalizableHasTowerData)
    (h_target : MoleculeBridgeTarget.MoleculeImpliesSatellitePrincipalNestData) :
    LocallyConnectedSpace mandelbrotSet :=
  mlc_conjecture_of_infinitelyRenormalizableHasTowerData_moleculeBridgeTarget
    h_tower_data h_target

/-- Direct-route wrapper: global IR→tower bridge data with the uniform
    conformal molecule bridge target implies MLC. -/
theorem mlc_conjecture_of_directInfinitelyRenormalizableHasTowerDataMoleculeUniformBridgeTarget
    (h_tower_data : InfinitelyRenormalizableHasTowerData)
    (h_uniform : MoleculeBridgeTarget.MoleculeImpliesUniformConformalLowerBoundTarget) :
    LocallyConnectedSpace mandelbrotSet :=
  mlc_conjecture_of_infinitelyRenormalizableHasTowerData_moleculeUniformBridgeTarget
    h_tower_data h_uniform

end

end MLC
