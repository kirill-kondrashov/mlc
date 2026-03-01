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

- `PuzzleBoundaryMotionHyp` is equivalent to `ParaPuzzlePieceInterMandelbrotConnectedData`
  (proved in this file). Both reduce to:
  `∀ c ∈ M, ∀ n, IsConnected (ParaPuzzlePieceAt c n ∩ M)`
- This connectivity is currently an axiom (`para_puzzle_piece_inter_mandelbrot_connected`).
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

The actual `mlc_conjecture` proof uses two axioms:
1. `para_puzzle_piece_inter_mandelbrot_connected` (FR branch)
2. `ir_locally_connected_seam` (IR branch)

The `DirectMLCData` structure below shows the finer three-component
decomposition of the IR branch, which `ir_locally_connected_seam` subsumes.
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

/-- Packaged direct-route payload alias: FR connectedness + packaged IR
    classify/bridge data. -/
abbrev DirectMLCPackagedData : Prop := MLCClassifyBridgeSeamData

/-- Minimal direct-route payload alias: FR connectedness + IR local-connectivity
    seam. -/
abbrev DirectMLCMinimalData : Prop := MLCSeamData

/-- Convert fine-grained direct-route data to the minimal seam payload. -/
def directMLCMinimalData_of_directMLCData
    (h : DirectMLCData) :
    DirectMLCMinimalData :=
  mlcSeamData_of_paraPuzzleConnectedData_irClassifyBridgeData
    h.puzzle_connected
    (irClassifyBridgeData_of_classify_bridge_data
      h.ir_classification
      h.satellite_bridge)

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

/-- MLC follows from `DirectMLCMinimalData`. -/
theorem mlc_conjecture_of_directMLCMinimalData
    (h : DirectMLCMinimalData) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_MLCSeamData h

/-- MLC follows from `DirectMLCPackagedData`. -/
theorem mlc_conjecture_of_directMLCPackagedData
    (h : DirectMLCPackagedData) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_MLCClassifyBridgeSeamData h

/-- MLC follows from `DirectMLCData` — no axioms beyond core needed. -/
theorem mlc_conjecture_of_directMLCData
    (h : DirectMLCData) :
    LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_directMLCPackagedData
    (directMLCPackagedData_of_directMLCData h)

end

end MLC
