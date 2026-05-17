# PLAN 10: Eliminate the remaining root frontier after the true-modulus cutover

**Status:** NEW  
**Difficulty:** Extremely High  
**Goal:** Remove all project axioms from `MLC.mlc_conjecture` until only built-in
Lean axioms remain.

---

## Current Root Frontier

The checked root frontier is now:

- `MLC.Quadratic.para_puzzle_piece_inter_mandelbrot_connected`
- `MLC.chosenTrueConformalModulusData`
- `MLC.primitiveFeigenbaumTypewiseRealBoundsAxiom`
- `MLC.chosenTruePrimitiveFeigenbaumTypewiseGrotzschPromotionAxiom`
- `MLC.chosenTruePrimitiveFeigenbaumAffineNormalizationComparisonAxiom`
- `MLC.chosenTruePrimitiveEventualBridgeAxiom`
- `MLC.feigenbaumConstructiveBoundedTypeProblem45Axiom`
- `MLC.residualOpenVirtualNearMoleculeAxiom`

This is an intentional **graph-exposing cutover**: the root now passes through
the latest primitive Feigenbaum / true-modulus route instead of hiding behind the
old monolithic Problem 4.5 axiom.

---

## Strategic Decomposition

The frontier naturally splits into three blocks:

1. **True-modulus primitive block**
   - `chosenTrueConformalModulusData`
   - `primitiveFeigenbaumTypewiseRealBoundsAxiom`
   - `chosenTruePrimitiveFeigenbaumTypewiseGrotzschPromotionAxiom`
   - `chosenTruePrimitiveFeigenbaumAffineNormalizationComparisonAxiom`
   - `chosenTruePrimitiveEventualBridgeAxiom`
2. **Bounded-type constructive classification block**
   - `feigenbaumConstructiveBoundedTypeProblem45Axiom`
3. **Residual open seam**
   - `residualOpenVirtualNearMoleculeAxiom`
4. **Para-puzzle finite-branch seam**
   - `Quadratic.para_puzzle_piece_inter_mandelbrot_connected`

The elimination order should follow the dependency graph:

1. eliminate the true-modulus primitive block,
2. use that to eliminate the bounded-type constructive axiom,
3. isolate or reduce the residual open seam,
4. separately eliminate the para-puzzle connectedness seam,
5. rerun `check_axioms` after each cutover.

---

## Concrete Execution Order

### Phase A. Remove the true-modulus primitive block

Target the five axioms as one theoremization program rather than five unrelated
cleanup tasks.

Deliverables:

- a concrete `AnnulusConformalModulusAPI` instance or a theorem importing one;
- constructive proofs of:
  - `PrimitiveFeigenbaumTypewiseRealBoundsGlobalData`
  - `PrimitiveFeigenbaumTypewiseGrotzschPromotionGlobalData`
  - `PrimitiveFeigenbaumTrueAffineNormalizationComparisonGlobalData`
  - `ChosenTrueToLegacyPrimitiveEventualBridgeData`

Success criterion:

- the root no longer depends on any `chosenTrue*` axiom.

### Phase B. Eliminate the bounded-type constructive axiom

Use the completed true-modulus route to prove:

```lean
FeigenbaumConstructiveBoundedTypeProblem45Data
```

constructively, rather than postulating it at the root.

Success criterion:

- `feigenbaumConstructiveBoundedTypeProblem45Axiom` disappears from
  `check_axioms`.

### Phase C. Reduce the residual open seam

Split

```lean
ResidualOpenVirtualNearMoleculeData
```

into its two real mathematical constituents and treat them independently:

- Problem 4.3: unbounded satellite ql / pseudo-Siegel bounds
- Problem 4.4: virtual Molecule interpolation / no-tower primitive route

Success criterion:

- either the residual seam is removed entirely,
- or it is reduced to a smaller, more faithful pair of theorem surfaces that can
  be attacked independently.

### Phase D. Eliminate the para-puzzle connectedness seam

The root now additionally exposes

```lean
Quadratic.para_puzzle_piece_inter_mandelbrot_connected
```

as a genuine project-level blocker. This needs its own focused proof plan.

Success criterion:

- the only remaining axioms in `check_axioms` are built-in Lean axioms.

---

## Files to Drive

- `Mlc/MainConjecture.lean`
- `Mlc/PrimitiveModulusDivergence.lean`
- `Mlc/Quadratic/Complex/ConformalGroetzsch.lean`
- `Mlc/RenormalizationTypes.lean`
- `Mlc/MoleculeRenormalizationTower.lean`
- `Mlc/MoleculeToSatelliteNestData.lean`
- `Mlc/Quadratic/Complex/ParaPuzzle*.lean`
- `README.md`
- `check_axioms.lean`

---

## Exit Condition

This plan is complete only when:

```text
project_frontier(MLC.mlc_conjecture) = {}
```

so that `MLC.mlc_conjecture` depends only on built-in Lean axioms.

