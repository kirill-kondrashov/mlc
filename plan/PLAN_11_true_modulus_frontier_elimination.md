# PLAN 11: Eliminate the true-modulus primitive frontier

**Status:** NEW  
**Difficulty:** Extremely High  
**Goal:** Remove the root-facing true-modulus primitive axioms:

- `MLC.chosenTrueConformalModulusData`
- `MLC.primitiveFeigenbaumTypewiseRealBoundsAxiom`
- `MLC.chosenTruePrimitiveFeigenbaumTypewiseGrotzschPromotionAxiom`
- `MLC.chosenTruePrimitiveFeigenbaumAffineNormalizationComparisonAxiom`
- `MLC.chosenTruePrimitiveEventualBridgeAxiom`

---

## Current Shape

The root currently uses the following chain:

```text
chosen true modulus handle
-> type-wise real bounds
-> type-wise Grötzsch promotion
-> affine normalization comparison
-> chosen true eventual lower bound
-> legacy bridge
-> bounded-type constructive cutover
```

This is now a good theorem graph, but it is still axiom-backed at every
nontrivial analytic step.

---

## Subproblems

### 1. Concrete true conformal modulus

Replace:

```lean
chosenTrueConformalModulusData : TrueConformalModulusData
```

with either:

- a concrete `AnnulusConformalModulusAPI` instance built from existing analytic
  infrastructure, or
- a theorem importing such an instance from an upstream package.

### 2. Type-wise real bounds

Prove:

```lean
PrimitiveFeigenbaumTypewiseRealBoundsGlobalData
```

from bounded primitive combinatorics.

This is the Step-2 theorem that should extract type-wise gap-ratio constants
`C_τ`.

### 3. Type-wise Grötzsch promotion

Prove:

```lean
PrimitiveFeigenbaumTypewiseGrotzschPromotionGlobalData μApi
```

from the true conformal modulus API plus a general Teichmüller / Grötzsch lower
bound theorem.

This is the Step-3 theorem that defines `ε_τ := Ψ(C_τ)`.

### 4. Affine normalization comparison

Eliminate:

```lean
PrimitiveFeigenbaumTrueAffineNormalizationComparisonGlobalData
```

by proving the principal-nest / renormalized-fundamental-annulus identification
constructively from `RenormalizationTowerNormalizationData`.

### 5. Legacy bridge elimination

Remove:

```lean
ChosenTrueToLegacyPrimitiveEventualBridgeData
```

by either:

- proving the bridge theorem directly, or
- migrating the remaining legacy consumer path off Gaussian-facing
`EventualPrimitiveModulusLowerBoundData`.

---

## Preferred Implementation Order

1. true modulus instance
2. affine comparison
3. type-wise real bounds
4. type-wise Grötzsch promotion
5. legacy bridge elimination

The first four make the new route constructive; the fifth removes the last
compatibility shim.

---

## Success Criterion

All five true-modulus primitive axioms disappear from `check_axioms`.

