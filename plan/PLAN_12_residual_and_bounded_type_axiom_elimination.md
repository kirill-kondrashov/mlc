# PLAN 12: Eliminate the bounded-type constructive axiom and residual open seam

**Status:** NEW  
**Difficulty:** Extremely High  
**Goal:** Remove:

- `MLC.feigenbaumConstructiveBoundedTypeProblem45Axiom`
- `MLC.residualOpenVirtualNearMoleculeAxiom`

from the root frontier.

---

## Current Shape

The root now rebuilds the old Problem 4.5 payload by combining:

1. the bounded-type constructive slice from the true-modulus primitive route,
2. the residual open seam:
   ```lean
   ResidualOpenVirtualNearMoleculeData
   = Problem43PseudoSiegelAPrioriBoundsData ∧ Problem44VirtualMoleculeData
   ```

This is mathematically cleaner than the old monolithic Problem 4.5 axiom, but it
still leaves two project-level seams.

---

## Track A: Feigenbaum constructive bounded-type cutover

Target:

```lean
FeigenbaumConstructiveBoundedTypeProblem45Data
```

Needed ingredients:

- a constructive provider of
  `FeigenbaumConstructiveBoundedTypeIRClassificationData`
- a constructive provider of
  `BoundedTypeVirtualJuliaSatelliteLocalConnectivityData`

The primitive side is now explicitly routed through the true-modulus Feigenbaum
program; the satellite side should be handled by the bounded-type portion of the
virtual Julia / Molecule bridge machinery.

---

## Track B: Residual open seam split

Split the residual seam into independent theorem programs:

### Problem 4.3

Target:

```lean
Problem43PseudoSiegelAPrioriBoundsData
```

Current formal proxy:

```lean
MoleculeBridgeTarget.MoleculeImpliesUniformConformalLowerBoundTarget
```

Needed work:

- theoremize the unbounded satellite ql / pseudo-Siegel regime,
- preferably through a true-modulus or canonical principal-nest target rather
  than reviving Gaussian-proxy obstructions.

### Problem 4.4

Target:

```lean
Problem44VirtualMoleculeData
```

Current formal proxy:

```lean
IRNoTowerImpliesPrimitiveData
```

Needed work:

- theoremize the virtual Molecule interpolation regime,
- derive either direct `IRClassificationData` or at least the Track-1 no-tower
  primitive theorem constructively.

---

## Preferred Elimination Order

1. finish the bounded-type constructive axiom first,
2. then split the residual seam,
3. then eliminate Problem 4.4 if possible before Problem 4.3,
4. finally reassemble the root with no residual seam.

Reason:

- the bounded-type constructive slice now has the best formal infrastructure;
- Problem 4.4 is more interface-local than Problem 4.3;
- Problem 4.3 remains the most likely genuinely hard analytic residue.

---

## Success Criterion

Both `feigenbaumConstructiveBoundedTypeProblem45Axiom` and
`residualOpenVirtualNearMoleculeAxiom` disappear from `check_axioms`.

