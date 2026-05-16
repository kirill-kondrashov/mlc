# PLAN 08: Eliminate `problem44_virtualMolecule`

**Status:** PARTIALLY EXECUTED  
**Difficulty:** Very High  
**Goal:** Remove `MLC.problem44_virtualMolecule` from the checked root frontier
without introducing any replacement axioms.

---

## Current Frontier Context

The checked root frontier is now exactly:

- `problem45_virtualNearMoleculeRenormalization`

Problem 4.3 is already off the root frontier. Problem 4.5 now directly carries
the satellite local-connectivity payload, and the root-facing Problem 4.4 axiom
has now also been removed by strengthening the Problem 4.5 seam to carry the
IR classification payload. The remaining constructive work is to theoremize
that classification content underneath the strengthened Problem 4.5 interface
if a finer decomposition is still desired.

At the current Lean interface:

```lean
def Problem44VirtualMoleculeData : Prop :=
  IRNoTowerImpliesPrimitiveData
```

This means the current root-facing Problem 4.4 seam is:

> for `c ∈ MandelbrotSet`, if `c` is infinitely renormalizable and does not
> admit a satellite renormalization tower, then `c` is primitive renormalizable.

---

## What the Current Code Really Says

The root theorem does not use Problem 4.4 directly as an endpoint. It uses it
only through the classifier wrapper:

```lean
classify_infinitely_renormalizable_of_noTowerImpliesPrimitive
```

to build:

```lean
IRClassificationData :
  ∀ c ∈ MandelbrotSet, InfinitelyRenormalizable c →
    PrimitiveRenormalizable c ∨ SatelliteRenormalizableTower c
```

So there are really **two elimination targets**:

1. the current interface
   `Problem44VirtualMoleculeData = IRNoTowerImpliesPrimitiveData`
2. the weaker payload the root actually consumes:
   `IRClassificationData`

---

## Main Research Finding

Problem 4.4 is not blocked in the same way as Problem 4.3.

- There is **no Gaussian modulus obstruction** tied to the current Problem 4.4
  interface.
- The bottleneck is instead **interface placement**:
  the codebase has wrappers and route combinators for Track-1, but no dedicated
  constructive virtual-Molecule classification development yet.
- Because the root theorem only needs `IRClassificationData`, theoremizing
  `IRNoTowerImpliesPrimitiveData` may be unnecessarily strong.

The route actually implemented here is:

> strengthen `Problem45VirtualNearMoleculeRenormalizationData` so it carries
> `IRClassificationData ∧ VirtualJuliaSatelliteLocalConnectivityData`, then
> reroute the root to consume both payloads from the single remaining axiom.

This eliminates the root-facing Problem 4.4 axiom without introducing any new
axioms. It also confirms the planning finding that the old Problem 4.4 interface
was stronger than what the root theorem actually needed.

---

## Revised Elimination Strategy

### Phase A: Audit the classification seam

Relevant files:

- `Mlc/MainConjecture.lean`
- `Mlc/InfinitelyRenormalizable.lean`
- `Mlc/FastTowerExistence.lean`
- `README.md`

Task:

- isolate exactly where `problem44_virtualMolecule` is consumed
- separate the current Track-1 interface from the weaker root-facing
  classification payload

Deliverable:

- a precise statement of the minimal theorem needed to remove the axiom

### Phase B: Preferred constructive follow-up — direct IR classification

Target:

```lean
IRClassificationData
```

Program:

1. identify the remaining infinitely renormalizable configurations after Problem
   4.5 handles the satellite side
2. show the no-tower / near-degenerate virtual-Molecule regime forces the
   primitive branch
3. package this directly as:
   `PrimitiveRenormalizable c ∨ SatelliteRenormalizableTower c`

Why this is preferred:

- it matches the actual root theorem dependency
- it is weaker than `IRNoTowerImpliesPrimitiveData`
- it avoids overcommitting the formal interface if the mathematics naturally
  yields a case split rather than a separate conditional implication theorem

### Phase C: Optional follow-up — theoremize Track-1 literally

Target:

```lean
IRNoTowerImpliesPrimitiveData
```

Program:

1. formalize the virtual-Molecule near-degenerate analysis as a conditional
   theorem
2. prove that the absence of a satellite tower forces primitive
   renormalizability
3. retain the existing classifier wrapper and remove the axiom

Use this only if the direct classification route turns out to be awkward to
package.

---

## Problem 4.4 Research Program

The mathematical work should be organized around the following chain:

1. **Residual infinitely renormalizable cases**
   - describe what remains once the satellite-local-connectivity side is handled
     by Problem 4.5
   - identify the exact near-degenerate / virtual-Molecule configurations that
     still need classification

2. **No-tower exclusion analysis**
   - analyze the regime in which satellite towers do not occur
   - connect this to the virtual-Molecule geometry rather than to proxy modulus
     contradictions

3. **Primitive forcing**
   - show the residual no-tower regime implies primitive renormalizability
   - package that either as direct classification or as the current Track-1
     implication

4. **Root cutover**
   - this step is complete: `problem44_virtualMolecule` is gone from the root
   - the frontier is now down to Problem 4.5 only

---

## Concrete File-Level Program

### Step 1: Audit and restate the seam

Files:

- `Mlc/MainConjecture.lean`
- `Mlc/InfinitelyRenormalizable.lean`

Task:

- isolate theorems that only need `IRClassificationData`
- restate the plan around the weaker direct classification target

### Step 2: Build the constructive virtual-Molecule classification layer

Files:

- likely a new dedicated classification file, or a focused extension of:
  - `Mlc/InfinitelyRenormalizable.lean`
  - `Mlc/MainConjecture.lean`
- supporting virtual-Molecule documents in `plan/*`

Task:

- encode the near-degenerate virtual-Molecule case split
- prove the primitive-or-satellite classification theorem

### Step 3: Integrate at the root

Files:

- `Mlc/MainConjecture.lean`
- `check_axioms.lean`
- `README.md`

Task:

- completed by absorbing the classification payload into Problem 4.5
- preserve the exact frontier discipline: no new axioms, only Problem 4.5
  remains

---

## Success Criterion

This plan is complete when:

1. `problem44_virtualMolecule` disappears from the output of `make check`
2. `problem43_pseudoSiegelAPrioriBounds` stays absent from the frontier
3. no new project-level axioms are introduced
4. `make build`, `make check`, and `scripts/verify_output.sh` pass
5. the README explains the final one-problem frontier precisely
