# PLAN 07: Eliminate `problem43_pseudoSiegelAPrioriBounds`

**Status:** PARTIALLY EXECUTED  
**Difficulty:** Very High  
**Goal:** Remove `MLC.problem43_pseudoSiegelAPrioriBounds` from the checked root
frontier without introducing any replacement axioms.

---

## Current Frontier Context

The checked root frontier is now:

- `problem44_virtualMolecule`
- `problem45_virtualNearMoleculeRenormalization`

The finite-branch seam has already been removed, and the root-facing Problem 4.3
axiom has now also been removed by strengthening the Problem 4.5 seam to carry
the direct satellite local-connectivity payload. The remaining constructive work
is to theoremize that stronger Problem 4.5 bridge and, if desired, recover a
separate theorem-level Problem 4.3 package underneath it.

This means the current implementation has followed the plan's **fallback direct
satellite-local-connectivity route** rather than the canonical lower-bound route.

At the current Lean interface:

```lean
def Problem43PseudoSiegelAPrioriBoundsData : Prop :=
  MoleculeBridgeTarget.MoleculeImpliesUniformConformalLowerBoundTarget
```

So eliminating Problem 4.3 means theoremizing the current
`MoleculeImpliesUniformConformalLowerBoundTarget` interface, or replacing its
use by a strictly stronger theoremizable bridge with **no new axioms**.

---

## What the Current Code Really Says

The Problem 4.3 seam is currently implemented through the chain:

```lean
Problem43PseudoSiegelAPrioriBoundsData
  = MoleculeImpliesUniformConformalLowerBoundTarget
  = MoleculeUniformConformalLowerBoundData
```

and then used via:

```lean
satelliteLC_of_problem43_problem45 :
  Problem43PseudoSiegelAPrioriBoundsData →
  Problem45VirtualNearMoleculeRenormalizationData →
  VirtualJuliaSatelliteLocalConnectivityData
```

So the real formal target is:

> from Molecule input and a satellite tower on `c ∈ MandelbrotSet`, produce a
> **uniform positive lower bound** on the conformal moduli of the canonical
> principal-nest annuli selected by the tower.

This is the current formal proxy for pseudo-Siegel a priori bounds in the
remaining unbounded satellite ql cases.

---

## Main Research Finding

The current Problem 4.3 interface is **structurally entangled** with the
Gaussian proxy modulus layer.

Relevant files:

- `Mlc/MoleculeConjectureBridge.lean`
- `Mlc/MoleculeToParameterShrink.lean`
- `Mlc/MoleculeToSatelliteNestData.lean`
- `Mlc/FastTowerExistenceObstruction.lean`

The obstruction is explicit:

1. `Problem43PseudoSiegelAPrioriBoundsData` is a **uniform conformal lower bound**
   target on canonical principal-nest annuli.
2. Under the current proxy model, `cmodulus` and `modulus` are still tied to the
   Gaussian summability framework.
3. `FastTowerExistenceObstruction.lean` proves that such a uniform lower bound
   refutes the existence of Mandelbrot satellite towers in the current model.

So:

> **Problem 4.3 cannot be eliminated by a local proof patch inside the current
> modulus proxy layer.**

The modulus interface itself must first be revised or bypassed.

---

## Revised Elimination Strategy

### Phase A: Decouple Problem 4.3 from the Gaussian proxy obstruction

Goal:

- stop treating the current Gaussian `cmodulus`/`modulus` layer as the final
  home of pseudo-Siegel a priori bounds
- isolate which statements are:
  1. genuine mathematical Problem 4.3 targets
  2. temporary proxy artifacts used by the current inconsistency / tower
     machinery

Files:

- `Mlc/MoleculeConjectureBridge.lean`
- `Mlc/MoleculeToParameterShrink.lean`
- `Mlc/FastTowerExistenceObstruction.lean`
- `Mlc/MainConjecture.lean`

Deliverable:

- a clean bridge statement for Problem 4.3 that is not definitionally
  inconsistent with the Gaussian proxy architecture

### Phase B: Choose the constructive bridge target

There are two realistic theoremization routes:

1. **Canonical principal-nest data route**
   - prove a stronger theorem:
     `MoleculeImpliesCanonicalSatellitePrincipalNestData`
   - then derive the uniform lower bound as a corollary
   - then discharge Problem 4.3 from that corollary

2. **Direct satellite-local-connectivity route**
   - prove a theorem directly strong enough to replace the use of
     `Problem43PseudoSiegelAPrioriBoundsData` inside
     `satelliteLC_of_problem43_problem45`
   - this would bypass the current lower-bound interface rather than
     theoremizing it literally

Preference:

- start with **(1)**, because the code already contains the canonical-depth
  bridge scaffolding in `MoleculeToSatelliteNestData.lean`
- keep **(2)** as a fallback if the lower-bound interface remains too tied to the
  proxy modulus layer

### Phase C: Problem 4.3 research program

The mathematical work should be organized around the following chain:

1. **Canonical satellite depth schedule**
   - use `depthsFromSatelliteTower`
   - identify the exact annuli that correspond to the remaining unbounded
     satellite ql cases

2. **Pseudo-Siegel control package**
   - formalize the a priori geometric control needed in those cases
   - localize it to the tower-selected principal annuli rather than to a global
     placeholder modulus statement

3. **Uniform conformal lower bound**
   - prove a positive lower bound on conformal modulus for each canonical annulus
   - then upgrade pointwise control to a uniform lower bound `μ > 0`

4. **Bridge to satellite LC**
   - feed that lower bound into the existing Problem 4.5 bridge
   - remove the root-facing Problem 4.3 axiom

---

## Concrete File-Level Program

### Step 1: Audit and refactor the bridge types

Files:

- `Mlc/MoleculeConjectureBridge.lean`
- `Mlc/MoleculeToParameterShrink.lean`
- `Mlc/MoleculeToSatelliteNestData.lean`
- `Mlc/FastTowerExistenceObstruction.lean`

Task:

- identify exactly which equivalences or reuse lemmas force Problem 4.3 into the
  Gaussian obstruction
- split “real conformal target” from “current proxy target” if necessary

### Step 2: Strengthen the canonical-depth theorem route

Files:

- `Mlc/MoleculeToSatelliteNestData.lean`
- `Mlc/SatellitePrincipalNestData.lean`
- any upstream Molecule-facing bridge files

Task:

- make `MoleculeImpliesCanonicalSatellitePrincipalNestData` the primary target
- derive the Problem 4.3 lower-bound interface from it, rather than taking the
  lower bound as the primitive theorem

### Step 3: Integrate at the root

Files:

- `Mlc/MainConjecture.lean`
- `check_axioms.lean`
- `README.md`

Task:

- replace `problem43_pseudoSiegelAPrioriBounds` by a theorem
- preserve the exact frontier discipline: no new axioms, only Problems 4.4 / 4.5
  remain

---

## Success Criterion

This plan is complete when:

1. `problem43_pseudoSiegelAPrioriBounds` disappears from the output of
   `make check`
2. no new project-level axioms are introduced
3. `make build`, `make check`, and `scripts/verify_output.sh` pass
4. the README explains the new post-Problem-4.3 frontier precisely
