# PLAN 09: Eliminate `problem45_virtualNearMoleculeRenormalization`

**Status:** PARTIALLY EXECUTED  
**Difficulty:** Extremely High  
**Goal:** Remove `MLC.problem45_virtualNearMoleculeRenormalization` from the
checked root frontier without introducing any replacement axioms.

---

## Current Frontier Context

The checked root frontier is now exactly:

- `problem45_virtualNearMoleculeRenormalization`

Problems 4.3 and 4.4 are already off the checked root frontier. The remaining
root-facing work is therefore entirely concentrated in the strengthened Problem
4.5 seam.

At the current Lean interface:

```lean
def Problem45VirtualNearMoleculeRenormalizationData : Prop :=
  IRClassificationData ∧ VirtualJuliaSatelliteLocalConnectivityData
```

So the current root-facing Problem 4.5 seam packages:

1. infinitely-renormalizable classification on `M`
2. satellite local connectivity on parameters with
   `SatelliteRenormalizableTower`

---

## What the Current Code Really Says

The root theorem uses Problem 4.5 only through:

```lean
irClassification_of_problem45
satelliteLC_of_problem45
```

to build:

```lean
IRClassifyBridgeData
```

and then immediately applies:

```lean
mlc_conjecture_of_irClassifyBridgeData
```

This means there are really **three possible elimination targets**:

1. theoremize the current strengthened pair
   `IRClassificationData ∧ VirtualJuliaSatelliteLocalConnectivityData`
2. theoremize the packaged payload
   `IRClassifyBridgeData`
3. theoremize the still-weaker endpoint
   `IRLocallyConnectedData`

Of these, the weakest root-sufficient target is `IRLocallyConnectedData`.

---

## Main Research Finding

There is a tempting but unacceptable shortcut:

- the code already has
  `mlc_conjecture_of_irLocallyConnectedData`
- and also an existing axiom-backed provider
  `ir_locally_connected_seam`

So one could reroute the root to `IRLocallyConnectedData` immediately.

However, that would **not eliminate project axioms**. It would merely swap the
remaining Problem 4.5 axiom for older hidden seam machinery:

- `ir_locally_connected_seam`
- the tower/inconsistency route
- and, through that route, the old bridge axioms such as
  `lyubich_conformal_bridge` and tower-existence bridge data

So:

> **Problem 4.5 cannot be considered eliminated by rerouting the root to the
> old IR seam.**

The final elimination must theoremize the remaining IR payload constructively,
not reactivate older axiom-backed infrastructure.

Concrete audit result from the current codebase:

1. Rerouting the root to `ir_locally_connected_seam` would reintroduce the
   explicit project axiom `ir_locally_connected_seam`.
2. Rerouting through `irLocallyConnectedData_of_tower` revives the
   inconsistency route and therefore depends on `lyubich_conformal_bridge`.
3. Producing the required tower via
   `exists_renormalization_tower_of_molecule_bridge_axioms` revives
   `molecule_renormalizable_fixed_point_data` and
   `fixedPoint_parameter_model_data`.

So the repository currently contains **no axiom-free implementation path** for
the remaining Problem 4.5 payload. The blocker is no longer just interface
placement; it is the absence of any constructive provider for the final IR
local-connectivity content.

---

## Revised Elimination Strategy

### Phase A: Isolate the true final target

Relevant files:

- `Mlc/MainConjecture.lean`
- `Mlc/InconsistencyRoute.lean`
- `Mlc/RenormalizationTowerExistence.lean`
- `Mlc/PrimitiveModulusDivergence.lean`

Task:

- separate the current strengthened Problem 4.5 interface from the weaker final
  target `IRLocallyConnectedData`
- distinguish theoremizable payloads from old axiom-backed shortcuts

Deliverable:

- a precise statement of the minimal final theorem needed to clear the root
  frontier without reviving older axioms

### Phase B: Preferred route — theoremize `IRLocallyConnectedData`

Target:

```lean
IRLocallyConnectedData
```

Program:

1. prove local connectivity directly for infinitely renormalizable Mandelbrot
   parameters from the virtual Julia / virtual near-Molecule program
2. avoid the old inconsistency route as a dependency
3. reroute the root theorem through `mlc_conjecture_of_irLocallyConnectedData`

Why this is preferred:

- it is weaker than the current strengthened Problem 4.5 pair
- it matches the actual endpoint used by the IR-only assembly
- it avoids carrying unnecessary intermediate packaging at the root

### Phase C: Fallback route — theoremize the strengthened Problem 4.5 pair

Target:

```lean
IRClassificationData ∧ VirtualJuliaSatelliteLocalConnectivityData
```

Program:

1. theoremize the classification payload constructively
2. theoremize the satellite local-connectivity payload constructively
3. retain the current root route and delete the axiom

Use this if the direct `IRLocallyConnectedData` theorem is awkward to package.

---

## Problem 4.5 Research Program

The mathematical work should be organized around the following chain:

1. **Primitive-first ql case decomposition**
   - formalize the virtual near-Molecule chain
     `M = M(0) ⊋ M(1) ⊋ ... ⊋ M(n+1)`
   - identify the exact data needed to control both classification and local
     connectivity in this regime

2. **Classification payload**
   - explain why the remaining infinitely renormalizable cases fall into the
     primitive-or-satellite split needed by the root
   - package this either as direct classification or as part of full IR local
     connectivity

3. **Satellite local-connectivity payload**
   - prove the local-connectivity endpoint for the tower case without appealing
     to root-facing Problem 4.3 / 4.4 seams
   - if the current proof still depends on deeper proxy machinery, isolate that
     dependency explicitly

4. **IR local-connectivity synthesis**
   - combine the classification and satellite endpoint into a theoremized
     `IRLocallyConnectedData`
   - use that theorem to clear the final root seam

---

## Concrete File-Level Program

### Step 1: Audit the remaining axiom-backed routes

Files:

- `Mlc/MainConjecture.lean`
- `Mlc/InconsistencyRoute.lean`
- `Mlc/RenormalizationTowerExistence.lean`
- `Mlc/PrimitiveModulusDivergence.lean`

Task:

- identify exactly which old axioms reappear if the root is rerouted to
  `ir_locally_connected_seam`
- make sure the final elimination plan avoids that route

### Step 2: Build the constructive IR payload

Files:

- likely `Mlc/MainConjecture.lean`
- likely `Mlc/InfinitelyRenormalizable.lean`
- possibly new focused files for virtual near-Molecule classification / LC

Task:

- prove either direct `IRLocallyConnectedData` or the stronger pair feeding it
- keep the theorem statements aligned with the current code architecture

### Step 3: Integrate at the root

Files:

- `Mlc/MainConjecture.lean`
- `check_axioms.lean`
- `README.md`

Task:

- remove `problem45_virtualNearMoleculeRenormalization`
- preserve a root frontier with no project-level axioms beyond Lean core

Current blocker:

- any available root cutover in the existing repository revives older project
  axioms instead of removing the last one
- no constructive theorem currently provides either `IRLocallyConnectedData` or
  the current strengthened Problem 4.5 pair

---

## Success Criterion

This plan is complete when:

1. `problem45_virtualNearMoleculeRenormalization` disappears from the output of
   `make check`
2. `problem43_pseudoSiegelAPrioriBounds` stays absent from the frontier
3. `problem44_virtualMolecule` stays absent from the frontier
4. no new project-level axioms are introduced
5. `make build`, `make check`, and `scripts/verify_output.sh` pass
6. the README explains the zero-project-axiom root frontier precisely
