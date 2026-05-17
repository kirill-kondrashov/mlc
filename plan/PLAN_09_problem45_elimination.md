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

### Literature refinement of this blocker

The literature search sharpens the obstruction:

1. The blocker is **not uniform across all IR configurations**.
2. There is a substantial **bounded-type constructive region** already covered
   by proven mathematics:
   - Kahn, *A priori bounds I: Bounded primitive combinatorics*
   - Kahn–Lyubich, *A priori bounds III: Molecules*
   - Dudko–Lyubich, arXiv:2309.02107 (MLC at Feigenbaum points)
3. The genuinely open residue aligns with Dudko 2512.24171:
   - remaining unbounded satellite ql cases (Problem 4.3)
   - virtual Molecule interpolation / virtual bounded-type satellite ql
     (Problem 4.4)
4. Therefore the strongest next revision is to **split Problem 4.5 by proven vs
   still-open regions**, not to keep it as a single monolithic seam

---

## Revised Elimination Strategy

### Phase A: Normalize the IR interface

Relevant files:

- `Mlc/RenormalizationTypes.lean`
- `Mlc/InfinitelyRenormalizable.lean`
- `Mlc/MainConjecture.lean`
- `.lake/packages/yoccoz-theorem/Yoccoz/Yoccoz.lean`

Task:

- stop treating the current raw definition
  ```lean
  InfinitelyRenormalizable c :=
    Summable (fun n => modulus (PuzzleAnnulus c n))
  ```
  as the final IR interface
- use the upstream `yoccoz-theorem` package to normalize the finite side:
  ```lean
  NonRenormalizable c :=
    ¬ Summable (fun n => modulus (PuzzleAnnulus c n))
  ```
- explicitly separate:
  1. the puzzle/modulus proxy notion inherited from Yoccoz
  2. the actual renormalization-theoretic IR payload needed by the MLC route

Deliverable:

- a non-accidental IR interface that is no longer just a naked `Summable` alias

Observation from the current dependency:

- the `yoccoz-theorem` package provides the finite-side notion
  `NonRenormalizable` and Yoccoz's theorem
- it does **not** currently provide a ready-made notion of
  infinitely renormalizable parameters, primitive combinatorics, or a tower
  classifier
- therefore the dependency helps normalize the interface, but does not solve
  Problem 4.5 by itself

### Phase B: De-tautologize the primitive branch

Relevant files:

- `Mlc/RenormalizationTypes.lean`
- `Mlc/InfinitelyRenormalizable.lean`
- `Mlc/PrimitiveModulusDivergence.lean`
- `Mlc/MainConjecture.lean`

Task:

- replace the current tautological definition
  ```lean
  PrimitiveRenormalizable c :=
    ∀ hc : c ∈ MandelbrotSet,
      LocallyConnectedAt MandelbrotSet ⟨c, hc⟩
  ```
  by non-tautological primitive renormalization data
- the preferred replacement is combinatorial/dynamical:
  existence of a renormalization tower with infinitely many primitive steps, or
  an equivalent primitive ql package
- move local connectivity to a theorem proved from that primitive data

Deliverable:

- a theorem of the form
  ```lean
  PrimitiveData c → LocallyConnectedAt MandelbrotSet ⟨c, hc⟩
  ```
  rather than a definition equating primitive renormalizability with the
  conclusion itself

Current code-side landing point:

- the repo now contains a dedicated non-tautological sidecar interface
  ```lean
  PrimitiveRenormalizableData c :=
    ∃ T : RenormalizationTower (parameterToBMol c),
      {n | IsPrimitive (T.rel n)}.Infinite
  ```
- this is intentionally **not yet** the root-facing `PrimitiveRenormalizable`
  predicate, because swapping the root-facing interface immediately reactivates
  older primitive-branch dependencies in `collectAxioms`
- the next constructive task is therefore to route Problem 4.5 mathematics into
  `PrimitiveRenormalizableData` first, and only then replace the root-facing
  primitive interface when that cutover is axiom-safe

### Phase C: Isolate the true final target

Relevant files:

- `Mlc/MainConjecture.lean`
- `Mlc/InconsistencyRoute.lean`
- `Mlc/RenormalizationTowerExistence.lean`
- `Mlc/PrimitiveModulusDivergence.lean`

Task:

- separate the current strengthened Problem 4.5 interface from the weaker final
  target `IRLocallyConnectedData`
- distinguish theoremizable payloads from old axiom-backed shortcuts
- restate the final theorem using the revised IR/primitive interfaces from
  Phases A-B

Deliverable:

- a precise statement of the minimal final theorem needed to clear the root
  frontier without reviving older axioms

### Phase D: Preferred route — theoremize `IRLocallyConnectedData`

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

Literature caveat:

- the full direct theoremization of `IRLocallyConnectedData` is still open in
  the exact virtual near-Molecule generality of Dudko 2512.24171
- however, the bounded-type subregion appears theoremizable from existing
  literature, so the plan should first isolate and discharge that constructive
  subregion before confronting the residual open interpolation seam

### Phase E: Fallback route — theoremize the strengthened Problem 4.5 pair

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

1. **Interface cleanup before theoremization**
   - normalize the Yoccoz finite/IR interface
   - replace the tautological primitive branch by genuine primitive data
   - keep the old axiom-backed tower/inconsistency route out of the final target

2. **Primitive-first ql case decomposition**
   - formalize the virtual near-Molecule chain
     `M = M(0) ⊋ M(1) ⊋ ... ⊋ M(n+1)`
   - encode the condition that the first ql renormalization `f₁` is primitive
   - identify the exact data needed to control both classification and local
     connectivity in this regime

3. **Two virtual subcases from Dudko 2512.24171**
   - virtual bounded-type satellite ql: `n ≫ 1` with bounded relative periods
   - virtual near-neutral: `n = 0`
   - the remaining interpolation burden is exactly the virtual Molecule version
     of the near-degenerate regime

4. **Interpolation objects**
   - partially invariant virtual Julia sets
   - pseudo-Siegel / near-neutral control
   - a priori bounds that act on only the relevant portion of the postcritical
     set

5. **Classification payload**
   - explain why the remaining infinitely renormalizable cases fall into the
     primitive-or-satellite split needed by the root
   - package this either as direct classification or as part of full IR local
     connectivity
   - immediate code target:
     `IRNoTowerImpliesPrimitiveData` should eventually produce
     `PrimitiveRenormalizableData`, not just the current tautological primitive
     predicate

6. **Satellite local-connectivity payload**
   - prove the local-connectivity endpoint for the tower case without appealing
     to root-facing Problem 4.3 / 4.4 seams
   - if the current proof still depends on deeper proxy machinery, isolate that
     dependency explicitly

7. **IR local-connectivity synthesis**
   - combine the classification and satellite endpoint into a theoremized
     `IRLocallyConnectedData`
   - use that theorem to clear the final root seam

---

## Literature Map for the Next Revision

### Proven sources

1. **Kahn — bounded primitive combinatorics**
   - payload: primitive bounded-type a priori bounds
   - repo target: replace the fake primitive modulus layer by a genuine
     primitive lower-bound theorem feeding `PrimitiveRenormalizableData`

2. **Kahn–Lyubich — Molecules**
   - payload: anti-molecule / definitely primitive a priori bounds
   - repo target: constructive input for `IRNoTowerImpliesPrimitiveData` in the
     definitely primitive region

3. **Dudko–Lyubich 2309.02107 — MLC at Feigenbaum points**
   - payload: bounded-type primitive and bounded-type satellite local
     connectivity
   - repo target: the strongest constructive route for a bounded-type slice of
     `IRClassificationData ∧ VirtualJuliaSatelliteLocalConnectivityData`

4. **Dudko–Lyubich 2210.09280 — pseudo-Siegel / neutral renormalization**
   - payload: near-neutral pseudo-Siegel a priori bounds
   - repo target: the `n = 0` virtual near-Molecule subcase

### Programmatic / open source

5. **Dudko 2512.24171 §4.5**
   - payload: exact statement of the virtual near-Molecule chain and the
     interpolation problem
   - repo target: the residual open seam after bounded-type constructive work is
     extracted

### Planning consequence

- the plan should no longer aim at replacing the entire current Problem 4.5
  interface in one step
- instead, it should:
  1. theoremize the bounded-type constructive region
  2. shrink the remaining root seam to the honest open interpolation residue

---

## Concrete File-Level Program

### Step 1: Redesign the IR/primitive interfaces

Files:

- `Mlc/RenormalizationTypes.lean`
- `Mlc/InfinitelyRenormalizable.lean`
- `.lake/packages/yoccoz-theorem/Yoccoz/Yoccoz.lean`
- `Mlc/MainConjecture.lean`

Task:

- replace the raw `Summable`-based IR placeholder by a layered interface tied to
  the upstream Yoccoz finite-side notion
- replace the tautological primitive definition by combinatorial/dynamical
  primitive data
- make downstream theorem statements speak in terms of those revised interfaces

Additional literature-guided requirement:

- isolate a **bounded-type** subinterface as soon as possible, since this is the
  largest region with current constructive support in the literature

Current code-side milestone:

- `Mlc/MainConjecture.lean` now contains explicit bounded-type and residual-open
  sidecar interfaces:
  - `UniformlyBoundedRenormalizationPeriods`
  - `BoundedTypeRenormalizationTower`
  - `BoundedTypePrimitiveRenormalizableData`
  - `BoundedTypeSatelliteRenormalizableTower`
  - `BoundedTypeProblem45ConstructiveData`
  - `StrongBoundedTypeProblem45ConstructiveData`
  - `FullyConstructiveBoundedTypeIRClassificationData`
  - `FullyConstructiveBoundedTypeProblem45Data`
  - `ResidualOpenVirtualNearMoleculeData`
- the current `Problem45VirtualNearMoleculeRenormalizationData` now restricts
  canonically to the bounded-type slice via
  `boundedTypeConstructive_of_problem45`
- this keeps the root theorem unchanged while making the next split
  theorem-target explicit in Lean
- `Mlc/PrimitiveModulusDivergence.lean` now contains a direct bounded-type route
  from `PrimitiveModulusLowerBoundData` to parameter-piece shrinkage via
  `primitive_shrinkage_of_lower_bound`, and
  `Mlc/InfinitelyRenormalizable.lean` exposes the resulting constructive
  primitive endpoint as `primitiveRenormalizable_of_lowerBoundData`
- `Mlc/MainConjecture.lean` now also isolates the exact remaining bounded-type
  primitive input as
  `PrimitiveModulusLowerBoundFromBoundedTypeData`, with the assembly theorem
  `boundedTypeConstructive_of_fullyConstructive`
- `Mlc/MainConjecture.lean` now also contains the explicit placeholder axiom
  `primitiveModulusLowerBoundFromBoundedType` and theorem wrapper
  `primitiveModulusLowerBoundFromBoundedType_theorem`, so the remaining bounded
  primitive theorem target is named directly in code
- theorem-shape refinement from the literature:
  `Mlc/MainConjecture.lean` now also contains the stronger sidecar
  `PrimitiveFeigenbaumRenormalizableData` and theorem surface
  `PrimitiveModulusLowerBoundFromPrimitiveFeigenbaumData`
- this reflects Dudko–Lyubich `2309.02107`, where bounded-type primitive theory
  is naturally stated first for Feigenbaum maps whose renormalizations are all
  primitive, with eventual beau bounds `mod R^n f ≥ μ > 0`
- `Mlc/PrimitiveModulusDivergence.lean` and
  `Mlc/InfinitelyRenormalizable.lean` now also support the weaker and more
  honest eventual-lower-bound route via
  `EventualPrimitiveModulusLowerBoundData`,
  `primitive_shrinkage_of_eventual_lower_bound`, and
  `primitiveRenormalizable_of_eventualLowerBoundData`
- consequently, the remaining primitive blocker is no longer the shrinkage step
  itself but the absence of a genuine theorem producing
  eventual bounded primitive modulus control from bounded primitive tower data
- dependency audit result:
  - `.lake/packages/molecule-conjecture/Molecule/Problem4_3_Lemmas.lean`
    still treats the modulus-bounds step as `True`
  - `.lake/packages/molecule-conjecture/Molecule/Conjecture.lean`
    still defines `PseudoSiegelAPrioriBounds : Prop := True`
  - so there is currently no upstream Lean theorem to discharge
    `PrimitiveModulusLowerBoundFromBoundedTypeData`

### Step 3A: Theoremize eventual primitive Feigenbaum beau bounds

Files:

- `Mlc/MainConjecture.lean`
- `Mlc/PrimitiveModulusDivergence.lean`
- `Mlc/InfinitelyRenormalizable.lean`
- possibly a new focused file for bounded primitive compactness / modulus bridges

Task:

- replace the axiom
  `eventualPrimitiveModulusLowerBoundFromPrimitiveFeigenbaum`
  by a theorem proof
- derive
  `EventualPrimitiveModulusLowerBoundData c T`
  from primitive Feigenbaum bounded-type tower data
- keep the proof routed through the already theoremized chain:
  eventual primitive modulus lower bound
  -> `primitive_shrinkage_of_eventual_lower_bound`
  -> `primitiveRenormalizable_of_eventualLowerBoundData`

Research decomposition:

1. identify the exact literature theorem schema behind
   `EventualPrimitiveModulusLowerBoundFromPrimitiveFeigenbaumData`
2. decide whether
   `PrimitiveFeigenbaumRenormalizableData`
   is already the honest interface, or whether an intermediate compactness /
   anti-degeneracy package is still needed
3. split the proof into:
   - primitive Feigenbaum bounded-type data
     -> compactness / anti-degeneracy
   - compactness / anti-degeneracy
     -> eventual ql modulus lower bound
   - eventual ql modulus lower bound
     -> `EventualPrimitiveModulusLowerBoundData`
4. assemble these bridges into the final theorem
   `eventualPrimitiveModulusLowerBoundFromPrimitiveFeigenbaum_theorem`

Deliverable:

- a proved theorem replacing the placeholder axiom, with no new root-facing
  axioms introduced

Current refinement:

- the research program now targets the minimal theorem actually needed by the
  downstream proof chain:
  `EventualPrimitiveModulusLowerBoundFromPrimitiveFeigenbaumData`
- the current code-side landing point for the missing compactness / geometry
  input is now explicit:
  `PrimitiveFeigenbaumCompactModulusTrapData`
  together with the proved assembly theorem
  `eventualPrimitiveModulusLowerBoundFromPrimitiveFeigenbaum_of_compactTrap`
- the blocker has been sharpened further:
  `PrimitiveFeigenbaumCompactFamilyModulusData`
  packages the remaining task as an eventual compact family of renormalizations
  plus a positive modulus observable matching the principal-nest annuli, and now
  sits strictly below the compact-trap interface in code
- the blocker has now been made more canonical:
  `PrimitiveFeigenbaumCompactFamilyFundamentalModulusData`
  replaces the arbitrary modulus observable by the BMol fundamental annulus
  modulus `cmodulus (V \\ U)`, so the remaining gap is specifically the compact
  family + principal-nest/fundamental-annulus comparison theorem
- only after that theorem is in place should the repo attempt to derive or
  justify the broader target
  `EventualPrimitiveModulusLowerBoundFromBoundedTypeData`

### Step 2: Audit the remaining axiom-backed routes

Files:

- `Mlc/MainConjecture.lean`
- `Mlc/InconsistencyRoute.lean`
- `Mlc/RenormalizationTowerExistence.lean`
- `Mlc/PrimitiveModulusDivergence.lean`

Task:

- identify exactly which old axioms reappear if the root is rerouted to
  `ir_locally_connected_seam`
- make sure the final elimination plan avoids that route

### Step 3: Build the constructive IR payload

Files:

- likely `Mlc/MainConjecture.lean`
- likely `Mlc/InfinitelyRenormalizable.lean`
- likely `Mlc/RenormalizationTypes.lean`
- possibly new focused files for virtual near-Molecule classification / LC

Task:

- prove either direct `IRLocallyConnectedData` or the stronger pair feeding it
- keep the theorem statements aligned with the current code architecture

Refined execution order from the literature:

1. theoremize primitive bounded-type data
2. theoremize bounded-type satellite local connectivity
3. package a bounded-type slice of the current Problem 4.5 payload
4. only then isolate the residual unbounded / virtual interpolation seam

### Step 4: Integrate at the root

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
- the current `InfinitelyRenormalizable` / `PrimitiveRenormalizable` interfaces
  are not yet suitable as final constructive theorem targets
- the new `PrimitiveRenormalizableData` interface exists, but the root-facing
  cutover from `PrimitiveRenormalizable` to this non-tautological data is still
  blocked by missing axiom-free primitive local-connectivity synthesis
- the literature suggests that this blocker should be decomposed, not attacked
  monolithically: bounded-type appears constructively accessible, while the full
  virtual near-Molecule interpolation problem remains open

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
