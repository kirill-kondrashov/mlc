# PLAN 06: Eliminate `finite_branch_local_connectivity`

**Status:** EXPOSED-BLOCKER STATE  
**Difficulty:** High  
**Goal:** Remove `finite_branch_local_connectivity` from the root frontier
without surfacing replacement finite-branch axioms.

---

## Current Outcome

The direct elimination attempt removed the root axiom
`finite_branch_local_connectivity`, but it did **not** finish the finite branch.

The currently exposed non-core frontier is:

- `MLC.Quadratic.para_puzzle_piece_basis_sketch`
- `MLC.Quadratic.para_puzzle_piece_inter_mandelbrot_connected`
- `problem43_pseudoSiegelAPrioriBounds`
- `problem44_virtualMolecule`
- `problem45_virtualNearMoleculeRenormalization`

The important new information is the **shape of the real blocker** this cutover
made visible.

---

## What the Failed Attempt Showed

The earlier version of this plan assumed:

1. connectedness on `ParaPuzzlePieceAt c n ∩ MandelbrotSet` was already
   effectively internal
2. the only real blocker was the shrink chain
   ```lean
   para_iInter_eq_singleton_of_dyn_iInter_eq_singleton
   → parameter_shrink_of_yoccoz
   → finite_branch_local_connectivity
   ```

That turned out to be incomplete.

When `finite_branch_local_connectivity` was pushed inward, `make check`
surfaced two deeper finite-branch axioms:

- `MLC.Quadratic.para_puzzle_piece_inter_mandelbrot_connected`
- `MLC.Quadratic.para_puzzle_piece_basis_sketch`

So the true blocker is:

> the finite branch currently depends on **three** unresolved internal seams,
> not one.

---

## Revised Blocker Decomposition

### Blocker A: honest parameter-piece interface

The mathematically honest translated definition of

```lean
ParaPuzzlePieceAt c n
```

is the right one for proving parameter shrink from dynamical shrink.

But the current simplified definition is what makes the old
`MandelbrotSet ⊆ ParaPuzzlePieceAt c n` connectedness shortcut work.

So the next pass must first settle the interface:

- either keep the simplified definition and accept that the shrink theorem is not
  honestly derivable there
- or restore the translated definition and rebuild the FR connectedness route
  around it

For a genuine elimination, the second option is the right target.

### Blocker B: connectedness replacement

The axiom

```lean
Quadratic.para_puzzle_piece_inter_mandelbrot_connected
```

is still lurking behind the default motion/transport witness machinery.

In particular, the attempted constructive route through Böttcher motion still
ran through an axiom-backed default witness path in the current code.

So the next pass needs an **axiom-free transport-witness / boundary-motion
construction** for:

```lean
ParaPuzzlePieceAt c n ∩ MandelbrotSet
```

### Blocker C: neighborhood-basis replacement

The axiom

```lean
Quadratic.para_puzzle_piece_basis_sketch
```

also surfaced immediately once the finite branch was internalized.

This means local connectivity from parameter shrink still depends on a separate
topological para-puzzle basis theorem.

So the next pass must either:

1. prove `para_puzzle_piece_basis_sketch` internally, or
2. replace the current `lc_at_of_shrink` route by another theorem that does not
   depend on that basis axiom

### Blocker D: only then the shrink chain

Once A/B/C are resolved, the remaining theoremization becomes the old target:

1. prove
   `Quadratic.PrincipalNest.para_iInter_eq_singleton_of_dyn_iInter_eq_singleton`
2. theoremize `parameter_shrink_of_yoccoz`
3. remove `finite_branch_local_connectivity`

---

## Updated Execution Order

### Step 1: Trace and remove the hidden connectedness dependency

Files:
- `Mlc/Quadratic/Complex/PuzzleLemmas2.lean`
- `Mlc/Quadratic/Complex/PuzzleBoundaryMotion.lean`
- `Mlc/Quadratic/Complex/Bottcher/BottcherMotion.lean`

Task:
- identify the exact path by which the current default motion route depends on
  `para_puzzle_piece_inter_mandelbrot_connected`
- replace it with an explicit boundary-motion / transport witness theorem

Progress:
- completed the first half of this step
- `Mlc/Quadratic/Complex/Bottcher/BottcherMotion.lean` now has explicit
  witness-parameterized constructors:
  - `motion_preserves_para_piece_of_green_sublevel_of_witness_hyp`
  - `bottcher_motion_data_of_green_sublevel_of_witness_hyp`
  - `bottcher_motion_hyp_of_green_sublevel_of_witness_hyp`
  - `puzzle_boundary_motion_hyp_of_onM_of_witness_hyp`
- the old defaults still exist, but the dependency is now explicit instead of
  being hidden inside the Böttcher route

### Step 2: Rework the para-puzzle interface

Files:
- `Mlc/Quadratic/Complex/ParaPuzzle.lean`
- `Mlc/ParaPuzzleContainment.lean`
- `Mlc/MainConjecture.lean`

Task:
- restore the translated `ParaPuzzlePieceAt` definition
- update the few proofs that currently rely on the simplified membership fact
- make the FR route compatible with the honest parameter-piece notion

Progress:
- completed
- the translated definition is restored
- the pure translation shrink theorem is internalized
- the remaining issues are no longer interface-level but the two exposed FR seams

### Step 3: Replace the basis axiom

Files:
- `Mlc/Quadratic/Complex/ParaPuzzleBasis.lean`
- `Mlc/LcAtOfShrink.lean`

Task:
- either prove `para_puzzle_piece_basis_sketch`
- or refactor `lc_at_of_shrink` so that this theorem is no longer needed

### Step 4: Retry the shrink theoremization

Files:
- `Mlc/Quadratic/Complex/PrincipalNestShrink.lean`
- `Mlc/AxiomsMainConjecture.lean`

Task:
- prove `para_iInter_eq_singleton_of_dyn_iInter_eq_singleton`
- theoremize `parameter_shrink_of_yoccoz`

Progress:
- completed
- both theorems are now internal

### Step 5: Drop the root finite-branch axiom

Files:
- `Mlc/MainConjecture.lean`
- `check_axioms.lean`
- `README.md`
- `site/`

Task:
- rewire the finite branch through the theoremized internal route
- verify that no new FR axioms appear in `make check`

Progress:
- partially completed
- the root axiom is gone
- `make check` now exposes exactly:
  - `para_puzzle_piece_basis_sketch`
  - `para_puzzle_piece_inter_mandelbrot_connected`

---

## Success Criterion

This plan is complete only when all of the following are true:

1. `finite_branch_local_connectivity` disappears from `check_axioms.lean`
2. `make check` does **not** surface replacement FR axioms such as
   `para_puzzle_piece_inter_mandelbrot_connected` or
   `para_puzzle_piece_basis_sketch`
3. `make build` passes
4. `make check` passes
5. `bash scripts/verify_output.sh` passes
6. the remaining non-core frontier is exactly:
   - `problem43_pseudoSiegelAPrioriBounds`
   - `problem44_virtualMolecule`
   - `problem45_virtualNearMoleculeRenormalization`
