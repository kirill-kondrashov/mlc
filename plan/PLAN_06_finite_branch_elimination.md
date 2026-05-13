# PLAN 06: Eliminate `finite_branch_local_connectivity`

**Status:** EXPOSED-BLOCKER STATE  
**Difficulty:** High  
**Goal:** Remove `finite_branch_local_connectivity` from the root frontier
without surfacing replacement finite-branch axioms.

**Important:** the currently exposed
`para_puzzle_piece_basis_sketch` / `para_puzzle_piece_inter_mandelbrot_connected`
pair is a temporary diagnostic state, **not** a new accepted axiom frontier.

---

## Current Outcome

The direct elimination attempt removed the root axiom
`finite_branch_local_connectivity`, but it did **not** finish the finite branch.

The currently exposed non-core frontier is:

- `MLC.Quadratic.para_puzzle_piece_inter_mandelbrot_connected`
- `MLC.Quadratic.filled_julia_set_connected`
- `problem43_pseudoSiegelAPrioriBounds`
- `problem44_virtualMolecule`
- `problem45_virtualNearMoleculeRenormalization`

The important new information is the **shape of the real blocker** this cutover
made visible.

This state should be treated as:

1. a successful diagnostic cutover
2. a proof that the old root axiom was hiding deeper finite-branch seams
3. **not** a satisfactory stopping point

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
first surfaced two deeper finite-branch axioms:

- `MLC.Quadratic.para_puzzle_piece_inter_mandelbrot_connected`
- `MLC.Quadratic.para_puzzle_piece_basis_sketch`

So the true blocker is:

> the finite branch currently depends on **three** unresolved internal seams,
> not one.

Current update:

- the **basis seam has now been eliminated**
- `para_puzzle_piece_basis_sketch` and `iInter_closure_para_puzzle_piece` are
  theoremized in `ParaPuzzleBasis.lean`
- this currently exposes the lower-level theorem
  `MLC.Quadratic.filled_julia_set_connected` through the basis proof
- the remaining project-level `para_puzzle_*` blocker is now only
  `MLC.Quadratic.para_puzzle_piece_inter_mandelbrot_connected`

An additional conclusion from the latest elimination attempt is that the two
exposed `para_puzzle_*` seams are not just waiting for short local proofs under
the current abstraction. The present translated `ParaPuzzlePieceAt` model is
good enough for the shrink theorem, but it does not match the existing
containment and connectedness route built around the global Yoccoz
`ParaPuzzlePiece`.

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

Latest verdict:

- the translated `ParaPuzzlePieceAt` route successfully supports the internal
  shrink theorem
- but the remaining connectedness and basis steps do not appear theoremizable
  from the current translated model plus existing repo lemmas
- so the next real step is not “prove the two exposed axioms directly”, but
  “redesign the finite-branch parameter-piece abstraction so the shrink and
  connected-neighborhood routes are compatible”

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

### Step 0: Redesign the finite-branch parameter-piece model

Files:
- `Mlc/Quadratic/Complex/ParaPuzzle.lean`
- `Mlc/ParaPuzzleContainment.lean`
- `Mlc/LcAtOfShrink.lean`
- `Mlc/MainConjecture.lean`

Task:
- stop treating the current translated `ParaPuzzlePieceAt` surrogate as if it
  can simultaneously support:
  1. the shrink theorem
  2. the Mandelbrot-intersection connectedness route
  3. the neighborhood-basis route
- introduce a model where these routes are mathematically compatible, likely by
  splitting centered shrink pieces from the Yoccoz/global parameter pieces or by
  refactoring the finite-branch local-connectivity route away from the current
  surrogate

Reason:
- `ParaPuzzleContainment.lean` proves containment for the global Yoccoz
  `ParaPuzzlePiece n`, not for the translated family
- `para_puzzle_piece_basis_sketch` is not a formal consequence of the current
  shrink/compactness/nestedness package alone

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
- this exposed the deeper issue that the finite-branch route currently mixes two
  incompatible notions of parameter puzzle piece

### Step 3: Replace the basis axiom

Files:
- `Mlc/Quadratic/Complex/ParaPuzzleBasis.lean`
- `Mlc/LcAtOfShrink.lean`

Task:
- either prove `para_puzzle_piece_basis_sketch`
- or refactor `lc_at_of_shrink` so that this theorem is no longer needed

Refinement:
- do **not** accept `para_puzzle_piece_basis_sketch` as part of the new frontier
- the purpose of this step is to make the exposed basis seam disappear entirely

Progress:
- completed
- `para_puzzle_piece_basis_sketch` is theoremized
- `iInter_closure_para_puzzle_piece` is theoremized
- `ParaPuzzleBasis.lean` now also contains theoremized Mandelbrot-set
  openness/closedness/compactness groundwork used by the basis-side proof

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
- these exposed axioms must now be removed; they are blockers, not replacements

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
7. `check_axioms.lean`, `README.md`, and verification scripts are restored to
   enforce that three-axiom frontier rather than the temporary exposed-blocker
   one
8. the final route does not rely on the current translated `ParaPuzzlePieceAt`
   model in places where the global Yoccoz `ParaPuzzlePiece` semantics are
   actually required
9. the basis-side proof does not leak `filled_julia_set_connected` into the root
   frontier if the intended final frontier is exactly Problems 4.3 / 4.4 / 4.5
