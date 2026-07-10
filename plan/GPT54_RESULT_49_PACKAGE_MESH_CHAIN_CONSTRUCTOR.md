# Task 49 — Package Mesh Chain Constructor

## Outcome

Completed in `Mlc/BottcherFiniteEscapingLoopCover.lean`.

## What landed

Added the finite mesh-chain packaging for a `BasinLoopFiniteLocalRootBranchCover`:

- choice-based global parameters
  - `choiceDelta`
  - `choiceDelta_pos`
  - `choiceMeshSize`
  - `choiceMeshSize_lt`
- per-cell selections
  - `lebesgueCenterAt`
  - `lebesgueCenterAt_ball_subset`
  - `centerAt`
  - `centerAt_mem_centers`
- packaged chain data
  - `BasinLoopMeshChain`
  - `BasinLoopFiniteLocalRootBranchCover.toMeshChain`
- standalone mesh coverage lemma
  - `exists_mesh_cell_covering`

## Key design point

The implementation had to separate two different selections:

1. `center` / `lebesgueCenterAt`
   - the index produced by the Lebesgue-number theorem;
   - used to prove whole-cell containment in a `coverSet`.

2. `coverCenter` / `centerAt`
   - an actual Stage 2C center taken from the original finite cover witness;
   - carries membership in `cover.centers`.

This distinction is necessary because the Lebesgue-number witness need not itself
be a chosen element of `cover.centers`.

## Constructor content

`BasinLoopMeshChain` records:

- mesh size;
- a containment center for each `Fin (m+1)` cell;
- a genuine selected cover center for each cell;
- membership of each selected cover center in `cover.centers`;
- cell containment into the chosen `coverSet`;
- coverage of `Icc (0,1)` by some mesh cell;
- for each adjacent pair, the shared endpoint and membership in both neighboring cells.

## Proof notes

- Cell containment uses `mesh_interval_dist_lt_fin` together with the chosen
  Lebesgue ball inclusion.
- Coverage is proved by `exists_mesh_cell_covering` using a `Nat.floor` index on
  `(m+1) * y` and a last-cell fallback when `floor` exceeds `m`.
- The overlap point is the shared endpoint `(j+1)/(m+1)` built via `meshPointRight`.

## Validation

Targeted validation passed:

- `lake env lean Mlc/BottcherFiniteEscapingLoopCover.lean`
