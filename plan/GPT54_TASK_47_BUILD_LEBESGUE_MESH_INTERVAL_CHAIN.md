# TASK 47 — Build an explicit Lebesgue-mesh chain on `Icc (0,1)`

## Global context

The global objective remains removal of:

```lean
MLC.green_sublevel_translate_inter_mandelbrot_connected_straddling
```

The local branch-continuation route is currently blocked only by interval
combinatorics. Result 46 added the actual open-cover API:

```lean
BasinLoopFiniteLocalRootBranchCover.coverSet
BasinLoopFiniteLocalRootBranchCover.coverSet_isOpen
BasinLoopFiniteLocalRootBranchCover.center_mem_coverSet
```

For a uniformly escaping loop, these cover sets are open subsets of the compact
interval subtype `{t : ℝ // t ∈ Icc (0,1)}` and cover the whole subtype.

## Deliverable

Implement a constructive refinement using a Lebesgue number and a uniform mesh.
The exact representation is flexible, but the result must provide:

1. a natural mesh size `m` and endpoints covering `[0,1]`;
2. an assigned Stage 2C center/branch to each mesh cell;
3. every mesh cell contained in the assigned relative-open `coverSet`;
4. ordered coverage of all points in `Icc (0,1)`;
5. an explicit shared endpoint for every pair of adjacent cells.

The intended mathematical proof is:

```text
finite open cover of compact Icc(0,1)
→ positive Lebesgue number δ
→ choose m with 1/m < δ
→ each mesh interval has diameter < δ
→ each mesh interval lies in one cover member
→ adjacent cells share endpoint k/m
```

Prefer a theorem specialized to the Stage 2C cover if a generic theorem causes
unnecessary subtype complexity. The assigned cover member must remain tied to
the actual branch data, not merely to an abstract open set.

## Constraints

- Construct all witnesses; do not use a bare existential chain field.
- Keep the result independent of branch alignment and monodromy.
- Do not use `BasinLoopChartChain.of_escaping_level` as a substitute.
- Do not build a global Böttcher coordinate or parameter external coordinate.
- No `sorry`, `admit`, or new axiom.
- Prefer a focused new module or a narrowly scoped addition near
  `BottcherFiniteEscapingLoopCover`.
- Do not commit.

## Verification

Compile all probes. If implementation succeeds, run:

```bash
lake build
lake env lean check_axioms.lean
```

The axiom frontier must remain unchanged. If blocked, report the exact
Lebesgue-number/subtype theorem gap and the smallest next task.

## Result report

Write:

`plan/GPT54_RESULT_47_BUILD_LEBESGUE_MESH_INTERVAL_CHAIN.md`

Include:

- the exact mesh/chain representation;
- the compactness/Lebesgue-number theorem used;
- how each mesh cell is assigned to real branch data;
- how adjacent shared endpoints are represented;
- any precise blocker.
