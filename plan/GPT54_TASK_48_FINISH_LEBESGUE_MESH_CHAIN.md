# TASK 48 — Finish the explicit Lebesgue-mesh interval chain

## Global context

The target remains removal of:

```lean
MLC.green_sublevel_translate_inter_mandelbrot_connected_straddling
```

Result 47 established the correct compactness foundation for the actual Stage
2C cover:

```lean
cover.exists_lebesgue_number
```

and checked mesh endpoint helpers:

```lean
mesh_left_mem_Icc
mesh_right_mem_Icc
meshPoint
meshPointRight
```

The only remaining gap is selecting one cover center for each uniform mesh cell
and packaging the resulting ordered chain.

## Deliverable

Complete the chain construction in or next to
`Mlc/BottcherFiniteEscapingLoopCover.lean`.

For some `m : ℕ`, construct cells indexed by `k ≤ m` with endpoints:

```text
left(k)  = k / (m + 1)
right(k) = (k + 1) / (m + 1).
```

For each cell, choose a center from `cover.centers` whose relative-open
`coverSet` contains the entire cell, and retain the corresponding actual
`LocalPullbackRootBranchData`. The output must prove:

1. endpoint membership in `Icc (0,1)`;
2. ordered mesh coverage of every point of `Icc (0,1)`;
3. closed-cell containment in the selected `coverSet`;
4. adjacent cells share the explicit endpoint
   `(k+1)/(m+1)`;
5. the shared endpoint is in both selected cover sets.

The exact Lean representation may use a `List`, `Fin (m+1)`, or a specialized
structure, but all witnesses must be constructed, not asserted.

## Constraints

- Reuse the checked Result 47 APIs.
- Keep the result at the interval-cover level.
- Do not invoke branch rotations or overlap equality yet.
- Do not connect to the abstract value-space chart chain.
- Do not claim continuation or monodromy.
- No `sorry`, `admit`, or new axiom.
- Do not edit unrelated modules or commit.

## Verification

Run:

```bash
lake env lean Mlc/BottcherFiniteEscapingLoopCover.lean
lake build
lake env lean check_axioms.lean
```

The existing axiom frontier must remain unchanged.

## Result report

Write:

`plan/GPT54_RESULT_48_FINISH_LEBESGUE_MESH_CHAIN.md`

Report the exact chain structure, the mesh-size choice, the per-cell center
selection, and the overlap-witness theorem.
