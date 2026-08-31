# TASK 50 — Generalize local branch overlap and alignment to distinct centers

## Global context

The target remains removal of:

```lean
MLC.green_sublevel_translate_inter_mandelbrot_connected_straddling
```

The concrete finite loop infrastructure now includes:

- `BasinLoopFiniteLocalRootBranchCover`;
- the Stage 2C `coverSet` API;
- a checked Lebesgue-number refinement;
- `BasinLoopMeshChain`, with actual branch data assigned to each mesh cell.

However, the local overlap theorems landed in Tasks 42/43 were stated for:

```lean
LocalPullbackRootBranchData c N z₀
```

on both sides. The mesh-chain branch data are centered at different points, so
the current theorem cannot be applied directly.

## Deliverable

Add a focused generalized API, preferably in a new leaf module:

```lean
left  : LocalPullbackRootBranchData c N z₁
right : LocalPullbackRootBranchData c N z₂
```

where `z₁` and `z₂` are independent.

Prove:

1. if a preconnected set `s` lies in both domains, the common pullback target is
   nonzero on `s`, and the branch values agree at one `w₀ ∈ s`, then the branch
   functions agree on `s`;
2. at an explicit overlap point, a root-of-unity multiplier can rotate the
   right branch to agree with the left branch;
3. the rotated right branch is valid local branch data with center `z₂`;
4. the aligned branch agrees with the left branch on the overlap.

Reuse the existing torsor, countability, and continuity proof. Only the
center-index types should change. If useful, make the generalized theorem the
primary declaration and derive the old same-center theorem as a specialization.

## Constraints

- No casts that erase the distinct-center types.
- No `sorry`, `admit`, or new axiom.
- Keep the theorem finite-level and local.
- Do not yet construct endpoint continuation or monodromy.
- Do not use `BasinLoopChartChain.of_escaping_level`.
- Do not edit unrelated files or commit.

## Verification

Run:

```bash
lake build
lake env lean check_axioms.lean
```

The project axiom frontier must remain unchanged.

## Result report

Write:

`plan/GPT54_RESULT_50_GENERALIZE_BRANCH_OVERLAP_TO_DISTINCT_CENTERS.md`

Report the generalized theorem signatures, module location, compatibility with
the existing same-center API, and any precise blocker.
