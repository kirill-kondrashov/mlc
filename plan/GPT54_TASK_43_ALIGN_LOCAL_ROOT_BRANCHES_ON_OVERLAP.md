# TASK 43 — Align finite-level local root branches on an overlap

## Global context

The long-term target remains removal of:

```lean
MLC.green_sublevel_translate_inter_mandelbrot_connected_straddling
```

The credible route uses genuine moving parameter geometry, but that route first
needs a genuine whole-basin Böttcher coordinate. The current basin program has
now established:

- local holomorphic finite-level root branches;
- one-step and arbitrary finite-level lifting;
- finite local covers of uniformly escaping loops;
- equality of two root branches on a connected overlap when they agree at one
  point.

The remaining local-glue problem is to produce that agreement by an explicit
root-of-unity normalization.

## Deliverable

Implement a focused theorem/module for the following situation.

Let `left` and `right` be finite-level local root branch data solving the same
equation at level `N`. Let `s` be a connected/preconnected overlap with:

- `s ⊆ left.U`;
- `s ⊆ right.U`;
- a chosen point `w₀ ∈ s`;
- the common pullback target is nonzero on `s`.

Use:

```lean
pullbackRootSet_torsor_transitive
localPullbackRootBranch_eqOn_of_eqAt
```

to obtain a root-of-unity multiplier `ζ` such that the rotated branch
`ζ * right.branch` agrees with `left.branch` at `w₀`, then prove it agrees on
all of `s`.

Prefer packaging the rotated branch itself as a
`LocalPullbackRootBranchData` object, with:

- the same center/domain;
- branch function `fun z => ζ * right.branch z`;
- inherited differentiability;
- root equation proved using `ζ ^ (2 ^ N) = 1`;
- center root-set membership;
- an explicit theorem that the aligned branch equals `left.branch` on `s`.

If a fully packaged rotated structure is unnecessarily intrusive, first land a
precise theorem about the rotated function and state why that is the smallest
sound API. Do not hide the multiplier in a proposition-valued existential that
cannot be reused by later chain constructions.

## Constraints

- Keep the theorem finite-level and local.
- Make all nonvanishing assumptions explicit before division or torsor use.
- Do not claim that the multiplier is globally or canonically trivial.
- Do not infer global monodromy triviality from connectedness of one overlap.
- Do not use the false principal-`cpow` basin candidate as a global coordinate.
- Do not attempt parameter rays, equipotentials, or the parameter external map.
- No `sorry`, `admit`, or new axiom.
- Prefer a new leaf module; edit `ConstructiveBasinCoordinate.lean` only if
  unavoidable for a narrowly scoped declaration.
- Register a new module in `Mlc.lean` only if implementation succeeds.
- Do not commit.

## Verification

If implementation succeeds, run:

```bash
lake build
lake env lean check_axioms.lean
```

The axiom frontier must remain unchanged. If blocked, compile the temporary
probe isolating the blocker and report the exact command/result.

## Result report

Write:

`plan/GPT54_RESULT_43_ALIGN_LOCAL_ROOT_BRANCHES_ON_OVERLAP.md`

State:

- whether the alignment theorem was implemented or blocked;
- its exact Lean statement and module;
- the multiplier/rotation construction used;
- what remains before finite cover-chain continuation can be formalized.
