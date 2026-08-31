# TASK 42 — Prove equality of finite-level local root branches on overlaps

## Global context

The global target remains removal of:

```lean
MLC.green_sublevel_translate_inter_mandelbrot_connected_straddling
```

The credible replacement route is:

```text
genuine whole-basin Böttcher coordinate
→ parameter external coordinate
→ parameter rays/equipotentials
→ finite moving parameter graph
→ connected parapuzzle component
→ downstream migration
→ remove the frozen straddling axiom
```

Result 41 showed that the parameter external coordinate cannot yet be defined
honestly because the repository lacks the whole-basin evaluation theorem
`B_c(c)` for arbitrary `c ∉ MandelbrotSet`. The immediate prerequisite is local
branch compatibility. Existing work has only supplied:

- Stage 1: local holomorphic finite-level root branches;
- Stage 2A: one-level lifting;
- Stage 2B: arbitrary finite-level lifting;
- Stage 2C: finite covers of uniformly escaping loops.

It has not supplied overlap equality, transition multipliers, or monodromy
triviality.

## Deliverable

Audit the existing structures and implement a focused module proving a local
overlap theorem of the following mathematical form:

Given two local branch data objects at the same finite level, if an overlap
`V` is connected/preconnected, lies in both branch domains, the two branch
functions agree at one point of `V`, and the common pullback target is nonzero
on `V`, then the branch functions agree on all of `V`.

The theorem should conclude an `EqOn` statement and should expose the
nonvanishing/outside condition explicitly. It must not assume global basin
simple-connectivity or an all-level chart chain.

Prefer the smallest API compatible with:

```lean
LocalPullbackRootBranchData c N z₁
LocalPullbackRootBranchData c N z₂
```

when their branches are compared on a common overlap. If a theorem for two
arbitrary continuous root functions is cleaner, package that first and then
derive the local-branch corollary.

## Required checks

- Reuse `pullbackRootSet_torsor_transitive` or the existing connected analytic
  zero-free chart theorem where appropriate.
- Ensure the proof does not silently divide by zero.
- Keep the result finite-level and local.
- Do not claim any loop monodromy is trivial.
- Do not prove or use holomorphicity of
  `basinLogSeriesExtensionCandidate`; that principal candidate is known to fail
  globally.
- No `sorry`, `admit`, or new axiom.
- Do not edit `ConstructiveBasinCoordinate.lean` unless a narrowly necessary
  theorem registration/import change is required; prefer a new leaf module.
- Register a new module in `Mlc.lean` only if implementation succeeds.
- Do not commit.

## Verification

If implementation succeeds, run:

```bash
lake build
lake env lean check_axioms.lean
```

The axiom frontier must remain unchanged. If implementation is blocked, compile
the temporary probes used to isolate the blocker and report their exact result.

## Result report

Write:

`plan/GPT54_RESULT_42_PROVE_LOCAL_ROOT_BRANCH_OVERLAP_EQUALITY.md`

State:

- whether the overlap theorem was implemented or blocked;
- its exact Lean statement and module if implemented;
- the exact theorem/API gap if blocked;
- why this is the correct next step toward the whole-basin extension and
  parameter external coordinate.
