# TASK 45 — Connect the concrete local-branch cover to actual continuation

## Global context

The target remains removal of:

```lean
MLC.green_sublevel_translate_inter_mandelbrot_connected_straddling
```

The Böttcher route currently has genuine local ingredients:

- `LocalPullbackRootBranchData`;
- finite-level lifting;
- `BasinLoopFiniteLocalRootBranchCover`;
- `localPullbackRootBranch_eqOn_of_eqAt`;
- `LocalPullbackRootBranchData.rotate`;
- `localPullbackRootBranch_eqOn_of_alignable`.

The repository also contains older `BasinLoopChartChain` and monodromy
structures. However, those structures describe zero-free charts in the
value-space and admit a canonical one-cell punctured-plane chain at escaping
levels. That chain has no actual adjacent overlap and does not by itself
continue a local branch in the dynamical z-plane.

## Deliverable

First audit the type-level relationship between:

```lean
BasinLoopFiniteLocalRootBranchCover
BasinLoopChartChain
ChartChainContinuationData
AnalyticContinuationAlongBasinLoop
```

Then choose one honest outcome.

### Outcome A — Concrete continuation package

If current APIs suffice, add a focused module defining a concrete continuation
package for a uniformly escaping loop. It should contain, directly or through a
clearly equivalent representation:

1. a finite ordered list of actual
   `LocalPullbackRootBranchData c N ...`;
2. intervals in time covering `Icc (0,1)`;
3. adjacent overlap times where the loop value lies in both corresponding
   domains;
4. explicit root-of-unity rotations aligning the right branch to the left;
5. use of Result 42/43 to prove equality on each connected overlap;
6. an endpoint branch and an explicit endpoint multiplier relative to the
   initial branch.

The endpoint multiplier may remain nontrivial. This is continuation data, not a
triviality theorem.

### Outcome B — Exact blocker

If the current finite cover cannot be converted into ordered actual branch
intervals, do not add an abstract existence field or reuse the vacuous
punctured-plane chain. Identify the first missing compact-interval/continuation
lemma and give the smallest next task.

## Constraints

- Work with actual local branch functions in the z-plane.
- Do not infer global monodromy triviality.
- Do not assume basin simple-connectivity.
- Do not use `basinLogSeriesExtensionCandidate` as a global holomorphic
  coordinate.
- Do not define or use the parameter external coordinate.
- No `sorry`, `admit`, or new axiom.
- Prefer a new leaf module; avoid modifying the abstract scaffolding unless a
  narrowly necessary theorem registration is required.
- Do not commit.

## Verification

For Outcome A:

```bash
lake build
lake env lean check_axioms.lean
```

The project axiom frontier must remain unchanged. For Outcome B, compile the
smallest temporary probes used to isolate the blocker and report the exact
results.

## Result report

Write:

`plan/GPT54_RESULT_45_CONNECT_LOCAL_BRANCH_COVER_TO_ACTUAL_CONTINUATION.md`

State:

- whether actual continuation was implemented or blocked;
- the exact new structure/theorem and its relation to existing APIs;
- how branch rotations and overlap equality are used;
- whether the endpoint multiplier remains conditional/nontrivial;
- the next smallest task toward genuine monodromy control.
