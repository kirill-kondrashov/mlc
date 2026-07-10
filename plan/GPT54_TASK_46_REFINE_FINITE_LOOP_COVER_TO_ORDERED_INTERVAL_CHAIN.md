# TASK 46 — Refine the finite loop cover into an ordered interval chain

## Global context

The global target remains removal of:

```lean
MLC.green_sublevel_translate_inter_mandelbrot_connected_straddling
```

The local Böttcher branch program has:

- finite local branch data along uniformly escaping loops;
- local overlap equality;
- root-of-unity branch alignment.

The exact blocker before actual continuation is interval combinatorics. The
Stage 2C structure:

```lean
BasinLoopFiniteLocalRootBranchCover
```

contains a finite center set and a pointwise cover, but no order, intervals, or
adjacent overlap witnesses.

## Deliverable

Prove a generic, constructive finite-interval refinement theorem, or a
specialized theorem for `BasinLoopFiniteLocalRootBranchCover`, that turns the
finite relative-open cover of `Icc (0,1)` into data equivalent to:

```text
(s₀, [a₀,b₀]), ..., (sₖ, [aₖ,bₖ])
```

with:

1. `0 ≤ aᵢ ≤ bᵢ ≤ 1`;
2. the intervals cover every `t ∈ Icc (0,1)`;
3. each `[aᵢ,bᵢ]` is contained in the relative-open set assigned to `sᵢ`;
4. the sequence is ordered along the interval;
5. every adjacent pair has a nonempty intersection;
6. an explicit witness `τᵢ` belongs to both adjacent intervals.

The assigned cover sets should be the preimages of interiors of actual branch
domains, so that the result can later be applied to `γ.path τᵢ`.

The representation may use a `List`, `Fin m`, or another finite index, but it
must expose enough inequalities and membership facts for a later telescoping
continuation proof. Do not require any branch equality or multiplier data yet.

## Constraints

- Construct the chain from the cover; do not add an unproved existential field.
- Keep the theorem independent of global monodromy and simple-connectivity.
- Do not use the abstract punctured-plane chart chain as a replacement.
- Do not modify the frontier axiom or parameter-plane definitions.
- No `sorry`, `admit`, or new axiom.
- Prefer a new focused module or a narrowly scoped addition next to
  `BottcherFiniteEscapingLoopCover`.
- Do not commit.

## Verification

Compile all temporary probes. If implementation succeeds, run:

```bash
lake build
lake env lean check_axioms.lean
```

The project axiom frontier must remain unchanged.

## Result report

Write:

`plan/GPT54_RESULT_46_REFINE_FINITE_LOOP_COVER_TO_ORDERED_INTERVAL_CHAIN.md`

Report:

- the exact chain representation;
- the construction from the finite open cover;
- the topology lemmas used;
- any precise blocker if implementation failed;
- why the result is sufficient for the next actual-branch continuation task.
