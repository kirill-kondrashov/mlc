# TASK 44 — Build an ordered finite overlap chain for an escaping basin loop

## Global context

The target remains removal of:

```lean
MLC.green_sublevel_translate_inter_mandelbrot_connected_straddling
```

The current local Böttcher infrastructure has reached:

- Stage 1 local holomorphic root branches;
- Stage 2A/2B finite-level lifting;
- Stage 2C finite local covers of uniformly escaping loops;
- Stage 2D overlap equality;
- Stage 2E root-of-unity branch alignment.

The remaining finite-level gap is not yet global monodromy. The Stage 2C cover
is unordered and only says every loop point lies in some branch neighborhood.
Continuation needs an ordered chain whose neighboring entries have an explicit
common path point.

## Deliverable

Audit the existing declaration:

```lean
BasinLoopFiniteLocalRootBranchCover
```

and implement a new focused chain structure/constructor if the required
topology can be proved. A useful shape is a structure containing:

```lean
indices : Fin m → {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1}
times : Fin (m + 1) → {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1}
ordered : ...
segment_mem : ...
adjacent_overlap : ...
```

The exact representation is flexible, but it must provide these mathematical
facts:

1. the selected times are ordered from `0` to `1`;
2. the corresponding path segments cover the whole parameter interval;
3. each segment lies in the assigned local branch domain;
4. every adjacent pair has an explicit time `t` with
   `γ.path t ∈ Uᵢ ∩ Uᵢ₊₁`;
5. the overlap is suitable for applying the Result 43 alignment theorem.

Use the existing continuity of `γ.path`, compactness of `Icc (0,1)`, and the
open interiors of the Stage 1 neighborhoods. If a Lebesgue-number theorem is
needed, isolate it in a small probe first. Do not fake the chain by inserting
an existential field without constructing its witnesses.

## Constraints

- Keep the result finite-level and restricted to uniformly escaping loops.
- Do not claim neighboring unrotated branches agree.
- Do not claim total monodromy is trivial.
- Do not assume the basin is simply connected.
- Do not build the whole-basin Böttcher extension or parameter external map.
- No `sorry`, `admit`, or new axiom.
- Prefer a new leaf module and register it in `Mlc.lean` only on success.
- Do not edit unrelated files or commit.

## Verification

If implementation succeeds:

```bash
lake build
lake env lean check_axioms.lean
```

The existing axiom frontier must remain unchanged. If blocked, compile the
smallest probe demonstrating the blocker and report the exact command/result.

## Result report

Write:

`plan/GPT54_RESULT_44_BUILD_ESCAPING_LOOP_OVERLAP_CHAIN.md`

State:

- whether chain construction succeeded or was blocked;
- the exact structure/theorem added;
- how adjacent overlaps are represented;
- what remains before finite-chain continuation and monodromy accounting.
