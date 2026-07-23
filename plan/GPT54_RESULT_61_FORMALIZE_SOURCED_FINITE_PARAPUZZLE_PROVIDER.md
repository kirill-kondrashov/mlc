# GPT-5.4 Result 61 — Formalize a sourced finite parapuzzle provider

## Scope

I executed Prompt/Task 61 as a source-driven feasibility and prerequisite audit.
I reviewed the requested project modules, selected a concrete classical theorem
family to target, and checked whether the repository already has the formal
ingredients needed to instantiate

```lean
FiniteMovingWindowProviderData :=
  ∀ (c : ℂ) (hc : c ∈ MandelbrotSet) (_h : FinitelyRenormalizable c),
    ∃ (W K : ℕ → Set ℂ),
      ConnectednessWindowParameterPieceData c W K.
```

Per the hard honesty gate, I made **no speculative source edits** because the
required sourced mathematics is not yet formalized in the current codebase.
I wrote only this result artifact and did not commit.

## Executive verdict

**Hard stop.** Task 61 does **not** currently justify implementing a genuine
sourced finite parapuzzle provider.

The repo already has:
- the generic consumer interface `ConnectednessWindowParameterPieceData`;
- the theorem-facing finite-side route through `FiniteMovingWindowProviderData`;
- the old para-puzzle wrappers for openness, shrinkage, and connectedness;
- shell-level motion/family structures.

But it does **not** have the first decisive sourced theorem needed to construct a
new moving finite parapuzzle family `W n` distinct from `ParaPuzzlePieceAt c n`.
The first missing theorem is a genuine **phase–parameter / boundary-motion
transport theorem** producing finite-level parameter windows and identifying
their Mandelbrot slices with connected transport sets.

So the remaining work is **mathematical formalization**, not Lean bookkeeping.

## Stage A — Selected classical source theorem

I selected the standard Douady–Hubbard / Yoccoz parapuzzle package for quadratic
polynomials near finitely renormalizable parameters, in the following usable form:

> For a finitely renormalizable quadratic parameter `c` (outside the infinitely
> renormalizable obstruction), sufficiently deep parapuzzle pieces form a nested
> neighborhood basis at `c`; their boundaries move holomorphically with the
> parameter; and the corresponding parameter puzzle pieces cut out connected
> relative Mandelbrot slices determined by the same combinatorics.

This is not a single one-line theorem in the repository, but it is the correct
classical mathematical package that Task 61 asks us to source and map.

A standard public reference family is:
- J.-C. Yoccoz, *Julia sets with positive measure?* / local connectivity lectures,
  together with the quadratic Yoccoz puzzle technology as exposited in
  Douady–Hubbard / Lyubich / Schleicher references.
- For the parapuzzle / phase–parameter correspondence viewpoint used in the repo:
  Douady–Hubbard style holomorphic motion + lambda-lemma transport of puzzle
  boundaries.

### Repository-relevant sourced formulation

The exact sourced theorem shape needed by Lean is roughly:

```text
For each finitely renormalizable c ∈ MandelbrotSet,
there exists a depth-indexed family W n of parameter parapuzzle windows such that:
1. each W n is open;
2. c ∈ W n for all n;
3. {W n} is nested / forms a neighborhood basis at c;
4. W n ∩ MandelbrotSet is connected;
5. W n is defined by genuine moving puzzle-boundary combinatorics,
   not merely by the frozen set ParaPuzzlePieceAt c n.
```

This is exactly the data demanded by
`ConnectednessWindowParameterPieceData c W K` (with `K n := W n` or an honest
connectedness locus inside `W n`).

## Stage B — Mapping the source theorem to repository requirements

The target data fields are:

1. `window_open : ∀ n, IsOpen (W n)`
2. `base_mem_window : ∀ n, c ∈ W n`
3. `basis : ∀ U ∈ 𝓝 c, ∃ n, W n ⊆ U`
4. `locus_subset_window : ∀ n, K n ⊆ W n`
5. `inter_mandelbrot_connected : ∀ n, IsConnected (W n ∩ MandelbrotSet)`

A classical parapuzzle theorem can support these as follows:

- **Open windows** come from parameter windows bounded by moving rays /
  equipotentials / puzzle boundaries.
- **Basepoint membership** comes from the windows being centered at the reference
  parameter `c`.
- **Basis/shrinkage** comes from finite renormalizability + Yoccoz shrinking.
- **Connectedness** comes from the phase–parameter correspondence / holomorphic
  motion identification of the finite parapuzzle slice.
- **Honest parameter meaning** comes from the moving boundary construction,
  not from reusing `ParaPuzzlePieceAt c n` as-is.

## Stage C — Repository prerequisite audit

Below is the required classification table.

| Item | Classification | What is available | Why it is insufficient for the new provider |
|---|---|---|---|
| `Mlc/LcAtOfShrink.lean` `ConnectednessWindowParameterPieceData` | Consumer interface only | Exact target structure and adapters | Does not produce any sourced moving family |
| `Mlc/MainConjecture.lean` `FiniteMovingWindowProviderData` / `mlc_strategy_of_movingWindowData` | Consumer route only | Correct theorem-facing finite-side seam | Still requires an external provider theorem |
| `Mlc/Quadratic/Complex/PuzzleLemmas2.lean` `para_puzzle_piece_open`, `para_puzzle_piece_basis` | Frozen wrapper | Openness and basis for `ParaPuzzlePieceAt c n` | Explicitly prohibited as the new provider source; not a moving family |
| `Mlc/Quadratic/Complex/PuzzleLemmas2.lean` `para_puzzle_piece_inter_mandelbrot_connected` | Frozen wrapper / axiom | Connectedness of `ParaPuzzlePieceAt c n ∩ MandelbrotSet` | It is an axiom, not a sourced theorem; using it would violate the task |
| `Mlc/Quadratic/Complex/PuzzleBoundaryMotion.lean` | Shell only | `PuzzleBoundaryMotionHyp`, transport-witness packaging | The current constructor `puzzleBoundaryMotionHyp_of_connected_data` is circular: it rebuilds motion from already-assumed connectedness |
| `Mlc/Quadratic/Complex/Bottcher/BottcherMotion.lean` | Incomplete bridge shell | Names equipotentials and motion-flavored bridge structures | No checked theorem here yields finite parameter windows with connected Mandelbrot slices |
| `Mlc/Quadratic/Complex/ParaPuzzle.lean` / `ParaPuzzleBasis.lean` | Frozen para-puzzle infrastructure | Existing parameter-piece objects and shrinkage sketch | Still centered on `ParaPuzzlePieceAt`; not a new moving parapuzzle provider |
| `DynamicalPuzzlePiece` usages across the repo | Dynamical/fiber data | Dynamical pieces and containment statements | No formal bridge from moving dynamical puzzle boundaries to ambient parameter windows |
| `Mlc/BMolFilledJulia.lean` `BMolParameterFamily.connectednessLocus` | Family shell only | Connectedness locus inside a parameter family | No theorem identifying a finite parapuzzle family as such a BMol family with the required topology |
| `Mlc/AnalyticQuadraticLikeFamilyCore.lean` | Ambient analytic-family scaffold | Open parameter set, total spaces, section fibers | Still no finite parapuzzle construction, no basis theorem around fixed `c`, no Mandelbrot-slice connectedness theorem |
| Parameter graph / ray / equipotential declarations | Partial background | Names and some shell declarations exist | No checked theorem packages them into the sourced finite parapuzzle provider |

## The decisive blocker

The first missing formal theorem is:

> **Missing theorem.** A genuine finite-level phase–parameter / puzzle-boundary
> transport theorem: for each finitely renormalizable `c ∈ MandelbrotSet` and
> each sufficiently deep depth `n`, there exists an ambient open parameter window
> `W n` defined by moving puzzle boundaries, with `c ∈ W n`, such that
> `W n ∩ MandelbrotSet` is connected and these windows form a neighborhood basis
> at `c`.

In repo terms, this is the first missing theorem because:
- `PuzzleBoundaryMotionHyp` is currently only a packaging target, not an honest
  theorem built from existing checked mathematics;
- `PuzzleBoundaryMotion` currently derives transport witnesses from already known
  connectedness rather than proving connectedness from motion;
- no existing theorem constructs new finite parameter windows distinct from
  `ParaPuzzlePieceAt c n`;
- no checked phase–parameter identification links a new `W n` to a connected
  transport set.

## Smallest prerequisite module that must be built first

The smallest honest prerequisite module is a new source-side boundary-motion /
phase–parameter correspondence module proving something like:

```lean
theorem finite_parapuzzle_window_of_boundary_motion
    (c : ℂ) (hc : c ∈ MandelbrotSet) (hfin : FinitelyRenormalizable c) :
    ∃ W : ℕ → Set ℂ,
      (∀ n, IsOpen (W n)) ∧
      (∀ n, c ∈ W n) ∧
      (∀ U ∈ 𝓝 c, ∃ n, W n ⊆ U) ∧
      (∀ n, IsConnected (W n ∩ MandelbrotSet))
```

plus a theorem explaining **why `W n` is the correct moving parapuzzle object**,
e.g. by identifying it with the parameter locus where a finite combinatorial
boundary pattern persists under holomorphic motion.

Only after such a module exists would it make sense to add:
- a new `FiniteParapuzzleWindow` definition;
- elementary window lemmas;
- an adapter to `ConnectednessWindowParameterPieceData`;
- and finally an instance of `FiniteMovingWindowProviderData`.

## Why I did not edit the source

Task 61 explicitly prohibited:
- relabelling `ParaPuzzlePieceAt` as the new moving window;
- using the frontier axiom;
- introducing an opaque restatement of the target;
- continuing unrelated Böttcher-monodromy work.

Given the audit above, any source edit right now would have been speculative.
The repo lacks the first genuine sourced theorem, so there is no honest Lean code
change to make yet.

## Dependency status relative to Prompt 60

Prompt 60 established that the theorem-facing route is ready but the provider is
missing. Task 61 confirms that the situation remains unchanged:

- **consumer side:** complete;
- **provider side:** still absent;
- **new information from Task 61:** the exact first missing theorem is the
  finite-level phase–parameter / moving-boundary transport theorem.

So the root theorem should **not** be rerouted yet, and the frontier axiom should
**not** be deleted.

## Recommended next worker task

Build the smallest new source-side module formalizing a genuine finite-level
phase–parameter / boundary-motion theorem for finitely renormalizable quadratic
parameters, producing ambient open parameter windows with basis/shrinkage and
connected relative Mandelbrot slices; only then define the new finite parapuzzle
window object and instantiate `FiniteMovingWindowProviderData`.

## Validation

No source files were edited, so no build/test rerun was required.

## Full `git status --short`

```text
M Mlc/DirectRoute.lean
 M Mlc/MainConjecture.lean
?? plan/GPT54_PROMPT_59_ISOLATE_MOVING_WINDOW_MAIN_ROUTE.md
?? plan/GPT54_PROMPT_60_FINAL_MOVING_PROVIDER_FEASIBILITY_GATE.md
?? plan/GPT54_RESULT_24_PROVE_TUBE_FIBER_HOMEOMORPH_DISK.md
?? plan/GPT54_RESULT_59_ISOLATE_MOVING_WINDOW_MAIN_ROUTE.md
?? plan/GPT54_RESULT_60_FINAL_MOVING_PROVIDER_FEASIBILITY_GATE.md
?? plan/GPT54_TASK_59_ISOLATE_MOVING_WINDOW_MAIN_ROUTE.md
?? plan/GPT54_TASK_60_FINAL_MOVING_PROVIDER_FEASIBILITY_GATE.md
?? plan/GPT54_TASK_61_FORMALIZE_SOURCED_FINITE_PARAPUZZLE_PROVIDER.md
```

## Write/commit confirmation

- Repository source edits: **none**
- Result artifact written: **`plan/GPT54_RESULT_61_FORMALIZE_SOURCED_FINITE_PARAPUZZLE_PROVIDER.md` only**
- Commit made: **no**
