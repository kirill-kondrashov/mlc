# GPT-5.4 Result 60 — Final moving-provider feasibility gate

## Verdict

No honest checked theorem in the current repository constructs

```lean
FiniteMovingWindowProviderData :=
  ∀ c hc hfin, ∃ W K, ConnectednessWindowParameterPieceData c W K
```

for finitely renormalizable `c ∈ MandelbrotSet` without using the frozen
parameter-puzzle frontier. Therefore **no source edit is justified** at this step,
and the frontier axiom

- `green_sublevel_translate_inter_mandelbrot_connected_straddling`

**cannot be deleted now**.

The repository now has the **consumer side** and the **theorem-facing moving-window
route**, but it still lacks a checked **provider theorem** producing a genuine open,
shrinking, Mandelbrot-connected moving parameter-window family.

## Exact dependency status of `MLC.mlc_conjecture`

The theorem-facing migration is real:

- `Mlc/LcAtOfShrink.lean` defines the generic consumer interfaces
  `ConnectednessWindowParameterPieceData` and `ConnectednessLocusWindowFamilyData`.
- `Mlc/InfinitelyRenormalizable.lean` already consumes that interface on the finite side.
- `Mlc/MainConjecture.lean` now exposes
  `FiniteMovingWindowProviderData`,
  `finite_lc_provider_of_movingWindowData`, and
  `mlc_strategy_of_movingWindowData`.
- `Mlc/DirectRoute.lean` packages the same theorem-facing route directly.

But the actual root route still depends on the old source theorem:

- `Mlc/MainConjecture.lean` imports `Mlc.ParaPuzzleConnectivity`
- `Mlc.ParaPuzzleConnectivity.lean` proves
  `para_puzzle_connectivity_data_proved`
- that proof still depends on
  `green_sublevel_translate_inter_mandelbrot_connected_straddling`
- and `Mlc/AxiomsMainConjecture.lean` only gives
  `parameter_shrink_of_yoccoz`, i.e. shrinkage for `ParaPuzzlePieceAt`, not a new
  moving-window provider.

So the checked dependency chain is still:

```lean
MLC.mlc_conjecture
  ← finite-side LC from para-puzzle connectedness + para-puzzle shrinkage
  ← para_puzzle_connectivity_data_proved
  ← green_sublevel_translate_inter_mandelbrot_connected_straddling
```

Prompt 59 isolated a theorem-facing replacement seam, but Prompt 60 finds that the
source-side provider has not yet been built.

## What the target provider actually requires

`ConnectednessWindowParameterPieceData c W K` in `Mlc/LcAtOfShrink.lean` requires:

1. `window_open : ∀ n, IsOpen (W n)`
2. `base_mem_window : ∀ n, c ∈ W n`
3. `basis : ∀ U ∈ 𝓝 c, ∃ n, W n ⊆ U`
4. `locus_subset_window : ∀ n, K n ⊆ W n`
5. `inter_mandelbrot_connected : ∀ n, IsConnected (W n ∩ MandelbrotSet)`

For Prompt 60, the key issue is not defining `W` abstractly but producing all of
(1)–(5) for a **genuine moving parameter window family**, not a renamed
`ParaPuzzlePieceAt` shell and not a theorem whose connectedness still comes from the
frontier axiom.

## Candidate audit

| Candidate | Classification | What it gives | Why it does **not** close the provider |
|---|---|---|---|
| `ConnectednessWindowParameterPieceData` / `ConnectednessLocusWindowFamilyData` in `Mlc/LcAtOfShrink.lean` | Abstract consumer interface only | Precisely the target fields consumers need | Merely restates the goal; no theorem instantiates it for finitely renormalizable Mandelbrot parameters |
| `finiteMovingParameterWindow F := F.parameterSet` in `Mlc/LcAtOfShrink.lean` | Valid ambient-window ingredient only | An ambient set attached to a `BMolParameterFamily` level | Supplies only the domain shell; no openness theorem for BMol families, no basis/shrinkage, no relative Mandelbrot connectedness |
| `analyticCoreFiniteMovingParameterWindow F := F.parameterSet` + `isOpen_analyticCoreFiniteMovingParameterWindow` | Valid ambient-window ingredient only | Honest open parameter domains for `AnalyticQuadraticLikeFamilyCore` | Still no depth-indexed shrinking family around a given `c`, no basis theorem, no theorem that `F.parameterSet ∩ MandelbrotSet` is connected |
| `BMolParameterFamily.connectednessLocus` in `Mlc/BMolFilledJulia.lean` | Dynamical/fiber data only | A locus `{a ∈ parameterSet | FilledJuliaConnected (F.map a)}` | Pure intrinsic BMol connectedness-locus shell; no openness, no neighborhood basis, no phase–parameter identification with Mandelbrot slices |
| `AnalyticQuadraticLikeFamilyCore` in `Mlc/AnalyticQuadraticLikeFamilyCore.lean` | Dynamical/fiber data only | Open parameter set, total source/target sets, joint analyticity of `eval` on total source | Fiber-family analytic scaffolding only; no local parameter-piece theorem near a finitely renormalizable Mandelbrot parameter |
| `parameter_shrink_of_yoccoz` in `Mlc/AxiomsMainConjecture.lean` | Frozen para-puzzle wrapper | Neighborhood-basis/shrinkage for `ParaPuzzlePieceAt c n` after dynamical shrinkage | It proves shrinkage only for the old para-puzzle pieces; it does not construct a new moving family `W n` |
| `PuzzleLemmas2.lean` (`para_puzzle_piece_open`, `para_puzzle_piece_basis`) | Frozen para-puzzle wrapper | Openness and neighborhood basis for `ParaPuzzlePieceAt c n` | This is exactly the old family under its original name; using it would violate Prompt 60’s rejection criteria |
| `PuzzleBoundaryMotion.lean` witness/transport scaffolding | Missing decisive phase–parameter theorem | Names the desired motion-based bridge shape | Current constructors are either trivial shell/witness packaging or ultimately feed from para-puzzle connectedness; no checked nontrivial motion theorem yields `W n ∩ M` connected |
| `ParaPuzzleConnectivity.lean` (`green_sublevel_translate_connected`, subset/superset strata) | Partial topology ingredient, but still frozen at the frontier | Gives connectivity of the untranslated parameter Green sublevel and discharges trivial subset/superset cases | The remaining straddling case is still exactly the frontier axiom; so any provider extracted here still depends on the frozen source |
| Parameter graph/ray/equipotential/component declarations searched during audit | Missing decisive topology theorem | Some ambient parameter/dynamical constructions exist elsewhere in the repo | No checked theorem was found packaging them into open shrinking windows with `W n ∩ MandelbrotSet` connected near arbitrary finitely renormalizable basepoints |

## Why no honest provider can be derived now

The audit found **pieces of the provider**, but never the full source theorem.
Concretely:

- There are honest **open parameter domains** (`AnalyticQuadraticLikeFamilyCore.parameterSet`).
- There are honest **family/locus shells** (`BMolParameterFamily.connectednessLocus`).
- There is an honest **generic consumer route** for any `ConnectednessWindowParameterPieceData`.
- There is still honest **para-puzzle shrinkage** and an old finite-side route.

What is missing is the decisive theorem of the form:

```lean
∀ c hc hfin, ∃ W K,
  ConnectednessWindowParameterPieceData c W K
```

where `W` is not `ParaPuzzlePieceAt`, and where `inter_mandelbrot_connected` is proved
without the straddling frontier axiom.

More explicitly, no existing checked module provides all of:

- a depth-indexed family `W n` of **ambient open** parameter windows,
- `c ∈ W n` for all `n`,
- a **basis/shrinkage theorem** `∀ U ∈ 𝓝 c, ∃ n, W n ⊆ U`,
- and **connectedness of `W n ∩ MandelbrotSet`**,
- with a genuine moving/family interpretation rather than the para-puzzle family.

The first hard missing theorem is therefore:

> **A finite moving-window provider theorem** constructing a genuine shrinking local
> parameter-window family around each finitely renormalizable Mandelbrot parameter,
> together with connectedness of the relative Mandelbrot slices.

Without that theorem, the new moving-window route remains only theorem-facing plumbing.

## Quantitative frontier statement

At this point:

- the **consumer migration is complete**;
- the **main/direct moving-window route exists**;
- the **provider derivation is absent**;
- therefore the non-core frontier **does not shrink**.

So the current frontier remains unchanged:

1. `green_sublevel_translate_inter_mandelbrot_connected_straddling`
2. `residualOpenVirtualNearMoleculeAxiom`

Prompt 60 does **not** justify deleting frontier item 1.

## Shortest honest next route

The shortest honest next route is **not** another wrapper. It is to prove the
source theorem that the new seam expects.

In practical terms, the next real mathematical target is:

1. construct a genuine moving parameter-window family near each finitely
   renormalizable `c ∈ MandelbrotSet`;
2. prove those windows are open and shrink to `c`;
3. prove each `W n ∩ MandelbrotSet` is connected;
4. only then instantiate `FiniteMovingWindowProviderData` and reroute
   `MLC.mlc_conjecture` through `mlc_strategy_of_movingWindowData`.

Given the current codebase, this looks equivalent in difficulty to supplying the
missing phase–parameter / parameter-puzzle connectedness theorem, not a small Lean
refactor.

## Action taken

Per task instructions, I made **no speculative source edits** and did not add any axiom,
wrapper, or fake provider theorem.
