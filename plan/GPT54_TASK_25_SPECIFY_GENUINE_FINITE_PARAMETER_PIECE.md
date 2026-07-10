# GPT-5.4 Worker Task 25: Specify the genuine finite-level parameter piece

**Repository:** `/home/kir/pers/mlc`
**Mode:** read-only source and Lean-interface architecture audit
**Result file:** `plan/GPT54_RESULT_25_SPECIFY_GENUINE_FINITE_PARAMETER_PIECE.md`

## Safety

Write only the result report, via atomic rename. Do not edit Lean sources,
dependencies, plans, or prior artifacts; do not commit. Use `/tmp` for source text
and Lean signature probes.

Read:

- `plan/GPT54_PROGRESS_GREEN_SUBLEVEL_FRONTIER.md`;
- `plan/PLAN_04_parameter_connectivity.md`;
- Results 03, 05, 08, and 09;
- `Mlc/ParaPuzzleConnectivity.lean`;
- `Mlc/LcAtOfShrink.lean`.

Prompt 24 and the tube/renormalization sequence are suspended for this active path.

## Goal

Fix one genuine, independently defined finite-level **moving-parameter**
parapuzzle object that can replace the repository's frozen-base
`ParaPuzzlePieceAt` in the local-connectivity consumer. The object must be defined
from parameter geometry/combinatorics, not connectedness, exact-image existence,
or `G_c(c'-c)`.

## A. Choose one concrete classical construction

Directly inspect the strongest locally available primary/expository sources for a
finite-level parameter puzzle/parapuzzle piece. Prefer a construction with:

- a finite parameter graph made from parameter rays and an equipotential, or an
  explicitly equivalent wake/component definition;
- a component containing the chosen base parameter;
- a theorem giving disk/Jordan-domain/component topology;
- nesting as depth increases.

Give exact source locations, short quotes, hypotheses, parameter classes, and
level conventions. Do not say merely “standard parapuzzle piece.”

Choose exactly one construction as the repository target. Explain why it is the
smallest viable first model.

## B. Independent set definition

Write a precise mathematical definition of:

```text
ParameterGraph(base, depth)
ParameterPiece(base, depth)
```

The piece should be a connected component of a complement/domain determined by
the graph, or another equally independent source definition. State boundary,
open/closed convention, and whether the consumer should use the open component,
its closure, or its intersection with `MandelbrotSet`.

Do not define the piece by:

- `IsConnected` witnesses;
- an image of a connected source;
- the frozen Green function;
- equality to the desired downstream target.

## C. Theorem matching

Identify the exact sourced theorem(s) needed for:

1. the parameter component itself being connected/open/Jordan;
2. `ParameterPiece(base, depth) ∩ MandelbrotSet` being connected, if that stronger
   relative statement is actually available;
3. basepoint membership;
4. antitone nesting;
5. shrinkage or singleton intersection for the parameter class covered.

Distinguish elementary component topology from deep phase–parameter/Yoccoz input.
Do not attribute the frozen-base theorem to these sources.

## D. Lean-facing API and existing support

Audit Mathlib and the repository for:

- connected components of complements;
- component containing a point;
- parameter rays/equipotentials already formalized;
- parameter Böttcher coordinate `Φ_M` or usable partial substitutes;
- finite graph/set constructions;
- the exact requirements of `LcAtOfShrink`.

Give compile-oriented `def` signatures for the graph and piece, plus elementary
membership/component lemmas. Label every declaration as existing, elementary to
prove, sourced theorem to formalize, or missing foundation.

Do not add axioms or opaque structures whose fields are the desired conclusions.

## E. Migration plan

Trace the smallest code change that would let `LcAtOfShrink` consume the genuine
piece family instead of the frozen `ParaPuzzlePieceAt`. State whether to:

- generalize `LcAtOfShrink` over an abstract piece family with separately proved
  hypotheses;
- add a parallel theorem specialized to genuine parameter pieces;
- redefine the existing object.

Prefer the option that preserves proved generic topology while making the
classical geometric frontier explicit. List every theorem currently depending on
`green_sublevel_translate_inter_mandelbrot_connected` that would move to the new
interface.

## F. Bounded first implementation

Propose one first Lean implementation task that adds real, non-axiomatic progress:

- an independently defined finite parameter graph/piece shell from existing
  geometry, or
- a generic component-based parameter-piece consumer lemma needed by the chosen
  definition.

It must not merely rename the connectivity assumption.

Compile-test proposed signatures under `/tmp`.

## G. Decision

Choose exactly one:

1. a specific sourced parameter piece is ready for a small Lean definition task;
2. parameter-ray/equipotential foundations are the immediate missing layer;
3. a generic `LcAtOfShrink` migration should be implemented before geometry;
4. no verified classical object currently supports the required relative
   connectivity consumer.

Give the exact next worker task but do not create its file.

## Report contract

Include exact sources and commands, tested signatures, parameter-class limitations,
complete `git status --short`, and confirmation that only the result artifact was
written and no commit was made.
