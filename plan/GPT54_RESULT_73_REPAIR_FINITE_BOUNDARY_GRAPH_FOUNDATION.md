# GPT-5.4 Result 73 — Repair finite boundary graph foundation

## Prompt executed

`@plan/GPT54_PROMPT_73_REPAIR_FINITE_BOUNDARY_GRAPH_FOUNDATION.md`

## Outcome

Prompt 73 was completed successfully.

I added a checked foundational module:

- `Mlc/Quadratic/Complex/FiniteParapuzzleBoundary.lean`

This repairs the exact blockers identified in Result 72 while staying within the
requested scope: finite continuous injective arcs, finite carriers, carrier
complements, selected complementary components, and refinement nesting.

## What was formalized

### 1. Concrete arc model

`BoundaryArc` is a genuine geometric object:

- `toFun : Set.Icc (0 : ℝ) 1 → ℂ`
- `continuous_toFun : Continuous toFun`
- `inj_toFun : Function.Injective toFun`

For each arc, the file proves:

- `carrier_eq_image`
- `isCompact_carrier`
- `isClosed_carrier`

The compactness proof uses the exact range/image normalization:
`range = image univ`, avoiding the unproved simp shortcut that blocked Prompt 72.

### 2. Finite graph carrier

`FiniteEmbeddedBoundaryGraph` stores a finite set of arcs, with carrier equal to
`⋃ γ ∈ arcs, γ.carrier`.

Closedness of the carrier is proved by an explicit `Finset.induction_on` via:

- `carrierFinset`
- `carrierFinset_empty`
- `carrierFinset_insert`
- `isClosed_carrierFinset`
- `isClosed_carrier`

So the finite-union blocker from Result 72 is repaired honestly.

### 3. Open selected complementary components in `ℂ`

The file proves:

- `isOpen_compl_carrier`
- `window := connectedComponentIn carrierᶜ z₀`
- `mem_window`
- `isOpen_window`
- `window_subset_compl_carrier`

For openness of selected components, I used the already-available repository fact
from `ParaPuzzleBasis.lean`:

- `complex_locally_connected : LocallyConnectedSpace ℂ`

This resolves the main structural blocker from Result 72 without any new axiom.

### 4. Selected-component nesting under refinement

The file proves:

- `window_subset_window_of_carrier_subset`

If `G.carrier ⊆ H.carrier` and the basepoint lies in both complements, then the
selected component for the refined graph `H` is contained in the selected
component for the coarser graph `G`.

This uses explicit intermediate subset lemmas:

- complement monotonicity from carrier inclusion;
- `window_subset_compl_carrier`;
- `IsPreconnected.subset_connectedComponentIn`.

So the nesting statement is now derived from actual component theory, not axiomatized.

### 5. Depth-indexed family packaging

The file also adds:

- `FiniteEmbeddedBoundaryGraphFamily`
- family `window`
- `isOpen_window`
- `mem_window`
- `RefinementData`
- `window_antitone_of_refinement`
- `ShrinkageData`

This is the exact finite-boundary scaffold needed for later parapuzzle work,
without yet claiming any phase–parameter semantics.

## What was not added

Per the prompt constraints, I did **not** add:

- Jordan separation;
- boundedness of complementary components;
- ray landing or wake structure;
- Mandelbrot connectedness;
- moving-window provider instantiations;
- phase–parameter transport;
- any new axiom / `sorry` / `admit`.

## Validation

Commands run successfully:

- `lake env lean Mlc/Quadratic/Complex/FiniteParapuzzleBoundary.lean`
- `lake build`
- `lake env lean check_axioms.lean`

## Files changed

- Added: `Mlc/Quadratic/Complex/FiniteParapuzzleBoundary.lean`
- Added: `plan/GPT54_RESULT_73_REPAIR_FINITE_BOUNDARY_GRAPH_FOUNDATION.md`
- Updated: `Mlc.lean`

## Next honest step

The next nontrivial step is not more abstract topology. It is to instantiate this
finite boundary-graph framework with actual quadratic parapuzzle boundary data
(angles/equipotentials/incidence/refinement), and only then connect it to the
existing moving-window/provider-facing interfaces.
