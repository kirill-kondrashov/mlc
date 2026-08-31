# GPT-5.4 Result 68 — Abstract finite parapuzzle topology

## Prompt executed

`@plan/GPT54_PROMPT_68_ABSTRACT_FINITE_PARAPUZZLE_TOPOLOGY.md`

## Outcome

Honest hard stop. I did **not** make Lean source edits.

Prompt 68 asked for a reusable, geometric finite-level topology layer sitting
strictly before any Mandelbrot connectedness or phase–parameter transport claim.
That is the right next target. But the repository still lacks the first
non-opaque abstract objects needed to implement it honestly: an actual formal
model of finite embedded boundary arcs/graphs in the parameter plane and the
associated planar component-selection theorem.

So the correct result here is a precise blocker report, not a fake abstract
module.

## What Prompt 68 required

The task was to formalize only the abstract finite planar topology needed before
quadratic instantiation:

- finite embedded arcs/graphs or equivalent concrete boundary objects;
- admissible combinatorial regions built from those objects;
- selected parameter components/windows defined from the boundaries;
- proofs of openness, basepoint membership, nesting/refinement;
- a basis consequence from a separately supplied shrinkage hypothesis;
- **without** claiming Mandelbrot connectedness or using transport placeholders.

This means the output had to be a genuine abstract geometry layer, not merely:

- a repackaged `ConnectednessWindowParameterPieceData`;
- a renamed `parameterSet`;
- a `Set ℂ` plus assumed open/subset fields;
- or any placeholder “graph” with no proved topological content.

## What the repository already has

From the audit:

- Mathlib/repo support for `connectedComponentIn`, openness of connected
  components of open sets, and generic neighborhood/component lemmas.
- Existing repo lemmas using connected components of open sublevel sets, e.g.
  `GreenSublevelConnectedDirect.lean`, `ParaPuzzleConnectivity.lean`,
  `ParaPuzzleContainment.lean`, and `ParaPuzzleBasis.lean`.
- Existing theorem-facing family shells in `AnalyticQuadraticLikeFamilyCore`.

These are useful *after* one has a concrete boundary subset `Γ ⊆ ℂ` and a
window defined as a selected component of `Γᶜ` or of a bounded region cut out by
`Γ`.

What is missing is the source-side abstract object `Γ` together with proved facts
that it behaves like a finite embedded parapuzzle boundary.

## The key missing abstract object

Prompt 67 identified the next honest source module as a finite boundary module.
This audit confirms that result.

The first missing abstract object is something like:

```lean
structure FiniteEmbeddedBoundaryGraph where
  carrier : Set ℂ
  -- vertices / edges / incidence / embedding / no-crossing /
  -- Jordan-arc style attachment data
```

with enough proved content to support statements such as:

- `carrier` is closed;
- the complementary component containing a basepoint is open;
- if one graph refines another, then the selected component is nested;
- if a shrinkage hypothesis is supplied on the selected components, then they
  form a neighborhood basis.

The repository does **not** yet contain such an object.

## Why generic connected-component machinery is not enough

One might try to skip the missing finite graph model and define

```lean
window c₀ Γ := connectedComponentIn Γᶜ c₀
```

for an arbitrary `Γ : Set ℂ`.

This is not enough for Prompt 68, for two reasons.

### 1. It loses the finite geometric content

Prompt 68 explicitly requires finite embedded arcs/graphs or an equivalent
concrete boundary model. An arbitrary `Γ : Set ℂ` with no provenance is not a
finite parapuzzle boundary model.

### 2. The needed planar theorems are not automatic from arbitrary `Γ`

To use such a definition honestly, we would still need exact hypotheses proving:

- `Γᶜ` is open, so the selected component is open;
- the chosen component is the intended bounded/admissible region;
- refinement of the boundary implies nesting of selected components;
- the basepoint remains in the selected component under refinement.

Those are not consequences of “finite parapuzzle topology” unless the boundary
object itself records enough embedding/non-crossing/separation structure.

So a bare `Γ : Set ℂ` contract would just hide the missing mathematics.

## Exact missing topology theorem

Even after introducing a finite graph object, a specific planar theorem is still
needed.

A sufficient missing theorem is:

> **Finite embedded boundary component theorem.**
> Let `Γ ⊆ ℂ` be a finite embedded planar graph built from finitely many pairwise
> compatible embedded arcs, and let `c₀ ∉ Γ`. Then the connected component of
> `c₀` in `Γᶜ` is an open region determined by the graph; if `Γ'` is a refinement
> of `Γ` preserving the same basepoint-side choices, then the selected component
> for `Γ'` is contained in that for `Γ`.

This is exactly the theorem needed to support:

- `window_open`;
- `base_mem_window`;
- `window_nested` from refinement;
- later `basis` from a separately supplied shrinkage theorem.

The current repository has the generic component tools, but **not** this finite
embedded-boundary theorem specialized to a concrete graph/arc model.

## Why I did not add a new Lean structure anyway

I could have written a purely formal shell such as:

```lean
structure AbstractFiniteParapuzzleBoundary where
  boundary : Set ℂ
  window : ℂ → Set ℂ
  window_open : ...
  base_mem : ...
  nested : ...
```

But that would violate the prompt’s intent. It would merely restate the desired
conclusions while hiding the missing finite geometry in opaque fields.

Prompt 68 explicitly required the windows to be **constructed from** the finite
boundary/combinatorial model.

Without a real boundary model and separation theorem, such a structure would be
another consumer wrapper, not an honest abstract topology layer.

## Smallest honest module still needed first

The first missing module remains:

### `Mlc/Quadratic/Complex/FiniteParapuzzleBoundary.lean`

It should define, abstractly but concretely, the finite planar boundary objects:

1. finite embedded arcs / finite embedded graph data;
2. admissibility / no-crossing / endpoint compatibility;
3. a selected parameter window as the distinguished complementary component for
   a basepoint;
4. theorems that this selected window is open and contains the basepoint;
5. refinement data implying window nesting.

Only once this module exists does it become honest to add a reusable topology
contract on top of it.

## What Prompt 68 tells us about implementation order

This audit sharpens the Result 67 roadmap:

1. **Define the boundary object first**
   - not as an arbitrary `Set ℂ`, but as finite embedded graph/arc data.
2. **Prove the abstract planar component theorem**
   - complementary selected components are open and nest under refinement.
3. **Then define the abstract topology layer**
   - window construction, basepoint membership, nesting, basis under shrinkage.
4. **Only after that**
   - instantiate with quadratic combinatorics and then prove transport.

So Prompt 68 is blocked one step earlier than a reusable topology structure.

## Final verdict

Prompt 68 does **not** yet justify adding a new checked Lean module.

The exact blocker is:

- no formal finite embedded boundary graph/arc object;
- no proved finite-boundary complementary-component theorem yielding the
  distinguished open window and nesting under refinement.

Therefore the honest result is this blocker report, not source edits.

No Lean files were modified, and no build/check run was needed.