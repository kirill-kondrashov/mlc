# GPT-5.4 Result 67 — Source theorem and formal contract

## Prompt executed

`@plan/GPT54_PROMPT_67_SOURCE_THEOREM_AND_FORMAL_CONTRACT.md`

## Outcome

I completed the requested **source-first design pass** and did **not** make Lean
source edits. The correct output for this prompt is a precise source theorem
selection plus a nontrivial Lean contract for genuine moving parapuzzle data.

The repository is still missing the first foundational module needed to state and
construct this contract non-opaquely, so implementation should begin there rather
than by adding a fake provider wrapper.

## Selected classical source theorem

I select the **finite-level quadratic parapuzzle correspondence** in the
Douady–Hubbard / Yoccoz puzzle technology, in the standard finitely
renormalizable regime.

A usable mathematical formulation is:

> Let `c₀ ∈ M` be finitely renormalizable and non-parabolic, and choose a finite
> admissible puzzle depth `n` for the quadratic polynomial `f_{c₀}(z)=z^2+c₀`.
> Then there is a parameter parapuzzle neighborhood `P⁽par⁾_n(c₀)` whose boundary
> is formed by finitely many parameter rays and equipotential arcs with the same
> combinatorics as the dynamical puzzle boundary of depth `n`; these parapuzzle
> pieces are open, nested, and for sufficiently deep levels form a neighborhood
> basis at `c₀`. Moreover the phase–parameter correspondence identifies the
> dynamical puzzle motion with a parameter slice so that
> `P⁽par⁾_n(c₀) ∩ M` is connected.

This is the right source shape because Prompt 67 explicitly asks for:
- finite boundary graphs/arcs;
- admissibility/combinatorics;
- moving parameter windows;
- a concrete phase–parameter map/homeomorphism;
- connectedness as a transported conclusion.

## Public source family

A public source family for this theorem package is the standard Yoccoz /
Douady–Hubbard parapuzzle literature for quadratic polynomials, e.g.
expositions of:

- Yoccoz puzzle and parapuzzle shrinking for finitely renormalizable quadratic
  parameters;
- Douady–Hubbard holomorphic motion / λ-lemma transport of puzzle boundaries;
- parameter puzzle pieces bounded by parameter rays and equipotentials with the
  same finite combinatorics as the dynamical puzzle pieces.

Prompt 67 asked for one precise theorem choice. The precise theorem family to
formalize is therefore:

> **Finite parapuzzle theorem for finitely renormalizable quadratic parameters:**
> sufficiently deep admissible quadratic parapuzzle pieces exist, are open and
> nested, form a neighborhood basis at the base parameter, and have connected
> relative Mandelbrot slices via phase–parameter correspondence.

## Exact hypotheses to formalize

The source theorem is not for arbitrary opaque parameter domains. Its natural
hypotheses are finite combinatorial and geometric.

### Base hypotheses

For a base parameter `c₀ : ℂ`:

1. `hc₀ : c₀ ∈ MandelbrotSet`;
2. `hfin : FinitelyRenormalizable c₀`;
3. `hdepth : AdmissiblePuzzleDepth c₀ n` for the chosen finite level;
4. if needed by the selected source text, exclusion of parabolic/degenerate
   combinatorics at the chosen depth.

### Conclusion to capture

For each admissible depth `n`, construct a genuine moving parameter window
`W(c₀,n)` together with finite boundary/combinatorial data and a transport map,
such that:

1. `W(c₀,n)` is open;
2. `c₀ ∈ W(c₀,n)`;
3. windows are nested in `n`;
4. sufficiently deep windows form a neighborhood basis at `c₀`;
5. `W(c₀,n) ∩ MandelbrotSet` is connected;
6. the connectedness conclusion is justified by a concrete phase–parameter
   transport theorem, not by a separate axiom.

## The moving parameter windows

The prompt asked for the **definition** of the moving parameter windows, not just
an existential consumer wrapper.

The correct source-side definition is not `ParaPuzzlePieceAt c₀ n` and not an
ambient `parameterSet`. It is a finite parameter domain cut out by the moving
quadratic parapuzzle boundary data at depth `n`.

Mathematically, the window should be defined by finite boundary objects such as:

- finitely many external-angle labels/rational ray labels;
- finitely many parameter rays with those labels;
- one parameter equipotential level;
- boundary arcs joining the designated ray landing points according to the chosen
  combinatorial graph;
- the connected bounded complementary component selected by the admissible
  combinatorics and containing `c₀`.

In Lean terms, the window should be derived from explicit finite boundary data,
for example as the distinguished component of the complement of a finite boundary
graph.

## Exact phase–parameter transport statement

The transport theorem to expose is:

> for each admissible depth `n`, the finite dynamical puzzle boundary graph of
> `f_{c₀}` moves holomorphically over the parameter window `W(c₀,n)`, preserving
> the finite combinatorics; the induced phase–parameter map identifies the
> corresponding dynamical marked piece with the parameter parapuzzle slice, and
> this identifies `W(c₀,n) ∩ M` as a connected transport image / parameter
> component.

This is stronger and more concrete than the current repo’s
`PuzzleBoundaryMotionHyp`, which only packages an existential witness after
connectedness is already assumed.

## Why the current repo contracts are insufficient

### Existing consumer contract

The current theorem-facing endpoint is:

```lean
def FiniteMovingWindowProviderData : Prop :=
  ∀ (c : ℂ) (hc : c ∈ MandelbrotSet) (_h : FinitelyRenormalizable c),
    ∃ (W K : ℕ → Set ℂ), ConnectednessWindowParameterPieceData c W K
```

This is a **consumer** interface only. It does not expose:
- finite boundary graphs;
- admissibility/combinatorics;
- a window constructed from those graphs;
- a phase–parameter map/homeomorphism.

Prompt 67 explicitly forbids merely repackaging this interface.

### Existing family cores are too weak

`Molecule.AnalyticQuadraticLikeFamilyCore` provides:
- an open `parameterSet`;
- total source/target sets;
- fiberwise maps;
- joint analyticity on `totalU`.

It does **not** provide:
- finite parapuzzle boundary graphs;
- admissibility data;
- a distinguished parameter component/window around `c₀`;
- a theorem that the chosen window has connected Mandelbrot slice.

### Existing motion layer is circular

`Mlc/Quadratic/Complex/PuzzleBoundaryMotion.lean` defines theorem-facing shells,
but the key constructor

```lean
puzzleBoundaryMotionHyp_of_connected_data
```

builds motion packaging from already-assumed connectedness of
`ParaPuzzlePieceAt c n ∩ MandelbrotSet`.

So it is the wrong direction for a source theorem.

### Existing Böttcher motion layer is still placeholder-based

`Mlc/Quadratic/Complex/Bottcher/BottcherMotion.lean` still contains:

```lean
def homeomorphism_maps_component_hyp : Prop := True
def parameter_dynamics_stability_hyp : Prop := True
```

and a placeholder identity `bottcher_motion`.

So it cannot serve as the concrete phase–parameter correspondence contract
requested here.

## Proposed nontrivial Lean contract

The right contract should sit **before** `FiniteMovingWindowProviderData` and
feed it later via an adapter.

A suitable source-side contract is the following pair of structures.

### 1. Finite combinatorial boundary data

```lean
structure FiniteParapuzzleCombinatorics where
  depth : ℕ
  equipotentialLevel : ℝ
  externalAngles : Finset RationalAngle
  admissible : Prop
  noCrossing : Prop
  cyclicOrderCompatible : Prop
```

Purpose:
- records the finite labels defining the puzzle/parapuzzle boundary;
- separates actual combinatorics from topology and transport;
- forbids a fake “window = arbitrary open set” provider.

In a stricter implementation, `admissible`, `noCrossing`, and
`cyclicOrderCompatible` should ultimately be theorem-bearing predicates, not
opaque placeholders.

### 2. Source-side moving parapuzzle window contract

```lean
structure FiniteParapuzzleWindowData (c₀ : ℂ) where
  comb : ℕ → FiniteParapuzzleCombinatorics
  parameterGraph : ℕ → Set ℂ
  window : ℕ → Set ℂ
  markedPiece : ℕ → Set ℂ
  phaseParameterMap : ∀ n, markedPiece n → window n
  base_mem_window : ∀ n, c₀ ∈ window n
  window_open : ∀ n, IsOpen (window n)
  window_nested : ∀ {m n}, m ≤ n → window n ⊆ window m
  basis : ∀ U ∈ 𝓝 c₀, ∃ n, window n ⊆ U
  finite_graph_boundary : ∀ n, IsFiniteGraph (parameterGraph n)
  window_is_distinguished_component :
    ∀ n, IsDistinguishedParameterComponent c₀ (parameterGraph n) (window n)
  markedPiece_connected : ∀ n, IsConnected (markedPiece n)
  transport_homeomorph :
    ∀ n, Homeomorph (markedPiece n) (window n ∩ MandelbrotSet)
```

This is substantively different from `ConnectednessWindowParameterPieceData`
because it exposes:
- actual finite combinatorial data;
- a parameter boundary graph;
- a distinguished component/window construction;
- a concrete transport map/homeomorphism.

The connectedness of the Mandelbrot slice would then be derived, not stored as a
primitive field:

```lean
lemma inter_mandelbrot_connected
    (h : FiniteParapuzzleWindowData c₀) (n : ℕ) :
    IsConnected (h.window n ∩ MandelbrotSet)
```

by transporting connectedness across `h.transport_homeomorph n`.

## Why this contract satisfies Prompt 67

The prompt required all of the following, and the contract provides them:

- **finite boundary arcs/graph**:
  `parameterGraph`, `finite_graph_boundary`;
- **combinatorial/admissibility data**:
  `comb`, admissibility fields;
- **parameter-component/window construction**:
  `window_is_distinguished_component`;
- **concrete map/homeomorphism**:
  `phaseParameterMap`, `transport_homeomorph`;
- **connectedness transport conclusion**:
  derived from `markedPiece_connected` and `transport_homeomorph`.

So this is not merely `ConnectednessWindowParameterPieceData` with renamed fields.

## Adapter to the existing theorem-facing route

Only **after** the above source contract exists should we add an adapter:

```lean
lemma connectednessWindowData_of_finiteParapuzzleWindowData
    {c₀ : ℂ} (h : FiniteParapuzzleWindowData c₀) :
    ∃ K : ℕ → Set ℂ,
      ConnectednessWindowParameterPieceData c₀ h.window K
```

with the natural choice `K n := h.window n` or, if needed by later architecture,
`K n := h.window n ∩ MandelbrotSet` repackaged appropriately.

The important point is: the adapter is a *downstream projection* from genuine
finite geometry, not the definition of that geometry.

## Smallest first missing foundational module

The selected contract cannot yet be implemented honestly because the repository
still lacks the first source-side module that defines finite parameter boundary
graphs and their admissibility.

The smallest missing module is:

### `Mlc/Quadratic/Complex/FiniteParapuzzleBoundary.lean`

This module should introduce the non-opaque source objects:

1. rational-angle / finite ray-label combinatorics used at a fixed puzzle depth;
2. finite parameter boundary graph built from parameter rays and equipotential
   arcs;
3. distinguished component/window selected by a base parameter `c₀`;
4. admissibility/non-crossing/cyclic-order statements for that graph.

Without this module, the contract above has nowhere to source these fields from.

## Second missing module after that

Once finite boundary graphs exist, the next smallest source module is:

### `Mlc/Quadratic/Complex/FiniteParapuzzleTransport.lean`

This should prove the genuine phase–parameter theorem:

- moving finite puzzle boundary over the window;
- induced map/homeomorphism from the marked dynamical piece to the relative
  Mandelbrot slice;
- connectedness transfer for `window n ∩ MandelbrotSet`.

This is exactly the theorem that current `PuzzleBoundaryMotion` and
`BottcherMotion` do not yet supply.

## Recommended implementation order

1. **Finite boundary objects**
   - define rational-angle labels and finite parapuzzle combinatorics;
   - define parameter boundary graphs and distinguished windows.
2. **Topological contract**
   - define `FiniteParapuzzleWindowData` on top of those objects.
3. **Transport theorem**
   - prove a source theorem producing `FiniteParapuzzleWindowData c₀` from the
     classical finite parapuzzle package for finitely renormalizable `c₀`.
4. **Adapter**
   - project to `ConnectednessWindowParameterPieceData`.
5. **Provider**
   - instantiate `FiniteMovingWindowProviderData`.

## Final verdict

Prompt 67 is complete as a design/sourcing task.

- I selected the source theorem family: finite-level quadratic parapuzzle
  correspondence for finitely renormalizable parameters.
- I specified the exact hypotheses/conclusions to formalize.
- I gave the moving-window definition strategy from finite boundary graphs.
- I proposed a nontrivial Lean contract exposing real finite geometry and a
  transport homeomorphism.
- I identified the first missing foundational module:
  `Mlc/Quadratic/Complex/FiniteParapuzzleBoundary.lean`.

No Lean source edits were made, because the repository still lacks this first
foundation and Prompt 67 prohibited speculative stubs.