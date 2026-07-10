# GPT-5.4 Result 09: Specify the canonical Option B parameter piece

## 1. Executive decision

**Decision:** **(2) specification ready but one source theorem must be pinned more precisely.**

I can now give a non-circular **Option B** specification based on a genuine
finite-level **parameter window / parapuzzle piece** rather than the current
frozen translate
`ParaPuzzlePieceAt c n = {c' | c' - c ∈ DynamicalPuzzlePiece c n 0}`.

The right first object is:

- a **finite parameter boundary graph** made from two parameter rays landing at a
  root, two parameter rays landing at a tip, and two parameter equipotential arcs;
- the **open connected component** of its complement/domain containing the base
  parameter;
- in the first restricted milestone, the **renormalization window** `W◦` of
  Lyubich’s canonical almost renormalization setup.

This is source-backed by Lyubich’s parameter-window discussion and holomorphic
motion of the boundary configuration, but I still need one more page-precise
primary-source pin for the exact “distinguished component / boundary graph”
formulation to avoid over-claiming a theorem name for the component definition
itself.

So the architecture is ready; the last missing item is a sharper source pin, not a
mathematical redesign.

## 2. Selected construction and exact source

### 2.1 Selected classical construction

I choose the **complex renormalization window** around a hyperbolic quadratic map
of period `p > 1` from Lyubich’s exposition.

### 2.2 Base parameter class

- base parameter `c₀` in a **hyperbolic component** `H◦` of period `p > 1`;
- initially restrict to the **primitive** case when needed to avoid root-side
  degeneracy;
- depth data are the finite ray/equipotential truncation data used in the
  canonical almost renormalization picture.

This is explicitly away from the virtual-near-neutral / unbounded-satellite
regimes highlighted in `2512.24171`.

### 2.3 Primary sources actually pinned

#### Source A
- **M. Lyubich**, *Conformal Geometry and Dynamics of Quadratic Polynomials*
- local file: `refs/Conformal Geometry and Dynamics of Quadratic Polynomials.pdf`
- pinned location: **Chapter 7, §45.2.1 “Complex windows”**, PDF page labeled near
  **206**, with **Proposition 7.41** and **Proposition 7.42**.
- local extract confirms:
  - “This domain is bounded by two parameter rays … and two … rays … truncated
    by the equipotential …”
  - Proposition 7.41: the boundary configuration “moves holomorphically over the
    parameter window `W◦`.”
  - Proposition 7.42: for `c ∈ W◦`, the maps are renormalizable with period `p`.

#### Source B
- same file, **§29.2** on parameter uniformization / phase-parameter relation.
- local extract confirms parameter external coordinates are defined through the
  parameter Böttcher map and matched with dynamical external coordinates of the
  moving map.
- role: this is the source backing for the **parameter rays / equipotentials** as
  genuine parameter-plane objects.

#### Source C
- `refs/2512.24171v1.pdf`
- pinned passage around lines `919–934`
- role: modern roadmap confirmation that the intended machine is **puzzle ↔ parapuzzle**,
  especially the “Almost-Linear puzzle-parapuzzle relation [37]”, and that the
  remaining hard cases are near-neutral / virtual Molecule rather than the basic
  finite hyperbolic window setup.

### 2.4 Faithful hypothesis/conclusion split

What Source A gives directly:
- existence of an **open parameter domain** `W◦` bounded by a finite graph of
  parameter rays and equipotential arcs;
- holomorphic motion of the finite boundary configuration over that domain;
- renormalizability of all parameters in that window.

What follows **by definition** once we choose the canonical component:
- `W◦` is connected if we define it as **the distinguished connected component** of
  the complement/domain bounded by that finite graph and containing `c₀`.

What still needs a sharper source pin:
- the exact theorem/page in a primary source where the **component containing the
  base parameter** is identified in a way I can cite directly as the canonical
  finite-level parameter piece, rather than only as prose around the window.

## 3. Mathematical definition stack

## 3.1 Why the current object is wrong for Option B

Current Lean object:

```lean
def ParaPuzzlePieceAt (c : ℂ) (n : ℕ) : Set ℂ :=
  {c' | c' - c ∈ DynamicalPuzzlePiece c n 0}
```

This is a **translated fixed-map dynamical piece**. It is not a genuine parameter
piece because membership is tested using the frozen map `f_c`, not the moving
parameter `c'`.

Task 08 already established that the literature naturally talks about parameter
objects built from:
- parameter rays/equipotentials defined by `Φ_M(c')`;
- moving ray portraits and parapuzzle boundary graphs;
- distinguished parameter domains / windows.

So Option B needs a new object whose **ambient plane and defining data are already
parameter-plane data**.

## 3.2 Canonical definition stack

I recommend the following stack.

### Layer 0: external parameter coordinate data
A parameter external coordinate / Böttcher map on `ℂ \ M`, enough to define:
- parameter rays at rational angles;
- parameter equipotential arcs at fixed potential level;
- landing points / truncation endpoints where already sourced.

### Layer 1: finite parameter boundary graph
For admissible finite combinatorics `κ` and truncation level `t > 0`, define a
finite set of boundary pieces:
- two parameter rays landing at the **root**,
- two parameter rays landing at the **tip**,
- two parameter equipotential arcs truncating the rays,
- optionally packaged as a finite indexed family of arcs.

This graph is defined independently of connectedness.

### Layer 2: ambient cut domain
Define the complement/domain cut by that graph, e.g. a set `ParameterWindowDomain κ t`.

### Layer 3: canonical component-based parameter piece
Define:
- `GenuineParaPuzzlePieceAt c₀ κ t := connectedComponentIn (ParameterWindowDomain κ t) c₀`,
  or equivalently the distinguished component containing `c₀`.

This is allowed by the task contract: connectedness is not assumed as a theorem
field; it comes from the fact that a connected component is connected by general
topology.

### Layer 4: closure / openness / compact truncation facts
Prove for the canonical piece:
- connectedness by component construction;
- openness if the ambient cut domain is open;
- relative compactness / compact closure when the boundary graph is truncated by
  equipotentials and lies in a bounded region.

### Layer 5: nested-family / shrink theorem
For a fixed admissible combinatorial class near `c₀`, increasing depth should
produce a nested family whose intersection is `{c₀}` in the restricted regime.
That is the exact replacement for the downstream shrink basis presently consumed by
`LcAtOfShrink`.

## 4. Lean-facing signatures with dependency labels

Below are **proposed signatures only**.

### 4.1 External parameter geometry

```lean
namespace MLC.Quadratic

constant ParameterExternalCoord : Set ℂ
constant parameterRay : Angle → Set ℂ
constant parameterEquipotential : ℝ → Set ℂ

end MLC.Quadratic
```

Better Lean shape:

```lean
constant parameterRay      : RationalAngle → Set ℂ
constant parameterArc      : RationalAngle → ℝ → Set ℂ
constant parameterLevelSet : ℝ → Set ℂ
```

Dependency labels:
- `parameterRay`, `parameterEquipotential`:
  **genuinely missing definition** in repo.
- external-coordinate existence/regularity:
  **sourced classical theorem to formalize**.
- topology of level/ray pieces:
  partly **existing Mathlib API** once the maps exist.

### 4.2 Finite boundary graph

```lean
structure FiniteParameterBoundaryGraph where
  support : Set ℂ
  isFiniteUnionOfArcs : Prop
  rootAngles : RationalAngle × RationalAngle
  tipAngles  : RationalAngle × RationalAngle
  level      : ℝ
```

or more explicit and Lean-friendly:

```lean
structure FiniteParameterBoundaryGraph where
  rootRayLeft  : Set ℂ
  rootRayRight : Set ℂ
  tipRayLeft   : Set ℂ
  tipRayRight  : Set ℂ
  lowerEquipotential : Set ℂ
  upperEquipotential : Set ℂ
  support : Set ℂ
  support_def :
    support = rootRayLeft ∪ rootRayRight ∪ tipRayLeft ∪ tipRayRight ∪
      lowerEquipotential ∪ upperEquipotential
```

Dependency labels:
- structure itself: **genuinely missing definition**.
- “these pieces are parameter rays/equipotentials”: **sourced classical theorem to formalize**.
- local finiteness / closedness of support: mix of **existing Mathlib API** plus
  source-backed geometry.

### 4.3 Canonical component-based piece

```lean
constant ParameterWindowDomain : FiniteParameterBoundaryGraph → Set ℂ

def GenuineParaPuzzlePieceAt (c₀ : ℂ) (G : FiniteParameterBoundaryGraph) : Set ℂ :=
  connectedComponentIn (ParameterWindowDomain G) c₀
```

Dependency labels:
- `ParameterWindowDomain`: **genuinely missing definition**.
- `GenuineParaPuzzlePieceAt`: **genuinely missing definition**, but topological API
  is standard.

### 4.4 Topological facts with no packaging axiom

```lean
theorem genuineParaPuzzlePiece_connected
    (hc₀ : c₀ ∈ ParameterWindowDomain G) :
    IsConnected (GenuineParaPuzzlePieceAt c₀ G)

theorem genuineParaPuzzlePiece_subset_domain :
    GenuineParaPuzzlePieceAt c₀ G ⊆ ParameterWindowDomain G

theorem genuineParaPuzzlePiece_open
    (hopen : IsOpen (ParameterWindowDomain G)) :
    IsOpen (GenuineParaPuzzlePieceAt c₀ G)
```

Dependency labels:
- connectedness/subset/openness of connected components:
  **existing Mathlib API** / standard topology.
- openness of `ParameterWindowDomain G` from the boundary graph:
  mostly **existing Mathlib API** once the graph is defined.

### 4.5 Compact-closure / boundedness facts

```lean
theorem isBounded_parameterWindowDomain
    (htruncated : TruncatedByEquipotential G) :
    IsBounded (ParameterWindowDomain G)

theorem isCompact_closure_genuineParaPuzzlePiece
    (hopen : IsOpen (ParameterWindowDomain G))
    (htruncated : TruncatedByEquipotential G) :
    IsCompact (closure (GenuineParaPuzzlePieceAt c₀ G))
```

Dependency labels:
- boundedness from finite ray truncation by equipotentials:
  **sourced classical theorem to formalize** plus routine analysis/topology.

### 4.6 Exact `LcAtOfShrink`-facing abstraction

Smallest reusable abstraction I would introduce:

```lean
structure CanonicalParameterPieceFamily (c₀ : ℂ) where
  piece : ℕ → Set ℂ
  mem_base : ∀ n, c₀ ∈ piece n
  isOpen_piece : ∀ n, IsOpen (piece n)
  connected_inter_M : ∀ n, IsConnected (piece n ∩ MandelbrotSet)
  antitone : Antitone piece
  shrink : (⋂ n, piece n) = {c₀}
```

This is the smallest honest abstraction for downstream use.
It exposes concrete neighborhood-family data and **does not** hide the target
statement inside a renamed witness bundle.

Dependency labels:
- structure itself: **genuinely missing definition**.
- topological fields: reusable from repo / Mathlib.
- `connected_inter_M` and `shrink` for a genuine parapuzzle family:
  **sourced classical theorem to formalize** in the restricted regime.
- full unrestricted global version: partly **open mathematics** because the full
  MLC program still reaches virtual near-Molecule / unbounded satellite problems.

## 5. Downstream consumer / migration table

### 5.1 Purely topological and reusable after set-family swap

| file | declarations | classification | migration |
| --- | --- | --- | --- |
| `Mlc/LcAtOfShrink.lean` | `LocallyConnectedAt`, `locallyConnectedSpace_of_locallyConnectedAt`, `lc_at_of_shrink_of_connected_at` | purely topological | generalize from `ParaPuzzlePieceAt` to a `CanonicalParameterPieceFamily` |
| `Mlc/Quadratic/Complex/ParaPuzzleBasis.lean` | openness / compact-closure / antitone / basis lemmas | reusable proof shape, but current proofs depend on frozen translate identity | keep theorem shapes, reprove for genuine pieces |
| `Mlc/Quadratic/Complex/PrincipalNest*.lean` consumers using only antitone/intersection-to-point | mostly reusable | switch to new family once shrink theorem exists |

### 5.2 Dependent on the frozen translation identity

| file | declarations | why frozen-dependent | status |
| --- | --- | --- | --- |
| `Mlc/ParaPuzzleConnectivity.lean` | `mem_paraPuzzlePieceAt_iff_green`, `paraPuzzlePieceAt_eq_green_translate`, all `green_sublevel_translate_*` theorems | these identify the current parameter object with translated fixed-map Green sublevels | **off the Option B path**; keep only as legacy/bridge if needed |
| `Mlc/Quadratic/Complex/ParaPuzzle.lean` | `ParaPuzzlePieceAt` definition itself | wrong ambient definition for genuine parameter pieces | replace or leave as `FrozenParaPieceAt` legacy object |
| `Mlc/Quadratic/Complex/ParaPuzzleBasis.lean` | current boundedness proof via translated dynamical sublevel | uses frozen translate equality | rework around genuine parameter windows |

### 5.3 Dependent on dynamical puzzle containment

| file | declarations | classification | migration |
| --- | --- | --- | --- |
| `Mlc/ParaPuzzleContainment.lean` | containment facts coming from `K(c)` and dynamical puzzle pieces | tied to the old translated/frozen model | likely legacy/off-path for Option B |
| any `PrincipalNestShrink` proof using `ParaPuzzlePieceAt` from dynamical data | dependent on old mediator | needs replacement by source-backed parameter shrink theorem |

### 5.4 Axiom / transport packaging to retire

| file | declarations | classification | action |
| --- | --- | --- | --- |
| `Mlc/Quadratic/Complex/PuzzleLemmas2.lean` | `ParaPuzzlePieceInterMandelbrotConnectedData`, `ParaPuzzleMandelbrotSubsetData`, `ParaPuzzleInterMandelbrotTransportData`, `...ExistsData` | retired packaging route | do not extend; phase out once genuine family abstraction exists |
| `Mlc/Quadratic/Complex/PuzzleBoundaryMotion.lean` | witness packages built from the target theorem | packaging / historical route | off-path for Task 09 target |
| `Mlc/Quadratic/Complex/Bottcher/Slodkowski.lean` | `ParaPieceIsMotionImage` | explicitly banned by task contract | retire from main plan |
| `Mlc/ParaPuzzleCarvingReduction.lean` | `ParaPieceCarvedByMotion` | explicitly banned by task contract | retire from main plan |

### 5.5 Unrelated / off-path

`MainConjecture`, `AxiomsMainConjecture`, molecule/satellite files are downstream
consumers of the **shrink + connected neighborhood** output, but not of the exact
frozen Green-translate identity. They should survive a clean family abstraction.

## 6. First restricted milestone and feasibility

## 6.1 Proposed milestone theorem

> **Restricted milestone:** For a primitive hyperbolic base parameter `c₀` of
> period `p > 1`, the finite renormalization-window piece `W◦(c₀,t)` defined by the
> four parameter rays and two parameter equipotential arcs of Lyubich §45.2.1 is a
> canonical open connected parameter neighborhood of `c₀` with compact closure.

Lean-shape sketch:

```lean
theorem primitive_window_connected_open
    (hc₀ : IsPrimitiveHyperbolicBase c₀)
    (ht : AdmissibleTruncation c₀ t) :
    IsOpen (GenuineParaPuzzlePieceAt c₀ (primitiveWindowGraph hc₀ t)) ∧
    IsConnected (GenuineParaPuzzlePieceAt c₀ (primitiveWindowGraph hc₀ t)) ∧
    IsCompact (closure (GenuineParaPuzzlePieceAt c₀ (primitiveWindowGraph hc₀ t)))
```

## 6.2 Why this is the right first milestone

- canonically defined target;
- no circular connectivity premise;
- directly sourced by a classical finite parameter window;
- validates the new parameter-plane interface before global shrinkage is attempted;
- matches the repo’s actual need: a nested connected neighborhood family, not an
  exact frozen translate theorem.

## 6.3 Proof outline

1. Use parameter external coordinates (`§29.2`) to define the four rays and two
   equipotential arcs.
2. Form the finite boundary graph.
3. Define the domain cut by that graph; select the component containing `c₀`.
4. Connectedness is immediate from component construction.
5. Openness follows because the cut domain is open.
6. Compact closure follows from truncation by equipotential arcs and boundedness of
   the window.
7. Proposition 7.41 / 7.42 justify that this is the correct renormalization window
   associated to the finite combinatorics.

## 6.4 Downstream validation theorem

The first consumer should be a generalized replacement for the current
`lc_at_of_shrink_of_connected_at` pipeline, but initially only at the level:

```lean
theorem primitive_window_has_connected_nhd
```

for one explicit `c₀`. That validates the family API without demanding the full
intersection-to-point theorem.

## 6.5 Feasibility

**Feasibility:** **medium** for the first topological piece object;
**low-medium** for a full nested shrink theorem.

### First likely Lean blocker

Not connectivity. The first blocker is the **parameter-ray / parameter-equipotential
object layer** itself: the repo currently lacks a bona fide parameter external
coordinate API. Without that, the new parameter boundary graph cannot even be
stated naturally.

## 7. Blockers and final decision

### 7.1 Non-blocking architecture conclusion

There is **no architecture mismatch** anymore. The right object is a genuine
parameter-plane component cut out by finite parameter boundary data.

### 7.2 Remaining source blocker

The exact missing pin is:
- a page-precise primary-source statement or passage giving the **distinguished
  parameter domain / component containing the base parameter** in a form close to
  the Lean definition I propose.

Lyubich’s §45.2.1 is enough to justify the window picture and the finite boundary
configuration, but I still want a tighter citation for the step “take the component
containing `c₀`” before calling the specification completely source-complete.

Hence decision **(2)** rather than **(1)**.

## 8. Proposed next worker task

**Next worker task:**

Pin the best primary-source theorem/passage for the canonical finite-level
parameter window / parapuzzle component containing the base parameter, then draft
`ParameterExternalCoord`, `FiniteParameterBoundaryGraph`,
`GenuineParaPuzzlePieceAt`, and `CanonicalParameterPieceFamily` signatures in a
plan/result artifact without editing Lean.

Concretely, the worker should search first in:
- Lyubich Astérisque 261 parapuzzle paper `[37]`;
- Douady–Hubbard Orsay parapuzzle / polynomial-like references;
- Yoccoz/Hubbard expository sources cited in the repo.

## 9. Exact searches / commands / tool limits

Commands/searches used in this task:

```bash
pdftotext 'refs/Conformal Geometry and Dynamics of Quadratic Polynomials.pdf' - | \
  grep -niE 'parapuzzle|parameter puzzle|parameter piece|Yoccoz puzzle|wake|component' | head -n 80

pdftotext 'refs/Conformal Geometry and Dynamics of Quadratic Polynomials.pdf' - | \
  sed -n '10590,10730p'

pdftotext 'refs/2512.24171v1.pdf' - | sed -n '900,960p'

git --no-pager status --short
rg -n 'ParaPuzzlePieceAt|green_sublevel_translate_inter_mandelbrot_connected|ParaPieceCarvedByMotion|ParaPieceIsMotionImage' Mlc/**/*.lean
```

Files read:
- `plan/GPT54_TASK_09_SPECIFY_CANONICAL_PARAMETER_PIECE.md`
- `plan/GPT54_RESULT_08_SOURCED_THEOREM_MATCHING_AUDIT.md`
- `Mlc/Quadratic/Complex/ParaPuzzle.lean`
- `Mlc/LcAtOfShrink.lean`
- `Mlc/Quadratic/Complex/PuzzleLemmas2.lean`
- `Mlc/ParaPuzzleConnectivity.lean`
- `Mlc/ParaPuzzleCarvingReduction.lean`
- `Mlc/Quadratic/Complex/ParaPuzzleBasis.lean`
- `Mlc/MainConjecture.lean`
- `Mlc/AxiomsMainConjecture.lean`
- `Mlc/ParaPuzzleContainment.lean`
- `Mlc/Quadratic/Complex/PuzzleBoundaryMotion.lean`

Web/source lookup used:
- Numdam Astérisque bibliography page
- one broad web search for parapuzzle terminology, treated only as a lead and not
  as a primary citation.

Tool limits / honesty notes:
- I did **not** extract the exact theorem text from Lyubich Astérisque 261 itself
  during this task.
- I therefore do not claim a fully pinned theorem for the component-selection
  clause.
- No Lean files were edited.

## 10. Complete `git status --short` and safety confirmation

```text
 M Mlc/ParaPuzzleCarvingReduction.lean
 M Mlc/Quadratic/Complex/Bottcher/Slodkowski.lean
 M plan/PLAN_04_parameter_connectivity.md
```

Safety confirmation:
- I wrote **only** this result artifact.
- I did **not** edit Lean sources, plans, notebooks, or docs beyond this required
  result file.
- I did **not** commit.
- No `axiom`, `sorry`, or `admit` were introduced.