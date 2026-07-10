# GPT54 Result 03 — Parapuzzle interface audit

## 1. Executive verdict

Verdict: **the repository does not currently formalize a genuine classical finite-level parapuzzle object.**

`MLC.Quadratic.ParaPuzzlePieceAt` is, by definition, a **translated fixed-base dynamical puzzle piece**:

```lean
Mlc/Quadratic/Complex/ParaPuzzle.lean

def ParaPuzzlePieceAt (c : ℂ) (n : ℕ) : Set ℂ :=
  {c' | c' - c ∈ DynamicalPuzzlePiece c n 0}
```

After `Mlc/ParaPuzzleConnectivity.lean` proves `DynamicalPuzzlePiece c n 0 = GreenSublevel c n` for `c ∈ M`, this becomes a translated fixed-base Green sublevel

```lean
{c' | green_function c (c' - c) < (1 / 2 : ℝ)^n}
```

and **not** a moving-parameter puzzle domain built from parameter rays, wakes, parapuzzle graphs, or a finite-level phase-parameter correspondence.

So from repository definitions alone,
`green_sublevel_translate_inter_mandelbrot_connected_straddling` is best classified as:

- **not** a standard classical finite-level parapuzzle connectivity theorem;
- **yes**, a stronger/artificial statement about a fixed-base translated Green sublevel intersected with `M`;
- partially reduced to a sharper carving/motion target, but **not discharged**.

Smallest honest next milestone:
1. a restricted theorem stated directly for the existing translated-Green interface; and/or
2. the first real parameter-side definition (finite-level parameter piece/wake/graph) that does not already package connectivity.

## 2. Definition/equality trace

### Root definition

`Mlc/Quadratic/Complex/ParaPuzzle.lean`

```lean
def ParaPuzzlePieceAt (c : ℂ) (n : ℕ) : Set ℂ :=
  {c' | c' - c ∈ DynamicalPuzzlePiece c n 0}
```

Immediate consequences:

```lean
lemma mem_paraPuzzlePieceAt_iff (c c' : ℂ) (n : ℕ) :
  c' ∈ ParaPuzzlePieceAt c n ↔ c' - c ∈ DynamicalPuzzlePiece c n 0

lemma mem_paraPuzzlePieceAt_self (c : ℂ) (n : ℕ) :
  c ∈ ParaPuzzlePieceAt c n ↔ 0 ∈ DynamicalPuzzlePiece c n 0
```

This contains **no moving parameter data**. The base parameter `c` is frozen and reused inside the dynamical piece.

### Equality chain to Green sublevels

`Mlc/ParaPuzzleConnectivity.lean` gives the entire identification chain:

1. `connectedComponentIn_eq_of_isConnected`
2. `dynamicalPuzzlePiece_eq_greenSublevel {c} (hc : c ∈ MandelbrotSet) (n : ℕ)`
3. `mem_paraPuzzlePieceAt_iff_green {c c'} (hc : c ∈ MandelbrotSet) (n : ℕ)`
4. `paraPuzzlePieceAt_eq_green_translate {c} (hc : c ∈ MandelbrotSet) (n : ℕ)`

Exact endpoint:

```lean
theorem paraPuzzlePieceAt_eq_green_translate {c : ℂ} (hc : c ∈ MandelbrotSet) (n : ℕ) :
  ParaPuzzlePieceAt c n = {c' | green_function c (c' - c) < (1 / 2 : ℝ) ^ n}
```

Supporting step:

```lean
theorem dynamicalPuzzlePiece_eq_greenSublevel {c : ℂ} (hc : c ∈ MandelbrotSet) (n : ℕ) :
  DynamicalPuzzlePiece c n 0 = Quadratic.GreenSublevel c n
```

with

```lean
def GreenSublevel (c : ℂ) (n : ℕ) : Set ℂ :=
  {w | green_function c w < (1 / 2) ^ n}
```

### Audit conclusion for Task A

The current `ParaPuzzlePieceAt` is **merely a translated fixed-base dynamical sublevel/piece**.
It does **not** contain any of the following intrinsically:

- moving parameter critical-orbit conditions,
- parameter rays,
- parameter equipotentials,
- wakes,
- parapuzzle graphs,
- phase-parameter maps.

Those are at most discussed in comments/docstrings or represented by later packaging layers.

## 3. Genuine-infrastructure inventory

Below, “content” means actual mathematical definitions/theorems; “packaging” means assumption transport or witness wrappers.

### A. Holomorphic motions indexed by parameter

1. `Mlc/Quadratic/Complex/Axioms.lean`

```lean
structure HolomorphicMotion (E : Set ℂ) where
```

- This is a genuine structure/interface.
- It is abstract infrastructure, not by itself a constructed parapuzzle motion.

2. `Mlc/Quadratic/Complex/Bottcher/Slodkowski.lean`

```lean
def LambdaLemmaContinuity : Prop := ...
def SlodkowskiExtension {E : Set ℂ} (H : HolomorphicMotion E) : Prop := ...
structure SpaceHolomorphicMotion (E : Set ℂ) extends HolomorphicMotion E where ...
def ParaPieceIsMotionImage (c : ℂ) (n : ℕ) : Prop := ...
theorem isConnected_greenSublevel_inter_mandelbrot_of_motionImage ...
```

- `SpaceHolomorphicMotion` is real mathematical interface content.
- `LambdaLemmaContinuity` and `SlodkowskiExtension` are **named Prop statements**, not proved here.
- `ParaPieceIsMotionImage` is a **conditional reduction target**, not a constructed finite-level parapuzzle theorem.

3. `Mlc/Quadratic/Complex/PuzzleBoundaryMotion.lean`

Key declarations:

```lean
def motion_preserves_para_piece ... : Prop :=
  c₀ ∈ MandelbrotSet → ∃ S : Set ℂ, IsConnected S ∧ S = ParaPuzzlePieceAt c₀ n ∩ MandelbrotSet

structure PuzzleBoundaryMotionHyp : Prop where
  motion : ...

private def trivialHolomorphicMotion : HolomorphicMotion (∅ : Set ℂ)
```

Audit finding:
- `motion_preserves_para_piece` ignores `_r`, `E`, `_h` in the payload.
- `PuzzleBoundaryMotionHyp` is therefore largely **phantom packaging** for connectedness.
- `trivialHolomorphicMotion` on `∅` confirms the interface can be inhabited without genuine geometric content.

4. `Mlc/DirectRoute.lean`

```lean
theorem puzzleBoundaryMotionHyp_of_connected ...
theorem connected_of_puzzleBoundaryMotionHyp ...
theorem puzzleBoundaryMotionHyp_iff_connected :
  PuzzleBoundaryMotionHyp ↔ ParaPuzzlePieceInterMandelbrotConnectedData
```

This explicitly proves the motion layer is logically equivalent to connectedness in the present code.
This is strong evidence that the current “boundary motion” layer is **not** yet a genuine parapuzzle construction.

### B. Moving dynamical puzzle graphs / equipotential packaging

`Mlc/Quadratic/Complex/Bottcher/BottcherMotion.lean`

Relevant declarations found:

```lean
def equipotential (B : BottcherData) (c : ℂ) (n : ℕ) : Set ℂ := ...
... puzzle_boundary_eq_equipotential :
  PuzzleBoundary c n = equipotential (BottcherData.ofFamily phi) c n
```

Assessment:
- This is a real dynamical/equipotential-side interface.
- But the surrounding theorem-facing constructors still factor through witness packaging such as `motion_preserves_para_piece_of_green_sublevel_of_witness_hyp`.
- So this is not yet an implemented parameter-side parapuzzle construction.

### C. Parameter rays / equipotentials / wakes / phase-parameter maps

Searches found:
- `external_ray_map` declarations in Böttcher files (`BottcherAxioms.lean`, `BottcherCore.lean`, `BottcherOnMTheory.lean`, `DegreeOneInj.lean`, `GreenFunctionRayInversion.lean`)
- no audited declaration defining a finite-level **parameter wake** or **parameter parapuzzle domain**;
- no audited declaration defining a **phase-parameter map**;
- no audited declaration giving a component/separation characterization of true parameter pieces independent of the fixed-base Green-translate model.

Important distinction:
- `external_ray_map` is a dynamical/exterior-side object in this repository slice, not a completed parameter-side wake/parapuzzle formalization.
- I found comments mentioning equipotential boundaries and Böttcher parametrizations, but not a checked definition of a finite-level parameter wake / parameter puzzle graph that is later used to define `ParaPuzzlePieceAt`.

### D. Connectivity providers / witness packaging

`Mlc/Quadratic/Complex/PuzzleLemmas2.lean`

Key declarations:

```lean
axiom para_puzzle_piece_inter_mandelbrot_connected ...
def ParaPuzzlePieceInterMandelbrotConnectedData : Prop := ...
structure ParaPuzzleInterMandelbrotTransportData where ...
structure ParaPuzzleInterMandelbrotTransportExistsData : Prop where ...
```

Assessment:
- `para_puzzle_piece_inter_mandelbrot_connected` is axiom-backed legacy hook.
- The transport structures are packaging layers for connected witness sets.
- They do **not** introduce genuine parameter geometry.
- Several constructors simply turn connectedness into transport data and back.

## 4. Parameter-class dependency table

| Class | Main file(s) | Where connectivity/shrinkage enters | Status in code |
|---|---|---|---|
| Finitely renormalizable | `Mlc/InfinitelyRenormalizable.lean`, `Mlc/AxiomsMainConjecture.lean`, `Mlc/LcAtOfShrink.lean` | `mlc_finitely_renormalizable_of_paraPuzzleConnectedData`; needs para-piece connectedness plus shrinkage `(⋂ n, ParaPuzzlePieceAt c n) = {c}` | connectedness is transported from data/hook; shrinkage gets wrapped by `parameter_shrink_of_yoccoz` |
| Infinitely renormalizable (classification entry) | `Mlc/MainConjecture.lean`, `Mlc/InfinitelyRenormalizable.lean` | classification theorem expects `PrimitiveRenormalizable c ∨ SatelliteRenormalizableTower c` | packaged interface, not fully derived here |
| Primitive IR branch | `Mlc/InfinitelyRenormalizable.lean`, `Mlc/PrimitiveModulusDivergence.lean` | primitive route goes through shrinkage theorems (`primitive_shrinkage_of_*`) and then `lc_at_of_shrink` | theorem-facing bridge content exists; not a parapuzzle-connectivity theorem |
| Satellite / tower branch | `Mlc/SatelliteRenormalizationTower.lean`, `Mlc/MoleculeConjectureBridge.lean`, `Mlc/MoleculeToParameterShrink.lean` | parameter shrinkage enters via Molecule bridge data: `MoleculeModulusLowerBoundData`, `MoleculeConformalModulusLowerBoundData`, `MoleculeUniformConformalLowerBoundData` | assumed/bridged, not proved from explicit parapuzzle geometry |
| Neutral / Siegel / parabolic | mostly represented only indirectly via docs/comments/frontier planning; no audited dedicated route-to-`ParaPuzzlePieceAt` geometry found in current inspection | no direct parapuzzle connectivity/shrinkage formalization located | unresolved / not represented as a concrete parameter-piece geometry layer in inspected code |
| Residual virtual near-molecule | plan/frontier layer; linked to `residualOpenVirtualNearMoleculeAxiom` in current architecture | enters as remaining open residual package, separate from finite parapuzzle connectivity | explicitly open / axiomatic frontier |

### Notes on finitely renormalizable path

`Mlc/InfinitelyRenormalizable.lean`:

```lean
theorem mlc_finitely_renormalizable_of_paraPuzzleConnectedData ...
```

This consumes connectedness through a payload:

```lean
(h_conn : ParaPuzzlePieceInterMandelbrotConnectedData)
```

and a shrinkage hypothesis:

```lean
(h_para_shrink : (⋂ n, MLC.Quadratic.ParaPuzzlePieceAt c n) = {c})
```

So finite-branch connectivity is **not independently rebuilt from genuine parameter geometry** in the current code path.

### Notes on Yoccoz shrink wrapper

`Mlc/AxiomsMainConjecture.lean`:

```lean
theorem parameter_shrink_of_yoccoz :
  ∀ (c : ℂ) ...,
    (⋂ n, DynamicalPuzzlePiece c n 0) = {0} →
    (⋂ n, ParaPuzzlePieceAt c n) = {c}
```

This is a checked theorem wrapper around an imported/principal-nest bridge, but it is still a bridge theorem, not a new parameter-side parapuzzle geometry construction.

## 5. Assessment of the current target

Target audited:

```lean
axiom green_sublevel_translate_inter_mandelbrot_connected_straddling ...
```

from `Mlc/ParaPuzzleConnectivity.lean`.

### Formal classification from code inspection

Best answer: **(2)** a stronger/artificial statement about an fixed-base translated Green sublevel, with partial reduction to sharper hooks, but not a standard classical finite-level parapuzzle theorem.

Why:

1. The underlying set is literally

```lean
{c' | green_function c (c' - c) < (1 / 2 : ℝ)^n} ∩ MandelbrotSet
```

for a frozen base parameter `c`.

2. `ParaPuzzlePieceAt` is definitionally tied to `DynamicalPuzzlePiece c n 0`, hence to the same frozen-base dynamical system.

3. No inspected definition makes this equal to a classical finite-level parameter wake/domain cut out by parameter rays/equipotentials/graphs.

4. The file itself documents the theorem as the residual content of a Douady–Hubbard parameter↔dynamical correspondence, i.e. something still **needed**, not already formalized.

### Is it equivalent to another explicit project hook?

Partially, yes, in the following sense:

- `green_sublevel_translate_inter_mandelbrot_connected` is now a theorem reduced to the weaker axiom `..._straddling` by subset/straddling case split.
- `Mlc/ParaPuzzleCarvingReduction.lean` further sharpens the frontier to a carving/motion-image obstruction theorem (`not_paraPieceCarvedByMotion_of_straddling` and surrounding reductions from prior task context).
- `Mlc/Quadratic/Complex/Bottcher/Slodkowski.lean` gives a conditional route via `ParaPieceIsMotionImage`.

But these are **reductions**, not equivalences to an already-realized finite-level parapuzzle construction.

### Honest conclusion

From repository definitions alone, the target is **not yet justified as a classical finite-level parapuzzle connectivity theorem**. It is a repository-specific surrogate statement motivated by that mathematics.

## 6. Proposed next theorem signatures

### Candidate 1 — smallest honest restricted theorem supported now

```lean
theorem green_sublevel_translate_inter_mandelbrot_connected_of_motionImage
    (c : ℂ) (n : ℕ)
    (h : MLC.Quadratic.ParaPieceIsMotionImage c n) :
    IsConnected ({c' | green_function c (c' - c) < (1 / 2 : ℝ) ^ n} ∩ MLC.Quadratic.MandelbrotSet)
```

Status note: this already exists under the name
`isConnected_greenSublevel_inter_mandelbrot_of_motionImage` in
`Mlc/Quadratic/Complex/Bottcher/Slodkowski.lean`.

Why it is the smallest honest target:
- hypotheses are explicit and geometric enough to be meaningful;
- it does **not** assume the intersection is connected;
- it avoids circular exact-image packaging of the target set by naming the motion-image bridge as the missing mathematical input.

Expected consumer:
- `Mlc/ParaPuzzleConnectivity.lean`, replacing or localizing `..._straddling` once a concrete `ParaPieceIsMotionImage` instance is built.

### Candidate 2 — first missing genuine parapuzzle definition/theorem

```lean
def ParameterPuzzlePiece (c : ℂ) (n : ℕ) : Set ℂ
```

together with a first theorem of the shape

```lean
theorem parameterPuzzlePiece_eq_motionImage
    (c : ℂ) (n : ℕ) :
    ∃ (E : Set ℂ) (H : MLC.Quadratic.SpaceHolomorphicMotion E) (t : ℂ),
      t ∈ Metric.ball (0 : ℂ) 1 ∧ IsConnected E ∧
      H.f t '' E = ParameterPuzzlePiece c n
```

Required dependencies:
- an actual finite-level parameter-side definition using parameter rays/equipotentials/wakes/graphs, or another non-circular Douady–Hubbard-accurate parameter-piece object;
- a genuine Böttcher inverse / motion construction on a nonempty reference set;
- no assumption that already states connectedness of `ParameterPuzzlePiece c n`.

Expected consumer:
- a replacement for the present surrogate `ParaPuzzlePieceAt`/Green-translate target in the finite branch;
- eventually a theorem comparing `ParameterPuzzlePiece c n` to the currently used translated-Green set, if mathematically valid for the intended regime.

Why this is not circular:
- the definition introduces a new object rather than postulating connectedness or exact witness transport for the old one;
- the motion-image theorem supplies a mechanism from geometry, not a packaged connected set.

### Rejected circular signatures

I reject signatures of the form

```lean
∃ S, IsConnected S ∧ S = target
```

as the next milestone, because `PuzzleLemmas2.lean` already shows this is just connectedness packaging (`ParaPuzzleInterMandelbrotTransportExistsData`). That would not advance the genuine parapuzzle formalization.

## 7. Exact commands run

Environment note: the task asked for shell `rg`/`rg --files`, but in this environment `rg` is not installed. I therefore used the built-in repository search tools and direct file reads. This should be recorded as an execution limitation, not as a source edit.

Commands/tool actions used in this audit included:

- viewed `plan/GPT54_TASK_03_PARAPUZZLE_INTERFACE_AUDIT.md`
- searched declarations/content across `Mlc/**/*.lean` and `refs/**`, `plan/**`
- viewed:
  - `Mlc/Quadratic/Complex/ParaPuzzle.lean`
  - `Mlc/ParaPuzzleConnectivity.lean`
  - `Mlc/Quadratic/Complex/PuzzleBoundaryMotion.lean`
  - `Mlc/Quadratic/Complex/PuzzleLemmas2.lean`
  - `Mlc/Quadratic/Complex/Bottcher/Slodkowski.lean`
  - `Mlc/Quadratic/Complex/Bottcher/BottcherMotion.lean`
  - `Mlc/DirectRoute.lean`
  - `Mlc/MainConjecture.lean`
  - `Mlc/InfinitelyRenormalizable.lean`
  - `Mlc/AxiomsMainConjecture.lean`
  - `Mlc/SatelliteRenormalizationTower.lean`
  - `Mlc/MoleculeConjectureBridge.lean`
  - `Mlc/MoleculeToParameterShrink.lean`
  - `Mlc/FastTowerExistence.lean`
  - `Mlc/FastTowerExistenceObstruction.lean`
- shell command run:

```bash
git --no-pager status --short
```

## 8. Complete `git status --short` output

```text
M Mlc/ParaPuzzleCarvingReduction.lean
?? plan/GPT54_RESULT_01_PARAMETER_CONNECTIVITY_AUDIT.md
?? plan/GPT54_RESULT_02_FORMALIZE_CARVING_NOGO.md
?? plan/GPT54_REVIEW_01_PARAMETER_CONNECTIVITY_AUDIT.md
?? plan/GPT54_REVIEW_02_FORMALIZE_CARVING_NOGO.md
?? plan/GPT54_TASK_01_PARAMETER_CONNECTIVITY_AUDIT.md
?? plan/GPT54_TASK_02_FORMALIZE_CARVING_NOGO.md
?? plan/GPT54_TASK_03_PARAPUZZLE_INTERFACE_AUDIT.md
```

## 9. Compliance confirmation

- No Lean source files were edited for this audit task.
- No existing plan, README, notebook, or previous result/review file was edited.
- No new `axiom`, `sorry`, or `admit` was introduced by this audit task.
- No commit was created.
- Report written as the only authorized artifact for Task 03.
