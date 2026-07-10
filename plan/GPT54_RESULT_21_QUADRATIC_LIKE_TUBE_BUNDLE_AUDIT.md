# GPT-5.4 Result 21: Quadratic-like tube bundle audit

## Executive summary

I completed the required read-only audit of the tube/fiber-bundle layer above
`AnalyticQuadraticLikeFamilyCore`.

### Final decision

**Decision: (1)** — a source-faithful tube layer is ready for a small Lean
implementation.

The local source does define a tube as a **fiber bundle over its projection** with
Jordan-disk fibers, but it does **not** supply a concrete Lean-ready atlas or any
explicit global trivialization data. Mathlib does contain a strong **global**
trivial-bundle API (`IsHomeomorphicTrivialFiberBundle`) and general bundle /
trivialization infrastructure, but reusing the full dependent `FiberBundle`
framework would be significantly heavier than what the source currently needs for
this project stage.

So the recommended next implementation is a **small project-local tube interface**:
store the total subset `total : Set (ℂ × ℂ)`, a projection to the parameter subtype,
first-coordinate compatibility, openness, and named propositional fields for:

- source-faithful local triviality over the parameter domain;
- Jordan-disk fibers.

This keeps the layer honest, compile-oriented, and below proper / unfolded /
equipped / tubing / straightening.

## Sources inspected

Repository files:

- `plan/GPT54_TASK_21_QUADRATIC_LIKE_TUBE_BUNDLE_AUDIT.md`
- `plan/GPT54_RESULT_19_DIRECT_SOURCE_CHECK_QUADRATIC_LIKE_FAMILY.md`
- `plan/GPT54_RESULT_20_IMPLEMENT_ANALYTIC_QUADRATIC_LIKE_FAMILY_CORE.md`
- `Mlc/AnalyticQuadraticLikeFamilyCore.lean`

Local source extraction commands:

```bash
cd /home/kir/pers/mlc && pdftotext 'refs/Conformal Geometry and Dynamics of Quadratic Polynomials.pdf' /tmp/lyubich_full.txt
cd /home/kir/pers/mlc && grep -n -E 'tube|fiber bundle|fibre bundle|Jordan disks|projection onto the first coordinate|Quadratic-like families' /tmp/lyubich_full.txt | sed -n '1,220p'
sed -n '11704,11714p' /tmp/lyubich_full.txt
sed -n '12844,12858p' /tmp/lyubich_full.txt
```

Mathlib API inspection:

- `Mathlib/Topology/FiberBundle/IsHomeomorphicTrivialBundle.lean`
- `Mathlib/Topology/FiberBundle/Basic.lean`
- `Mathlib/Topology/FiberBundle/Trivialization.lean`

Temporary compilation probes:

```bash
cd /home/kir/pers/mlc && lake env lean /tmp/task21_probe.lean
cd /home/kir/pers/mlc && lake env lean /tmp/task21_trivial_bundle_probe.lean
```

## A. Direct source semantics

### Main tube definition

**Extracted lines:** `/tmp/lyubich_full.txt:11708–11711`

> “Let π : C2 → C stand for the projection onto the ﬁrst coordinate. We call a set
> `U ⊂ C2` a tube over `Λ = π(U) ⊂ C` if it is a ﬁber bundle over `Λ` whose ﬁbers
> `U_λ = U ∩ π⁻¹ λ` are Jordan disks (either open or closed). For `X ⊂ Λ`, we let
> `U|X = U ∩ π⁻¹ X`.”

### Additional tube-use evidence

**Extracted lines:** `/tmp/lyubich_full.txt:12848–12850`

> “The map `H : V → ∂Λ × D, (λ, z) ↦ (λ, h⁻¹_λ (z))` straightens the tube `V` to the
> solid torus.”

This confirms that the source uses a fiber-preserving straightening chart when
additional structure is available, but it still does **not** redefine “tube” as a
single global trivialization.

### Conclusions required by Task 21.A

#### 1. Locally trivial or globally trivial?

The source says **fiber bundle over `Λ`** and does **not** state global triviality.
So the honest reading is **locally trivial**, not globally trivial.

#### 2. Model fiber and structure maps specified?

Only partially. The source specifies that fibers are **Jordan disks** (open or
closed), but does **not** fix one model disk or provide explicit transition maps in
this definition. So the model fiber is “some Jordan disk up to homeomorphism”, not a
single canonical Lean object at this point.

#### 3. Open and closed tubes separate notions?

Yes, at fiber level: the definition explicitly allows fibers that are Jordan disks
“either open or closed”. The source does not introduce separate terms like “open
tube” and “closed tube” here, but the distinction is present in the definition.

#### 4. Must both source and target be tubes?

In the quadratic-like family discussion, both source and target vary fiberwise as
`U_λ` and `U'_λ`, and the text explicitly calls the total source `U` a tube in the
family definition. Since the target fibers are also Jordan-disk codomains varying
with `λ`, the natural faithful reading for a complete family object is that the
source and target total spaces should each carry tube structure.

#### 5. Are Jordan-disk fibers part of tube definition or provided by fiber maps?

They are part of the **tube definition itself**. The line above explicitly says a
set `U ⊂ C²` is a tube if it is a fiber bundle whose fibers are Jordan disks.
This is not delegated to the separate fiberwise map object.

#### 6. What compatibility with projection `π : ℂ² → ℂ` is required?

At minimum:

- the base is `Λ = π(U)`;
- the fibers are the slices `U_λ = U ∩ π⁻¹ λ`;
- tube structure must be over that projection to the first coordinate.

So any Lean interface must ensure that the tube projection agrees with the first
coordinate on total-space points.

### Earlier/fuller definition search

The grep over the local text did **not** reveal an earlier formal definition of
tube before the §42 definition above. The later index entry

- `/tmp/lyubich_full.txt:12984` — `tube (of a q-l family) §42.1`

instead points back to §42.1 as the defining location.

So the first formal definition available in the local source appears to be the one
at `11708–11711`.

## B. Mathlib API audit

### 1. Global trivial-bundle abstraction

File:
- `Mathlib/Topology/FiberBundle/IsHomeomorphicTrivialBundle.lean`

Exact declaration:

```lean
def IsHomeomorphicTrivialFiberBundle (proj : Z → B) : Prop :=
  ∃ e : Z ≃ₜ B × F, ∀ x, (e x).1 = proj x
```

Useful derived lemmas:

```lean
IsHomeomorphicTrivialFiberBundle.proj_eq
  (h : IsHomeomorphicTrivialFiberBundle F proj) : ∃ e, proj = Prod.fst ∘ ⇑e

IsHomeomorphicTrivialFiberBundle.continuous_proj
  (h : IsHomeomorphicTrivialFiberBundle F proj) : Continuous proj

IsHomeomorphicTrivialFiberBundle.isOpenMap_proj
  (h : IsHomeomorphicTrivialFiberBundle F proj) : IsOpenMap proj

isHomeomorphicTrivialFiberBundle_fst
  : IsHomeomorphicTrivialFiberBundle F Prod.fst
```

Fit assessment:

- **Good** if one deliberately wants a **single global** fiber-preserving
  homeomorphism to `Λ × F`.
- **Too strong** as a source-faithful default, since the source only says “fiber
  bundle”, not “globally trivial bundle”.
- Also awkward for a total subset `totalU ⊆ ℂ × ℂ` if the model fiber is “an
  unspecified Jordan disk” rather than a fixed type `F`.

### 2. General dependent fiber-bundle class

File:
- `Mathlib/Topology/FiberBundle/Basic.lean`

Key declarations:

```lean
class FiberBundle where
  totalSpaceMk_isInducing' : ∀ b : B, IsInducing (@TotalSpace.mk B F E b)
  trivializationAtlas' : Set (Trivialization F (π F E))
  trivializationAt' : B → Trivialization F (π F E)
  mem_baseSet_trivializationAt' : ∀ b : B, b ∈ (trivializationAt' b).baseSet
  trivialization_mem_atlas' : ∀ b : B, trivializationAt' b ∈ trivializationAtlas'
```

and associated API:

```lean
FiberBundle.trivializationAtlas
FiberBundle.trivializationAt
FiberBundle.continuous_proj
FiberBundle.isOpenMap_proj
FiberBundle.surjective_proj
```

Fit assessment:

- This is genuine local-triviality machinery.
- But it is built around `Bundle.TotalSpace F E`, i.e. a dependent total space, not a
  pre-existing concrete subset `totalU ⊆ ℂ × ℂ`.
- Reusing it for the present project would require either:
  1. rebuilding the tube as an actual dependent bundle total space; or
  2. writing a nontrivial adapter connecting the subset-in-`ℂ²` representation to
     Mathlib’s `Bundle.TotalSpace` framework.
- That is more engineering than the current source-faithful milestone needs.

### 3. Local trivialization / pretrivialization API

File:
- `Mathlib/Topology/FiberBundle/Trivialization.lean`

Relevant declaration:

```lean
structure Pretrivialization (proj : Z → B) extends PartialEquiv Z (B × F) where
  open_target : IsOpen target
  baseSet : Set B
  open_baseSet : IsOpen baseSet
  source_eq : source = proj ⁻¹' baseSet
  target_eq : target = baseSet ×ˢ univ
  proj_toFun : ∀ p ∈ source, (toFun p).1 = proj p
```

This is close in spirit to what tube local charts would need: local partial
homeomorphisms to `baseSet × F` commuting with projection.

Fit assessment:

- conceptually relevant;
- still tied to a chosen model fiber `F` and substantial bundle infrastructure;
- helpful as an implementation reference, but probably too heavy for the smallest
  project-local tube layer.

### Distinctions requested by Task 21.B

- **Local triviality of a projection:** represented in Mathlib by the
  `FiberBundle` / `Trivialization` framework.
- **One global homeomorphism with `Λ × D`:** represented by
  `IsHomeomorphicTrivialFiberBundle`.
- **Merely continuous variation of Jordan domains:** not by itself encoded by the
  above APIs; one would need some weaker project-specific structure.

## C. Representation options

### Option 1. Reuse Mathlib `FiberBundle` / local trivializations

Pros:
- source-faithful local triviality;
- robust projection/trivialization API already exists.

Cons:
- representation mismatch with `totalU totalV : Set (ℂ × ℂ)`;
- likely requires an adapter into `Bundle.TotalSpace`;
- too much machinery for the immediate family-layer milestone.

Verdict:
- **Not recommended now**.

### Option 2. Store an atlas of local fiber-preserving homeomorphisms

Pros:
- most source-faithful direct project representation;
- keeps tube local rather than global.

Cons:
- encoding an honest local-triviality atlas in full is still sizable;
- requires explicit chart overlap compatibility from the start.

Verdict:
- **Faithful but heavier than needed for the next small implementation**.

### Option 3. Introduce a stronger global homeomorphism to a fixed Jordan disk

Pros:
- easy to express with `IsHomeomorphicTrivialFiberBundle`;
- convenient for derived openness/continuity statements.

Cons:
- stronger than source;
- would incorrectly hard-code global triviality unless clearly labeled as a
  project-specific strengthening.

Verdict:
- **Reject as the default source layer**.

### Option 4. Postpone local triviality and define only a named source-compatible interface

Pros:
- smallest honest next step;
- integrates cleanly with the existing analytic core;
- avoids false claims of global triviality;
- keeps future room for a fuller atlas later.

Cons:
- local triviality remains a `Prop` placeholder rather than a reusable chart API.

Verdict:
- **Recommended**.

## D. Integration with the analytic core

### Recommended tube layer signature

Compile-tested local alternative:

```lean
structure QuadraticLikeTubeOver (Λ : Set ℂ) where
  total : Set (ℂ × ℂ)
  proj : total → Λ
  proj_fst : ∀ p : total, (proj p).1 = p.1.1
  isOpen_total : IsOpen total
  fiber_is_jordan_disk : Prop
  local_trivial : Prop
```

Interpretation:

- `total` is the concrete subset of `ℂ²`.
- `proj` lands in the parameter subtype.
- `proj_fst` is the key field ensuring compatibility with first-coordinate
  projection `π : ℂ² → ℂ`.
- `fiber_is_jordan_disk` records the source’s Jordan-disk requirement.
- `local_trivial` is a named proposition standing for the source’s fiber-bundle
  condition until a fuller atlas is warranted.

### Recommended complete-family wrapper

Compile-tested wrapper:

```lean
structure QuadraticLikeFamilyWithTubes where
  core : AnalyticQuadraticLikeFamilyCore
  sourceTube : QuadraticLikeTubeOver core.parameterSet
  targetTube : QuadraticLikeTubeOver core.parameterSet
  total_eq_source : sourceTube.total = core.totalU
  total_eq_target : targetTube.total = core.totalV
```

Why this fits:

- it reuses the analytic core verbatim;
- it adds tube structure to both `totalU` and `totalV`;
- it avoids duplicating fiber sections and BMol/Jordan facts already carried through
  `GenuineBMol` except for the source-level statement that the **tube fibers** are
  Jordan disks.

### Projection-compatibility field/theorem

The field that enforces commutation with first-coordinate projection is:

```lean
proj_fst : ∀ p : total, (proj p).1 = p.1.1
```

This is the project-local replacement for the source condition that the bundle is
“over `Λ = π(U)`” and for Mathlib’s chart-level property
`Pretrivialization.proj_toFun`.

## E. Temporary compilation

### Probe 1: recommended local tube wrapper

File: `/tmp/task21_probe.lean`

Tested code:

```lean
import Mlc.AnalyticQuadraticLikeFamilyCore
import Mathlib.Topology.FiberBundle.IsHomeomorphicTrivialBundle

open Set Complex
namespace Molecule

structure QuadraticLikeTubeOver (Λ : Set ℂ) where
  total : Set (ℂ × ℂ)
  proj : total → Λ
  proj_fst : ∀ p : total, (proj p).1 = p.1.1
  isOpen_total : IsOpen total
  fiber_is_jordan_disk : Prop
  local_trivial : Prop

structure QuadraticLikeFamilyWithTubes where
  core : AnalyticQuadraticLikeFamilyCore
  sourceTube : QuadraticLikeTubeOver core.parameterSet
  targetTube : QuadraticLikeTubeOver core.parameterSet
  total_eq_source : sourceTube.total = core.totalU
  total_eq_target : targetTube.total = core.totalV

end Molecule
```

Command:

```bash
cd /home/kir/pers/mlc && lake env lean /tmp/task21_probe.lean
```

Outcome:
- passed (`exit code 0`)

### Probe 2: Mathlib global trivial-bundle API signatures

File: `/tmp/task21_trivial_bundle_probe.lean`

Tested code:

```lean
import Mathlib.Topology.FiberBundle.IsHomeomorphicTrivialBundle

open Topology

variable {B F Z : Type*} [TopologicalSpace B] [TopologicalSpace F] [TopologicalSpace Z]

#check IsHomeomorphicTrivialFiberBundle
#check IsHomeomorphicTrivialFiberBundle.proj_eq
#check IsHomeomorphicTrivialFiberBundle.continuous_proj
#check IsHomeomorphicTrivialFiberBundle.isOpenMap_proj
#check isHomeomorphicTrivialFiberBundle_fst
```

Command:

```bash
cd /home/kir/pers/mlc && lake env lean /tmp/task21_trivial_bundle_probe.lean
```

Outcome:
- passed (`exit code 0`)

### Limitation statement

The appropriate full Mathlib local-trivialization API exists, but using it honestly
for a concrete subset `totalU ⊆ ℂ × ℂ` would likely require a separate adapter to a
`Bundle.TotalSpace` model. That is exactly why the recommended next step is the small
project-local interface above rather than immediate adoption of the full dependent
bundle stack.

## F. Exact next worker task

Implement a new Lean module defining:

- `QuadraticLikeTubeOver`
- `QuadraticLikeFamilyWithTubes`

as a minimal project-local tube layer above
`AnalyticQuadraticLikeFamilyCore`, with fields for concrete total subset,
projection-to-parameter-subtype, first-coordinate compatibility, openness,
Jordan-disk-fiber proposition, and local-triviality proposition, and no proper /
unfolded / equipped / tubing / straightening data.

## Full git status --short

```text
M Mlc.lean
?? Mlc/AnalyticQuadraticLikeFamilyCore.lean
?? Mlc/BMolFilledJulia.lean
?? Mlc/GenuineBMol.lean
?? plan/GPT54_PROMPT_11_QUADRATIC_LIKE_FAMILY_FOUNDATION_AUDIT.md
?? plan/GPT54_PROMPT_12_BMOL_FILLED_JULIA_DEFINITION.md
?? plan/GPT54_PROMPT_13_IMPLEMENT_BMOL_FILLED_JULIA_FOUNDATION.md
?? plan/GPT54_PROMPT_14_GENUINE_BMOL_FAMILY_REFINEMENT_AUDIT.md
?? plan/GPT54_PROMPT_15_IMPLEMENT_GENUINE_BMOL_REFINEMENT.md
?? plan/GPT54_PROMPT_16_CORRECT_GENUINE_BMOL_COMPACT_CONTAINMENT.md
?? plan/GPT54_PROMPT_17_ANALYTIC_QUADRATIC_LIKE_FAMILY_TOTAL_SPACE_AUDIT.md
?? plan/GPT54_PROMPT_18_CORRECT_ANALYTIC_FAMILY_TOTAL_SPACE_SPEC.md
?? plan/GPT54_PROMPT_19_DIRECT_SOURCE_CHECK_QUADRATIC_LIKE_FAMILY.md
?? plan/GPT54_PROMPT_20_IMPLEMENT_ANALYTIC_QUADRATIC_LIKE_FAMILY_CORE.md
?? plan/GPT54_PROMPT_21_QUADRATIC_LIKE_TUBE_BUNDLE_AUDIT.md
?? plan/GPT54_RESULT_09_SPECIFY_CANONICAL_PARAMETER_PIECE.md
?? plan/GPT54_RESULT_10_RENORMALIZATION_LOCUS_SPECIFICATION.md
?? plan/GPT54_RESULT_11_QUADRATIC_LIKE_FAMILY_FOUNDATION_AUDIT.md
?? plan/GPT54_RESULT_12_BMOL_FILLED_JULIA_DEFINITION.md
?? plan/GPT54_RESULT_13_IMPLEMENT_BMOL_FILLED_JULIA_FOUNDATION.md
?? plan/GPT54_RESULT_14_GENUINE_BMOL_FAMILY_REFINEMENT_AUDIT.md
?? plan/GPT54_RESULT_15_IMPLEMENT_GENUINE_BMOL_REFINEMENT.md
?? plan/GPT54_RESULT_16_CORRECT_GENUINE_BMOL_COMPACT_CONTAINMENT.md
?? plan/GPT54_RESULT_17_ANALYTIC_QUADRATIC_LIKE_FAMILY_TOTAL_SPACE_AUDIT.md
?? plan/GPT54_RESULT_18_CORRECT_ANALYTIC_FAMILY_TOTAL_SPACE_SPEC.md
?? plan/GPT54_RESULT_19_DIRECT_SOURCE_CHECK_QUADRATIC_LIKE_FAMILY.md
?? plan/GPT54_RESULT_20_IMPLEMENT_ANALYTIC_QUADRATIC_LIKE_FAMILY_CORE.md
?? plan/GPT54_REVIEW_09_SPECIFY_CANONICAL_PARAMETER_PIECE.md
?? plan/GPT54_REVIEW_10_RENORMALIZATION_LOCUS_SPECIFICATION.md
?? plan/GPT54_REVIEW_11_QUADRATIC_LIKE_FAMILY_FOUNDATION_AUDIT.md
?? plan/GPT54_REVIEW_12_BMOL_FILLED_JULIA_DEFINITION.md
?? plan/GPT54_REVIEW_13_IMPLEMENT_BMOL_FILLED_JULIA_FOUNDATION.md
?? plan/GPT54_REVIEW_14_GENUINE_BMOL_FAMILY_REFINEMENT_AUDIT.md
?? plan/GPT54_REVIEW_15_IMPLEMENT_GENUINE_BMOL_REFINEMENT.md
?? plan/GPT54_REVIEW_16_CORRECT_GENUINE_BMOL_COMPACT_CONTAINMENT.md
?? plan/GPT54_REVIEW_17_ANALYTIC_QUADRATIC_LIKE_FAMILY_TOTAL_SPACE_AUDIT.md
?? plan/GPT54_REVIEW_18_CORRECT_ANALYTIC_FAMILY_TOTAL_SPACE_SPEC.md
?? plan/GPT54_REVIEW_19_DIRECT_SOURCE_CHECK_QUADRATIC_LIKE_FAMILY.md
?? plan/GPT54_REVIEW_20_IMPLEMENT_ANALYTIC_QUADRATIC_LIKE_FAMILY_CORE.md
?? plan/GPT54_TASK_10_RENORMALIZATION_LOCUS_SPECIFICATION.md
?? plan/GPT54_TASK_11_QUADRATIC_LIKE_FAMILY_FOUNDATION_AUDIT.md
?? plan/GPT54_TASK_12_BMOL_FILLED_JULIA_DEFINITION.md
?? plan/GPT54_TASK_13_IMPLEMENT_BMOL_FILLED_JULIA_FOUNDATION.md
?? plan/GPT54_TASK_14_GENUINE_BMOL_FAMILY_REFINEMENT_AUDIT.md
?? plan/GPT54_TASK_15_IMPLEMENT_GENUINE_BMOL_REFINEMENT.md
?? plan/GPT54_TASK_16_CORRECT_GENUINE_BMOL_COMPACT_CONTAINMENT.md
?? plan/GPT54_TASK_17_ANALYTIC_QUADRATIC_LIKE_FAMILY_TOTAL_SPACE_AUDIT.md
?? plan/GPT54_TASK_18_CORRECT_ANALYTIC_FAMILY_TOTAL_SPACE_SPEC.md
?? plan/GPT54_TASK_19_DIRECT_SOURCE_CHECK_QUADRATIC_LIKE_FAMILY.md
?? plan/GPT54_TASK_20_IMPLEMENT_ANALYTIC_QUADRATIC_LIKE_FAMILY_CORE.md
?? plan/GPT54_TASK_21_QUADRATIC_LIKE_TUBE_BUNDLE_AUDIT.md
```

## Confirmation

Only the result artifact `plan/GPT54_RESULT_21_QUADRATIC_LIKE_TUBE_BUNDLE_AUDIT.md`
was written. No repository source files or prior plan artifacts were modified, and
no commit was made.
