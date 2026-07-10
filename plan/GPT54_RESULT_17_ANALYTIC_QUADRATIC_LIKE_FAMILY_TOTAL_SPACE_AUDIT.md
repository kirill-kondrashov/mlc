# GPT-5.4 Result 17: Analytic quadratic-like family total-space audit

## Executive decision

**Decision: (1)** — minimal analytic-family data are ready for a small Lean implementation.

The current `GenuineBMol` wrapper is compatible with an honest family layer **provided the family is modeled on open total spaces** `totalU totalV : Set (ℂ × ℂ)` and analyticity is imposed on `totalU`, not on all of `Λ × ℂ` and not via the discrete topology on `BMol`.

The key correction to Result 14's provisional family sketch is exactly the one noted in Review 14: the joint map should be analytic on the actual varying source total space, not on `parameterSet ×ˢ Set.univ`.

## Sources inspected

Repository artifacts read:

- `plan/GPT54_TASK_17_ANALYTIC_QUADRATIC_LIKE_FAMILY_TOTAL_SPACE_AUDIT.md`
- `plan/GPT54_RESULT_10_RENORMALIZATION_LOCUS_SPECIFICATION.md`
- `plan/GPT54_RESULT_14_GENUINE_BMOL_FAMILY_REFINEMENT_AUDIT.md`
- `plan/GPT54_REVIEW_14_GENUINE_BMOL_FAMILY_REFINEMENT_AUDIT.md`
- `plan/GPT54_REVIEW_15_IMPLEMENT_GENUINE_BMOL_REFINEMENT.md`
- `plan/GPT54_RESULT_16_CORRECT_GENUINE_BMOL_COMPACT_CONTAINMENT.md`
- `Mlc/GenuineBMol.lean`
- `.lake/packages/molecule-conjecture/Molecule/BMol.lean`

Mathlib sources/audits inspected:

- `.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean`
- `.lake/packages/mathlib/Mathlib/Analysis/Complex/CauchyIntegral.lean`
- `.lake/packages/mathlib/Mathlib/Analysis/Analytic/Basic.lean`
- grep audit over Mathlib for `AnalyticOn` and `DifferentiableOn ℂ` usage on products/open sets

Local source text consulted:

- `refs/Conformal Geometry and Dynamics of Quadratic Polynomials.pdf` indirectly through the pinned excerpts already normalized in Result 10
- `refs/Dudko_2309.02107.txt` for background terminology (`Jordan disks X ⋐ Y ⊂ C`)

## A. Source definition audit

## A.1 What the source explicitly requires

From Result 10's normalized Chapter 10 §42 / Theorem 10.1 package, the source object is a **proper unfolded equipped quadratic-like family** over a parameter domain `Λ`.

Already normalized from the local source in Result 10:

- a parameter domain `Λ`;
- fibers `g_λ : U_λ → U'_λ`;
- properness as a **family** condition, not just fiberwise properness;
- unfolded / winding-one condition on the critical value along `∂Λ`;
- equipment by holomorphic motion and tubing;
- connectedness locus `M(g) = {λ ∈ Λ : J(g_λ) is connected}`.

Result 10 also records the exact short quote:

- “The Mandelbrot set of the quadratic-like family is defined as `M(g) = {λ ∈ Λ : J(g_λ) is connected}`.”

and the theorem package summary:

- Theorem 10.1 requires a **proper unfolded equipped quadratic-like family** over `Λ`.

Review 14 correctly sharpened the modeling point:

- analyticity belongs on an **open total-space source** such as
  `{p : ℂ × ℂ | p.1 ∈ Λ ∧ p.2 ∈ U p.1}`,
  not on all of `Λ × ℂ`.

## A.2 What the source package does **not** force into the minimal Lean structure

The source's full theorem package includes more than the minimal family kernel. In particular, the following should **not** be bundled into the minimal analytic-family core:

- proper family condition;
- unfolded/winding-one condition;
- holomorphic-motion equipment;
- tubing;
- connectedness locus, straightening, or conclusions.

These belong in later named predicates/structures layered over the minimal family.

## A.3 Parameter-domain properties

From Result 10:

- `Λ` is a planar parameter domain;
- in the concrete window setting, one has an **open parameter domain** `W° = Λ`;
- boundary geometry involving root/tip is part of later completion data and should not be forced into the minimal family kernel.

So the smallest honest Lean field is:

```lean
parameterSet : Set ℂ
isOpen_parameterSet : IsOpen parameterSet
```

Connectedness/Jordan assumptions should not be stored unless a later source-backed layer needs them.

## B. Mathlib complex-analytic audit

## B.1 Correct predicate for joint holomorphicity

Mathlib already supports the direct predicate:

```lean
AnalyticOn ℂ F s
```

for functions `F : E → F'` on subsets `s : Set E`, including product domains such as `E = ℂ × ℂ`.

The compile test below confirms that the signature

```lean
analyticOn_totalU : AnalyticOn ℂ eval totalU
```

is accepted for `eval : ℂ × ℂ → ℂ` and `totalU : Set (ℂ × ℂ)`.

This is the appropriate minimal predicate when the family is represented by an actual open total source `totalU`.

## B.2 Relation to `DifferentiableOn ℂ`

Mathlib also supplies the complex-analytic bridge recorded in:

- `Mathlib/Analysis/Complex/CauchyIntegral.lean`
- `Mathlib/Analysis/Calculus/FDeriv/Analytic.lean`

The grep audit shows the following named theorems are present:

- `DifferentiableOn.analyticOn`
- `AnalyticOn.differentiableOn`
- `AnalyticOnNhd.differentiableOn`

So for complex-valued maps on open subsets of `ℂ × ℂ`, either of the following is mathematically usable:

- store `AnalyticOn ℂ eval totalU` directly;
- or store `DifferentiableOn ℂ eval totalU` and derive analytic-on statements where needed.

For this task, the source language is holomorphic/analytic, so `AnalyticOn ℂ eval totalU` is the cleaner primary field.

## B.3 Why `parameterSet ×ˢ univ` is wrong here

Review 14's objection stands: a quadratic-like family is only defined on the varying total source space. An arbitrary extension of the evaluation map outside that source need not be analytic.

Therefore the earlier provisional field

```lean
AnalyticOn ℂ (fun p : ℂ × ℂ => jointMap p.1 p.2) (parameterSet ×ˢ Set.univ)
```

is generally too strong and should not be used as the core family field.

## C. Total-space representation comparison

## C.1 Representation 1: store total spaces directly

```lean
totalU totalV : Set (ℂ × ℂ)
```

with fibers extracted by sections:

```lean
fiberU (c) := {z | (c.1, z) ∈ totalU}
fiberV (c) := {z | (c.1, z) ∈ totalV}
```

Pros:

- matches Review 14's mathematically correct total-space domain;
- makes `AnalyticOn ℂ eval totalU` directly express the source notion;
- naturally supports later topological statements about the total tube;
- avoids pretending that off-fiber values exist independently of the total space;
- aligns better with future tubing/equipment layers.

Cons:

- requires explicit agreement laws tying extracted fibers to each `GenuineBMol`.

## C.2 Representation 2: store `U V : ℂ → Set ℂ`

Pros:

- fiber access is direct;
- some per-parameter lemmas can be slightly shorter.

Cons:

- still requires separate total-space openness hypotheses on sigma spaces;
- analyticity is still fundamentally about the total source subset of `ℂ × ℂ`;
- easier to drift into a dishonest global `Λ × ℂ` formulation.

## C.3 Recommendation

**Recommend representation 1**: store open total sets `totalU totalV : Set (ℂ × ℂ)` and define fibers by section.

This is the smallest honest layer because the source analyticity is joint analyticity on the actual total source.

## D. Domain scoping and off-domain fibers

Three ergonomic choices were compared:

### D.1 Total function `fiber : ℂ → GenuineBMol`

Pros:
- easiest raw function application syntax.

Cons:
- assigns arbitrary fibers outside `Λ`;
- forces extra “on-domain only” side conditions everywhere;
- conceptually weaker for later boundary-completion work.

### D.2 Subtype-indexed fibers `fiber : parameterSet → GenuineBMol`

Pros:
- mathematically honest: only on-domain fibers are stored;
- agreement laws are naturally stated for `c : parameterSet`;
- good fit with extracted section fibers from total spaces.

Cons:
- requires coercions `c.1` when building section sets.

### D.3 Total function plus on-domain laws

This mixes both worlds and offers little benefit over the subtype form.

## D.4 Recommendation

**Recommend subtype-indexed fibers**:

```lean
fiber : parameterSet → GenuineBMol
```

This is the most honest and least error-prone choice for subsequent sectionwise reasoning, connectedness loci, and later root/tip completion tasks.

## E. Compile-oriented minimal structure

The following skeleton compiled successfully in `/tmp` and is the recommended next implementation target:

```lean
structure AnalyticQuadraticLikeFamily where
  parameterSet : Set ℂ
  isOpen_parameterSet : IsOpen parameterSet
  fiber : parameterSet → GenuineBMol
  totalU : Set (ℂ × ℂ)
  totalV : Set (ℂ × ℂ)
  isOpen_totalU : IsOpen totalU
  isOpen_totalV : IsOpen totalV
  eval : ℂ × ℂ → ℂ
  fiberU (c : parameterSet) : Set ℂ := {z | (c.1, z) ∈ totalU}
  fiberV (c : parameterSet) : Set ℂ := {z | (c.1, z) ∈ totalV}
  mem_fiberU_iff (c : parameterSet) (z : ℂ) : z ∈ fiberU c ↔ (c.1, z) ∈ totalU := by rfl
  mem_fiberV_iff (c : parameterSet) (z : ℂ) : z ∈ fiberV c ↔ (c.1, z) ∈ totalV := by rfl
  fiberU_eq (c : parameterSet) : fiberU c = (fiber c : BMol).U
  fiberV_eq (c : parameterSet) : fiberV c = (fiber c : BMol).V
  eval_agrees (c : parameterSet) {z : ℂ} (hz : z ∈ fiberU c) :
    eval (c.1, z) = (fiber c : BMol).f z
  analyticOn_totalU : AnalyticOn ℂ eval totalU
```

This directly ensures:

- on-domain parameter openness;
- open total spaces;
- honest extracted fiber domains;
- agreement of fibers with `GenuineBMol.toBMol.U/V/f`;
- analyticity on the actual total source.

## F. Proper / unfolded / equipped boundary

These should be separate named layers, not bundled into the minimal family core.

## F.1 Proper family condition

Not enough source-backed repository foundation currently exists to encode the exact family properness condition nontrivially. It should therefore be a future named predicate/structure once the boundary/critical-value formulation is pinned down.

Recommended placeholder at the planning level only:

- `ProperQuadraticLikeFamilyData` or `IsProperQuadraticLikeFamily`

but **do not** yet implement it as an opaque generic `Prop` field in the minimal structure.

## F.2 Unfolded / winding-one

Similarly source-specific and boundary-based. Keep separate.

Recommended future name:

- `IsUnfoldedQuadraticLikeFamily`

Again, not yet a field in the minimal structure.

## F.3 Equipment / holomorphic motion / tubing

These definitely require new foundation objects, not generic blind `Prop` fields.

Recommended future names:

- `HolomorphicMotionEquipment`
- `QuadraticLikeTubing`
- `EquippedQuadraticLikeFamily`

These should only be implemented once the relevant motion/tube APIs are audited.

## G. Compatibility with current `GenuineBMol`

Decision (3) is **not** warranted. The current `GenuineBMol` wrapper is still compatible with varying total spaces because:

- each fiber stores intrinsic `U`, `V`, `f` data;
- the family layer can impose total-space/topological coherence externally via `totalU`, `totalV`, and agreement laws;
- no redesign of `GenuineBMol` is needed for this minimal total-space family layer.

## H. Temporary compilation

Temporary file used:

- `/tmp/task17_analytic_family_audit.lean`

Command run:

```bash
cd /home/kir/pers/mlc && lake env lean /tmp/task17_analytic_family_audit.lean
```

Outcome:

- **passed** (`exit code 0`)

The same command bundle also recorded `git --no-pager status --short`.

## I. Commands run

```bash
cd /home/kir/pers/mlc && lake env lean /tmp/task17_analytic_family_audit.lean && git --no-pager status --short
```

Additional read-only audits:

- grep over Mathlib for `AnalyticOn`
- grep over Mathlib for `DifferentiableOn ℂ`
- grep over local refs/result files for the source-normalized theorem packaging

## J. Full `git status --short`

```text
 M Mlc.lean
?? Mlc/BMolFilledJulia.lean
?? Mlc/GenuineBMol.lean
?? plan/GPT54_PROMPT_11_QUADRATIC_LIKE_FAMILY_FOUNDATION_AUDIT.md
?? plan/GPT54_PROMPT_12_BMOL_FILLED_JULIA_DEFINITION.md
?? plan/GPT54_PROMPT_13_IMPLEMENT_BMOL_FILLED_JULIA_FOUNDATION.md
?? plan/GPT54_PROMPT_14_GENUINE_BMOL_FAMILY_REFINEMENT_AUDIT.md
?? plan/GPT54_PROMPT_15_IMPLEMENT_GENUINE_BMOL_REFINEMENT.md
?? plan/GPT54_PROMPT_16_CORRECT_GENUINE_BMOL_COMPACT_CONTAINMENT.md
?? plan/GPT54_PROMPT_17_ANALYTIC_QUADRATIC_LIKE_FAMILY_TOTAL_SPACE_AUDIT.md
?? plan/GPT54_RESULT_09_SPECIFY_CANONICAL_PARAMETER_PIECE.md
?? plan/GPT54_RESULT_10_RENORMALIZATION_LOCUS_SPECIFICATION.md
?? plan/GPT54_RESULT_11_QUADRATIC_LIKE_FAMILY_FOUNDATION_AUDIT.md
?? plan/GPT54_RESULT_12_BMOL_FILLED_JULIA_DEFINITION.md
?? plan/GPT54_RESULT_13_IMPLEMENT_BMOL_FILLED_JULIA_FOUNDATION.md
?? plan/GPT54_RESULT_14_GENUINE_BMOL_FAMILY_REFINEMENT_AUDIT.md
?? plan/GPT54_RESULT_15_IMPLEMENT_GENUINE_BMOL_REFINEMENT.md
?? plan/GPT54_RESULT_16_CORRECT_GENUINE_BMOL_COMPACT_CONTAINMENT.md
?? plan/GPT54_REVIEW_09_SPECIFY_CANONICAL_PARAMETER_PIECE.md
?? plan/GPT54_REVIEW_10_RENORMALIZATION_LOCUS_SPECIFICATION.md
?? plan/GPT54_REVIEW_11_QUADRATIC_LIKE_FAMILY_FOUNDATION_AUDIT.md
?? plan/GPT54_REVIEW_12_BMOL_FILLED_JULIA_DEFINITION.md
?? plan/GPT54_REVIEW_13_IMPLEMENT_BMOL_FILLED_JULIA_FOUNDATION.md
?? plan/GPT54_REVIEW_14_GENUINE_BMOL_FAMILY_REFINEMENT_AUDIT.md
?? plan/GPT54_REVIEW_15_IMPLEMENT_GENUINE_BMOL_REFINEMENT.md
?? plan/GPT54_REVIEW_16_CORRECT_GENUINE_BMOL_COMPACT_CONTAINMENT.md
?? plan/GPT54_TASK_10_RENORMALIZATION_LOCUS_SPECIFICATION.md
?? plan/GPT54_TASK_11_QUADRATIC_LIKE_FAMILY_FOUNDATION_AUDIT.md
?? plan/GPT54_TASK_12_BMOL_FILLED_JULIA_DEFINITION.md
?? plan/GPT54_TASK_13_IMPLEMENT_BMOL_FILLED_JULIA_FOUNDATION.md
?? plan/GPT54_TASK_14_GENUINE_BMOL_FAMILY_REFINEMENT_AUDIT.md
?? plan/GPT54_TASK_15_IMPLEMENT_GENUINE_BMOL_REFINEMENT.md
?? plan/GPT54_TASK_16_CORRECT_GENUINE_BMOL_COMPACT_CONTAINMENT.md
?? plan/GPT54_TASK_17_ANALYTIC_QUADRATIC_LIKE_FAMILY_TOTAL_SPACE_AUDIT.md
```

## K. Exact next worker task

Implement a new Lean module introducing the minimal total-space analytic family structure over `GenuineBMol` with:

- `parameterSet : Set ℂ` and `isOpen_parameterSet`;
- subtype-indexed `fiber : parameterSet → GenuineBMol`;
- open total spaces `totalU totalV : Set (ℂ × ℂ)`;
- section-extracted fiber sets `fiberU`, `fiberV` with simp lemmas;
- fiber agreement laws `fiberU_eq`, `fiberV_eq`, `eval_agrees`;
- `analyticOn_totalU : AnalyticOn ℂ eval totalU`.

Do **not** add proper-family, unfolded, tubing, or holomorphic-motion fields in that worker.

## Confirmation

This task was completed read-only with respect to repository source code and dependencies. Only the present result artifact was written. No commit was made.
