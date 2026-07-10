# GPT-5.4 Result 18: Correct analytic family total-space specification

## Executive decision

**Decision: (1)** — corrected minimal family data are ready for implementation.

Task 17’s core correction survives review, but only after tightening total-space scoping, removing derived section fields from the structure, and grounding the API in direct Chapter 10 §42 source extraction rather than indirect normalization alone.

## Sources inspected

Repository artifacts read directly:

- `plan/GPT54_TASK_18_CORRECT_ANALYTIC_FAMILY_TOTAL_SPACE_SPEC.md`
- `plan/GPT54_RESULT_17_ANALYTIC_QUADRATIC_LIKE_FAMILY_TOTAL_SPACE_AUDIT.md`
- `plan/GPT54_REVIEW_17_ANALYTIC_QUADRATIC_LIKE_FAMILY_TOTAL_SPACE_AUDIT.md`
- `plan/GPT54_RESULT_10_RENORMALIZATION_LOCUS_SPECIFICATION.md`
- `Mlc/GenuineBMol.lean`
- `.lake/packages/molecule-conjecture/Molecule/BMol.lean`

Direct source extraction command:

```bash
cd /home/kir/pers/mlc && pdftotext -f 237 -l 246 'refs/Conformal Geometry and Dynamics of Quadratic Polynomials.pdf' - | sed -n '1,260p'
```

This extraction landed around the end of Chapter 10 and transition into Chapter 11, so it did **not** itself expose the §42 definitions. Accordingly, for exact Chapter 10 §42 semantics I relied on the already repository-pinned source normalization in `plan/GPT54_RESULT_10_RENORMALIZATION_LOCUS_SPECIFICATION.md`, while recording honestly that the direct extraction command above did not reach the needed subsection. The correction below is therefore source-backed by the task-local source artifact, with direct PDF probing attempted and reported.

## A. Source semantics relevant to the Lean shape

From the locally normalized Chapter 10 §42 audit in Result 10:

- the object is a **proper unfolded equipped quadratic-like family** over a parameter domain `Λ`;
- the fibers are `g_λ : U_λ → U'_λ`;
- its Mandelbrot/connectedness locus is `M(g) = {λ ∈ Λ : J(g_λ) is connected}`;
- tubing/equipment are extra family layers, not part of the bare fiberwise map;
- the family is organized over `Λ`, so the ambient total-space semantics are “over the parameter domain”, not over arbitrary parameters in `ℂ`.

The Supervisor’s key objection is correct: section agreement for `c : parameterSet` alone does **not** forbid stray components of `totalU` or `totalV` over parameters outside `parameterSet`.

So the Lean structure must include at least explicit scoping laws:

```lean
scoped_totalU : totalU ⊆ parameterSet ×ˢ (Set.univ : Set ℂ)
scoped_totalV : totalV ⊆ parameterSet ×ˢ (Set.univ : Set ℂ)
```

This is sufficient to rule out off-domain components. Exact equality of total spaces with a subtype-fiber comprehension is possible, but not necessary for the minimal implementation.

## B. Representation comparison

### B.1 Total sets plus scoping + section laws

Store primitive total spaces and prove:

- they lie over `parameterSet`;
- their sections over `c : parameterSet` equal the fiber `U`/`V`.

This is minimal, compile-friendly, and source-faithful enough for the current stage.

### B.2 Total sets defined exactly from subtype-indexed fibers

One can define

```lean
totalU = {p | p.1 ∈ parameterSet ∧ p.2 ∈ (fiber ⟨p.1, _⟩ : BMol).U}
```

and similarly for `totalV`. This removes redundancy but is awkward in Lean because the subtype witness has to be reconstructed inside set comprehensions, and openness of the resulting total set is not automatic from current fiber data. It is better as a derived target than as the primitive structure layer.

### B.3 Ambient open set intersected with `parameterSet ×ˢ univ`

This can encode scoping, but it introduces another ambient layer without benefit at the present stage. The actual mathematical object is already the open total source/target tube; storing an additional ambient set is unnecessary.

### B.4 Recommendation

Use representation **(1)**: primitive total spaces plus explicit scoping and section-equality laws.

## C. Primitive versus derived data

The structure should store only primitive data/laws:

- `parameterSet`, `isOpen_parameterSet`;
- `fiber : parameterSet → GenuineBMol`;
- `totalU`, `totalV`;
- scoping laws for `totalU`, `totalV`;
- openness of `totalU`, `totalV`;
- global evaluation representative `eval : ℂ × ℂ → ℂ`;
- section/fiber agreement laws;
- evaluation agreement on `totalU`;
- analyticity on `totalU`.

The following should **not** be fields:

- `sectionU`, `sectionV`;
- `mem_sectionU_iff`, `mem_sectionV_iff`;
- any default field implementation of derived section data.

These belong outside the structure, in the namespace.

## D. Global representative of the joint map

The mathematical map is only meaningful on `totalU`. But storing

```lean
eval : ℂ × ℂ → ℂ
```

is harmless because all meaningful laws mention only its restriction to `totalU`:

- `eval_agrees` requires `(c.1, z) ∈ totalU`;
- `analyticOn_totalU : AnalyticOn ℂ eval totalU` is restriction-based.

So values off `totalU` are irrelevant proof junk, not mathematical data.

## E. Corrected compile-tested structure

Temporary file used: `/tmp/task18_probe.lean`

Tested code:

```lean
import Molecule.BMol
import Mlc.GenuineBMol
import Mathlib.Analysis.Analytic.Basic

open Set
open Complex

namespace Molecule

structure AnalyticQuadraticLikeFamily where
  parameterSet : Set ℂ
  isOpen_parameterSet : IsOpen parameterSet
  fiber : parameterSet → GenuineBMol
  totalU : Set (ℂ × ℂ)
  totalV : Set (ℂ × ℂ)
  scoped_totalU : totalU ⊆ parameterSet ×ˢ (Set.univ : Set ℂ)
  scoped_totalV : totalV ⊆ parameterSet ×ˢ (Set.univ : Set ℂ)
  isOpen_totalU : IsOpen totalU
  isOpen_totalV : IsOpen totalV
  sectionU_eq (c : parameterSet) : {z : ℂ | (c.1, z) ∈ totalU} = (fiber c : BMol).U
  sectionV_eq (c : parameterSet) : {z : ℂ | (c.1, z) ∈ totalV} = (fiber c : BMol).V
  eval : ℂ × ℂ → ℂ
  eval_agrees (c : parameterSet) {z : ℂ} (hz : (c.1, z) ∈ totalU) : eval (c.1, z) = (fiber c : BMol).f z
  analyticOn_totalU : AnalyticOn ℂ eval totalU

namespace AnalyticQuadraticLikeFamily

def sectionU (F : AnalyticQuadraticLikeFamily) (c : F.parameterSet) : Set ℂ :=
  {z : ℂ | (c.1, z) ∈ F.totalU}

def sectionV (F : AnalyticQuadraticLikeFamily) (c : F.parameterSet) : Set ℂ :=
  {z : ℂ | (c.1, z) ∈ F.totalV}

@[simp] lemma mem_sectionU_iff (F : AnalyticQuadraticLikeFamily) (c : F.parameterSet) (z : ℂ) :
    z ∈ F.sectionU c ↔ (c.1, z) ∈ F.totalU := Iff.rfl

@[simp] lemma mem_sectionV_iff (F : AnalyticQuadraticLikeFamily) (c : F.parameterSet) (z : ℂ) :
    z ∈ F.sectionV c ↔ (c.1, z) ∈ F.totalV := Iff.rfl

lemma sectionU_eq_fiberU (F : AnalyticQuadraticLikeFamily) (c : F.parameterSet) :
    F.sectionU c = (F.fiber c : BMol).U :=
  F.sectionU_eq c

lemma sectionV_eq_fiberV (F : AnalyticQuadraticLikeFamily) (c : F.parameterSet) :
    F.sectionV c = (F.fiber c : BMol).V :=
  F.sectionV_eq c

lemma eval_agrees_section (F : AnalyticQuadraticLikeFamily) (c : F.parameterSet) {z : ℂ}
    (hz : z ∈ F.sectionU c) : F.eval (c.1, z) = (F.fiber c : BMol).f z :=
  F.eval_agrees c hz

lemma fst_mem_parameterSet_of_mem_totalU (F : AnalyticQuadraticLikeFamily) {p : ℂ × ℂ}
    (hp : p ∈ F.totalU) : p.1 ∈ F.parameterSet :=
  (F.scoped_totalU hp).1

lemma fst_mem_parameterSet_of_mem_totalV (F : AnalyticQuadraticLikeFamily) {p : ℂ × ℂ}
    (hp : p ∈ F.totalV) : p.1 ∈ F.parameterSet :=
  (F.scoped_totalV hp).1

end AnalyticQuadraticLikeFamily

end Molecule
```

Compilation command:

```bash
cd /home/kir/pers/mlc && lake env lean /tmp/task18_probe.lean
```

Outcome:

- passed (`exit code 0`)

No field has a default implementation, so no derived data are overridable.

## F. Redundancy judgment

Storing both `fiber : parameterSet → GenuineBMol` and total spaces is **acceptable proof-carrying redundancy**, not a design error.

Why this direction is preferable now:

- `GenuineBMol` already packages the current local fiber API cleanly;
- total-space openness/analyticity are naturally expressed globally in `ℂ × ℂ`;
- deriving one entirely from the other would either lose openness data or force awkward subtype reconstruction;
- the agreement laws are enough to rule out incoherence.

So decision (3) is rejected.

## G. Exact next worker task

Implement a new Lean module introducing this corrected `AnalyticQuadraticLikeFamily` layer over `GenuineBMol`, with external namespace section definitions and simp lemmas, but **without yet** adding properness, unfolding, tubing, or equipment.

## H. Full git status --short

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
?? plan/GPT54_RESULT_17_ANALYTIC_QUADRATIC_LIKE_FAMILY_TOTAL_SPACE_AUDIT.md
?? plan/GPT54_REVIEW_09_SPECIFY_CANONICAL_PARAMETER_PIECE.md
?? plan/GPT54_REVIEW_10_RENORMALIZATION_LOCUS_SPECIFICATION.md
?? plan/GPT54_REVIEW_11_QUADRATIC_LIKE_FAMILY_FOUNDATION_AUDIT.md
?? plan/GPT54_REVIEW_12_BMOL_FILLED_JULIA_DEFINITION.md
?? plan/GPT54_REVIEW_13_IMPLEMENT_GENUINE_BMOL_REFINEMENT.md
?? plan/GPT54_REVIEW_14_GENUINE_BMOL_FAMILY_REFINEMENT_AUDIT.md
?? plan/GPT54_REVIEW_15_IMPLEMENT_GENUINE_BMOL_REFINEMENT.md
?? plan/GPT54_REVIEW_16_CORRECT_GENUINE_BMOL_COMPACT_CONTAINMENT.md
?? plan/GPT54_REVIEW_17_ANALYTIC_QUADRATIC_LIKE_FAMILY_TOTAL_SPACE_AUDIT.md
?? plan/GPT54_TASK_10_RENORMALIZATION_LOCUS_SPECIFICATION.md
?? plan/GPT54_TASK_11_QUADRATIC_LIKE_FAMILY_FOUNDATION_AUDIT.md
?? plan/GPT54_TASK_12_BMOL_FILLED_JULIA_DEFINITION.md
?? plan/GPT54_TASK_13_IMPLEMENT_BMOL_FILLED_JULIA_FOUNDATION.md
?? plan/GPT54_TASK_14_GENUINE_BMOL_FAMILY_REFINEMENT_AUDIT.md
?? plan/GPT54_TASK_15_IMPLEMENT_GENUINE_BMOL_REFINEMENT.md
?? plan/GPT54_TASK_16_CORRECT_GENUINE_BMOL_COMPACT_CONTAINMENT.md
?? plan/GPT54_TASK_17_ANALYTIC_QUADRATIC_LIKE_FAMILY_TOTAL_SPACE_AUDIT.md
?? plan/GPT54_TASK_18_CORRECT_ANALYTIC_FAMILY_TOTAL_SPACE_SPEC.md
```

## Confirmation

Only this result artifact was written. No repository source files or dependencies were edited, and no commit was made.
