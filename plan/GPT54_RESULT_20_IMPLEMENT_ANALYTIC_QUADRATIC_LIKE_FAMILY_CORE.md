# GPT-5.4 Result 20: Implement analytic quadratic-like family core

## Executive summary

Implemented the requested scoped analytic family **core** in:

- `Mlc/AnalyticQuadraticLikeFamilyCore.lean`

and added the corresponding library import in:

- `Mlc.lean`

This implementation deliberately stops at the minimal analytic core confirmed by Results 18–19. It does **not** add tube fiber-bundle/local-triviality data, properness, unfolding, equipment, holomorphic motion, tubing, straightening, or connectedness-locus theorems.

## Implemented declarations

New namespace/module:

- `namespace Molecule`
- `structure AnalyticQuadraticLikeFamilyCore`
- `namespace AnalyticQuadraticLikeFamilyCore`

Primitive structure fields implemented exactly in the approved shape:

- `parameterSet : Set ℂ`
- `isOpen_parameterSet : IsOpen parameterSet`
- `fiber : parameterSet → GenuineBMol`
- `totalU totalV : Set (ℂ × ℂ)`
- scoping laws for `totalU`, `totalV`
- `isOpen_totalU`, `isOpen_totalV`
- `sectionU_eq`, `sectionV_eq`
- `eval : ℂ × ℂ → ℂ`
- `eval_agrees`
- `analyticOn_totalU : AnalyticOn ℂ eval totalU`

Derived namespace API implemented outside the structure:

- `sectionU`
- `sectionV`
- `[simp] mem_sectionU_iff`
- `[simp] mem_sectionV_iff`
- `sectionU_eq_fiberU`
- `sectionV_eq_fiberV`
- `eval_agrees_section`
- `fst_mem_parameterSet_of_mem_totalU`
- `fst_mem_parameterSet_of_mem_totalV`

## Documentation/scope compliance

The module docstring and structure docstring explicitly state that this is only a
core and that it omits:

- source-level tube fiber-bundle / local-triviality data;
- proper / unfolded / equipped hypotheses;
- holomorphic motion;
- tubing;
- straightening.

No derived sections or membership lemmas were stored as structure fields.

## Verification

### 1. Focused module check

Command:

```bash
cd /home/kir/pers/mlc && lake env lean Mlc/AnalyticQuadraticLikeFamilyCore.lean
```

Outcome:

- passed (`exit code 0`)

### 2. Full build

Command:

```bash
cd /home/kir/pers/mlc && lake build
```

Outcome:

- passed (`exit code 0`)
- only pre-existing warnings appeared in unrelated files

### 3. Placeholder audit

Command:

```bash
grep -n -E 'axiom|sorry|admit' Mlc/AnalyticQuadraticLikeFamilyCore.lean Mlc.lean
```

Outcome:

- no matches

## Exact diff

```diff
diff --git a/Mlc.lean b/Mlc.lean
index dd18b5f..27bb3ed 100644
--- a/Mlc.lean
+++ b/Mlc.lean
@@ -4,6 +4,7 @@ import Mlc.MainConjecture
 import Mlc.DirectRoute
 import Mlc.ParaPuzzleContainment
 import Mlc.BMolFilledJulia
 import Mlc.GenuineBMol
+import Mlc.AnalyticQuadraticLikeFamilyCore
 import Mlc.InconsistencyRoute
 import Mlc.Quadratic.Complex.Bottcher.BottcherOnM
 import Mlc.Quadratic.Complex.Bottcher.BottcherOnMTheory

diff --git a/Mlc/AnalyticQuadraticLikeFamilyCore.lean b/Mlc/AnalyticQuadraticLikeFamilyCore.lean
new file mode 100644
index 0000000..8fa730b
--- /dev/null
+++ b/Mlc/AnalyticQuadraticLikeFamilyCore.lean
@@ -0,0 +1,88 @@
+import Molecule.BMol
+import Mlc.GenuineBMol
+import Mathlib.Analysis.Analytic.Basic
+
+/-!
+# Analytic quadratic-like family core
+
+This module implements a deliberately incomplete core for analytic quadratic-like
+family data over a parameter domain. It records only the scoped total-source /
+total-target sets, their fiberwise agreement with `GenuineBMol`, and joint
+analyticity on the actual total source.
+
+It intentionally omits the source text's stronger tube fiber-bundle /
+local-triviality structure as well as all later theorem hypotheses such as
+properness, unfolding, equipment, holomorphic motion, tubing, and straightening.
+-/
+
+open Set
+open Complex
+
+namespace Molecule
+
+/--
+A minimal analytic quadratic-like family core over a parameter domain.
+
+This is only the scoped analytic core used for later development. It does **not**
+claim to be the full source-defined quadratic-like family object: in particular it
+omits tube fiber-bundle / local-triviality data and all later proper / unfolded /
+equipped hypotheses.
+-/
+structure AnalyticQuadraticLikeFamilyCore where
+  parameterSet : Set ℂ
+  isOpen_parameterSet : IsOpen parameterSet
+  fiber : parameterSet → GenuineBMol
+  totalU : Set (ℂ × ℂ)
+  totalV : Set (ℂ × ℂ)
+  scoped_totalU : totalU ⊆ parameterSet ×ˢ (Set.univ : Set ℂ)
+  scoped_totalV : totalV ⊆ parameterSet ×ˢ (Set.univ : Set ℂ)
+  isOpen_totalU : IsOpen totalU
+  isOpen_totalV : IsOpen totalV
+  sectionU_eq (c : parameterSet) : {z : ℂ | (c.1, z) ∈ totalU} = (fiber c : BMol).U
+  sectionV_eq (c : parameterSet) : {z : ℂ | (c.1, z) ∈ totalV} = (fiber c : BMol).V
+  eval : ℂ × ℂ → ℂ
+  eval_agrees (c : parameterSet) {z : ℂ} (hz : (c.1, z) ∈ totalU) :
+    eval (c.1, z) = (fiber c : BMol).f z
+  analyticOn_totalU : AnalyticOn ℂ eval totalU
+
+namespace AnalyticQuadraticLikeFamilyCore
+
+/-- The source section of the total domain over a parameter value. -/
+def sectionU (F : AnalyticQuadraticLikeFamilyCore) (c : F.parameterSet) : Set ℂ :=
+  {z : ℂ | (c.1, z) ∈ F.totalU}
+
+/-- The target section of the total codomain over a parameter value. -/
+def sectionV (F : AnalyticQuadraticLikeFamilyCore) (c : F.parameterSet) : Set ℂ :=
+  {z : ℂ | (c.1, z) ∈ F.totalV}
+
+@[simp] lemma mem_sectionU_iff (F : AnalyticQuadraticLikeFamilyCore) (c : F.parameterSet)
+    (z : ℂ) : z ∈ F.sectionU c ↔ (c.1, z) ∈ F.totalU :=
+  Iff.rfl
+
+@[simp] lemma mem_sectionV_iff (F : AnalyticQuadraticLikeFamilyCore) (c : F.parameterSet)
+    (z : ℂ) : z ∈ F.sectionV c ↔ (c.1, z) ∈ F.totalV :=
+  Iff.rfl
+
+lemma sectionU_eq_fiberU (F : AnalyticQuadraticLikeFamilyCore) (c : F.parameterSet) :
+    F.sectionU c = (F.fiber c : BMol).U :=
+  F.sectionU_eq c
+
+lemma sectionV_eq_fiberV (F : AnalyticQuadraticLikeFamilyCore) (c : F.parameterSet) :
+    F.sectionV c = (F.fiber c : BMol).V :=
+  F.sectionV_eq c
+
+lemma eval_agrees_section (F : AnalyticQuadraticLikeFamilyCore) (c : F.parameterSet) {z : ℂ}
+    (hz : z ∈ F.sectionU c) : F.eval (c.1, z) = (F.fiber c : BMol).f z :=
+  F.eval_agrees c hz
+
+lemma fst_mem_parameterSet_of_mem_totalU (F : AnalyticQuadraticLikeFamilyCore) {p : ℂ × ℂ}
+    (hp : p ∈ F.totalU) : p.1 ∈ F.parameterSet :=
+  (F.scoped_totalU hp).1
+
+lemma fst_mem_parameterSet_of_mem_totalV (F : AnalyticQuadraticLikeFamilyCore) {p : ℂ × ℂ}
+    (hp : p ∈ F.totalV) : p.1 ∈ F.parameterSet :=
+  (F.scoped_totalV hp).1
+
+end AnalyticQuadraticLikeFamilyCore
+
+end Molecule
```

## Changed files

Authorized changes only:

- `Mlc/AnalyticQuadraticLikeFamilyCore.lean` (new)
- `Mlc.lean` (import added)
- `plan/GPT54_RESULT_20_IMPLEMENT_ANALYTIC_QUADRATIC_LIKE_FAMILY_CORE.md` (this report)

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
```

## Confirmation

No vendored dependencies were edited. No `axiom`, `sorry`, or `admit` were introduced. No commit was made.
