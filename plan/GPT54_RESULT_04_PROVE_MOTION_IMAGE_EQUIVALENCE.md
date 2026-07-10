# GPT54 Result 04 — Prove motion-image equivalence

## Outcome

Completed the authorized task by editing only:

- `Mlc/Quadratic/Complex/Bottcher/Slodkowski.lean`

and proving, with no `axiom`/`sorry`/`admit`, the requested theorem:

```lean
theorem paraPieceIsMotionImage_iff_connected (c : ℂ) (n : ℕ) :
    ParaPieceIsMotionImage c n ↔
      IsConnected
        ({c' | green_function c (c' - c) < (1 / 2 : ℝ) ^ n} ∩ MandelbrotSet)
```

## What changed

### 1. Added reusable identity motion

Inserted at `Mlc/Quadratic/Complex/Bottcher/Slodkowski.lean:101`:

```lean
noncomputable def identitySpaceHolomorphicMotion (E : Set ℂ) :
    SpaceHolomorphicMotion E
```

Implementation details:
- `f := fun _ z => z`
- holomorphy domain `U := Set.univ`
- `h_space_holo` from `differentiableOn_id`
- used as the reverse-direction witness with time `t = 0`

### 2. Added the equivalence theorem

Inserted at `Mlc/Quadratic/Complex/Bottcher/Slodkowski.lean:134`:

```lean
theorem paraPieceIsMotionImage_iff_connected (c : ℂ) (n : ℕ) :
    ParaPieceIsMotionImage c n ↔
      IsConnected
        ({c' | green_function c (c' - c) < (1 / 2 : ℝ) ^ n} ∩ MandelbrotSet)
```

Proof structure:
- forward direction: reuses
  `isConnected_greenSublevel_inter_mandelbrot_of_motionImage c n`
- reverse direction:
  - choose
    `E = {c' | green_function c (c' - c) < (1 / 2 : ℝ) ^ n} ∩ MandelbrotSet`
  - choose `H = identitySpaceHolomorphicMotion E`
  - choose `t = 0`
  - prove `0 ∈ Metric.ball (0 : ℂ) 1`
  - the image equality is by extensionality/simp

### 3. Nearby documentation update

Added a docstring directly on `paraPieceIsMotionImage_iff_connected` explaining that `ParaPieceIsMotionImage` is exact connectivity packaging for its target set.

## Source diff

```diff
diff --git a/Mlc/Quadratic/Complex/Bottcher/Slodkowski.lean b/Mlc/Quadratic/Complex/Bottcher/Slodkowski.lean
index 0abd061..ed20a02 100644
--- a/Mlc/Quadratic/Complex/Bottcher/Slodkowski.lean
+++ b/Mlc/Quadratic/Complex/Bottcher/Slodkowski.lean
@@ -96,6 +96,23 @@ def ParaPieceIsMotionImage (c : ℂ) (n : ℕ) : Prop :=
     t ∈ Metric.ball (0 : ℂ) 1 ∧ IsConnected E ∧
       H.f t '' E = {c' | green_function c (c' - c) < (1 / 2 : ℝ) ^ n} ∩ MandelbrotSet
 
+/-- The identity motion on any set, viewed as a space-holomorphic motion on the
+whole plane. This packages no geometric input beyond the set itself. -/
+noncomputable def identitySpaceHolomorphicMotion (E : Set ℂ) :
+    SpaceHolomorphicMotion E where
+  f := fun _ z => z
+  h_zero := by intro z _; rfl
+  h_inj := by intro _ _ a _ b _ h; exact h
+  h_holo := by
+    intro z _
+    simpa using differentiableAt_id.differentiableWithinAt
+  U := Set.univ
+  hEU := by intro z hz; trivial
+  hU_open := isOpen_univ
+  h_space_holo := by
+    intro _ _
+    simpa using differentiableOn_id
+
 /-- **Reduction of frontier axiom A to the correspondence.** If the parameter
 puzzle piece is the space-holomorphic-motion image of a connected reference set,
 then it is connected. This discharges
@@ -111,6 +128,23 @@ theorem isConnected_greenSublevel_inter_mandelbrot_of_motionImage
   rw [← himg]
   exact H.isConnected_image ht hE
 
+/-- `ParaPieceIsMotionImage` is exactly connectivity packaging for its target set:
+the forward implication transports connectedness along a motion image, while the
+reverse implication uses the identity space-holomorphic motion. -/
+theorem paraPieceIsMotionImage_iff_connected (c : ℂ) (n : ℕ) :
+    ParaPieceIsMotionImage c n ↔
+      IsConnected
+        ({c' | green_function c (c' - c) < (1 / 2 : ℝ) ^ n} ∩ MandelbrotSet) := by
+  constructor
+  · intro h
+    exact isConnected_greenSublevel_inter_mandelbrot_of_motionImage c n h
+  · intro hconn
+    refine ⟨{c' | green_function c (c' - c) < (1 / 2 : ℝ) ^ n} ∩ MandelbrotSet,
+      identitySpaceHolomorphicMotion _, 0, ?_, hconn, ?_⟩
+    · simpa [Metric.mem_ball, dist_zero_right]
+    · ext z
+      simp [identitySpaceHolomorphicMotion]
+
 /-- For `t` in the unit disk, `1 + t ≠ 0` (used to build injective scaling
 slices). -/
 lemma one_add_ne_zero_of_mem_ball {t : ℂ} (ht : t ∈ Metric.ball (0 : ℂ) 1) :
```

## Verification

### 1. Targeted Lean check

Command:

```bash
lake env lean Mlc/Quadratic/Complex/Bottcher/Slodkowski.lean
```

Outcome:
- **passed**
- produced two pre-existing/local linter-style warnings in this file (`try 'simp' instead of 'simpa'`), but no errors

### 2. Build

Command:

```bash
make build
```

Outcome:
- **passed**
- build completed successfully
- emitted unrelated existing warnings elsewhere in the repository

### 3. Axiom/sorry check

Command:

```bash
make check
```

Outcome:
- **passed**
- reported:

```text
✅ The proof of 'MLC.mlc_conjecture' is free of 'sorry'.
All axioms used:
- Quot.sound
- propext
- Classical.choice
- MLC.green_sublevel_translate_inter_mandelbrot_connected_straddling
- MLC.residualOpenVirtualNearMoleculeAxiom
```

This task introduced **no new axioms**. The frontier axiom set is unchanged.

## Final theorem type

```lean
theorem paraPieceIsMotionImage_iff_connected (c : ℂ) (n : ℕ) :
    ParaPieceIsMotionImage c n ↔
      IsConnected
        ({c' | green_function c (c' - c) < (1 / 2 : ℝ) ^ n} ∩ MandelbrotSet)
```

## Constraints compliance

- Edited only the authorized Lean file and this result report.
- No new `axiom`, `sorry`, or `admit`.
- No change to `green_sublevel_translate_inter_mandelbrot_connected_straddling`.
- No change to the frontier architecture beyond exposing that `ParaPieceIsMotionImage` is equivalent to connectedness of its exact target.
- No commit created.
- Preserved pre-existing workspace changes.

## Complete `git status --short`

```text
 M Mlc/ParaPuzzleCarvingReduction.lean
 M Mlc/Quadratic/Complex/Bottcher/Slodkowski.lean
?? plan/GPT54_RESULT_01_PARAMETER_CONNECTIVITY_AUDIT.md
?? plan/GPT54_RESULT_02_FORMALIZE_CARVING_NOGO.md
?? plan/GPT54_RESULT_03_PARAPUZZLE_INTERFACE_AUDIT.md
?? plan/GPT54_REVIEW_01_PARAMETER_CONNECTIVITY_AUDIT.md
?? plan/GPT54_REVIEW_02_FORMALIZE_CARVING_NOGO.md
?? plan/GPT54_REVIEW_03_PARAPUZZLE_INTERFACE_AUDIT.md
?? plan/GPT54_TASK_01_PARAMETER_CONNECTIVITY_AUDIT.md
?? plan/GPT54_TASK_02_FORMALIZE_CARVING_NOGO.md
?? plan/GPT54_TASK_03_PARAPUZZLE_INTERFACE_AUDIT.md
?? plan/GPT54_TASK_04_PROVE_MOTION_IMAGE_EQUIVALENCE.md
```

## Interpretation

This task confirms the architectural point from the parapuzzle audit: in the current repository, `ParaPieceIsMotionImage` is not a smaller non-circular Douady–Hubbard hypothesis. It is equivalent to the connectedness claim for the exact translated Green-sublevel target, because the reverse implication can always be witnessed by the identity space-holomorphic motion.
