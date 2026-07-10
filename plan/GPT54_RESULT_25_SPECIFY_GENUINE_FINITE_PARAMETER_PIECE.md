# GPT-5.4 Result 25 — Specify the genuine finite-level parameter piece

## 1. Executive decision

**Decision:** **(1)** a specific sourced parameter piece is ready for a small Lean
specification task.

The correct first genuine finite-level moving-parameter object is **not** the
ambient renormalization window `W°` alone and **not** the frozen-base translate
`ParaPuzzlePieceAt c n`. Following Review 09, the right replacement target is the
**connectedness locus** `M(g)` of a proper unfolded equipped quadratic-like family,
and in the renormalization-window specialization the corresponding little copy
`M◦`.

This is the smallest viable first model because it is:
- independently defined from moving-parameter quadratic-like geometry;
- sourced locally with explicit theorems giving connectedness/fullness and, in a
  canonical window case, homeomorphism to `M`;
- close to the current `LcAtOfShrink` consumer, since it already supplies a
  connected subset of `M` rather than only a connected ambient window.

The immediate next worker task should specify a **connectedness-locus-backed finite
parameter piece family** and the minimal consumer migration for `LcAtOfShrink`.

## 2. Read set and source basis

Per task instructions I read:
- `plan/GPT54_PROGRESS_GREEN_SUBLEVEL_FRONTIER.md`
- `plan/PLAN_04_parameter_connectivity.md`
- `plan/GPT54_RESULT_03_PARAPUZZLE_INTERFACE_AUDIT.md`
- `plan/GPT54_RESULT_05_REVISE_PLAN_AND_RETIRE_DEAD_ROUTES.md`
- `plan/GPT54_RESULT_08_SOURCED_THEOREM_MATCHING_AUDIT.md`
- `plan/GPT54_RESULT_09_SPECIFY_CANONICAL_PARAMETER_PIECE.md`
- `plan/GPT54_REVIEW_09_SPECIFY_CANONICAL_PARAMETER_PIECE.md`
- `Mlc/ParaPuzzleConnectivity.lean`
- `Mlc/LcAtOfShrink.lean`
- `Mlc/Quadratic/Complex/ParaPuzzle.lean`

Primary local source used for the new object:
- `refs/Conformal Geometry and Dynamics of Quadratic Polynomials.pdf`

Supporting programmatic source:
- `refs/2512.24171v1.pdf`

## 3. Concrete classical construction chosen

### 3.1 Chosen construction

I choose the following concrete Option B target:

- for a proper unfolded equipped quadratic-like family `g` over a parameter domain
  `Λ`, the **connectedness locus**
  ```text
  M(g) := { λ ∈ Λ | J(g_λ) is connected }
  ```
  equivalently the locus where the filled Julia set of the fiber is connected;
- in the renormalization-window specialization around a superattracting center
  `c◦`, the corresponding finite combinatorics locus
  ```text
  M◦ = { c ∈ Λ : f_c is renormalizable with combinatorics c◦ } ∪ {root, tip}.
  ```

This choice is forced by Review 09: the ambient window `W°`/`Λ` is not enough,
because the MLC consumer needs a connected set inside `M`, not merely an open
parameter domain.

### 3.2 Exact sourced theorem matches

From `Conformal Geometry and Dynamics of Quadratic Polynomials.pdf`:

#### Theorem 10.1 (local text extraction)

Extracted around lines 11758ff from `pdftotext`:

> “Let `g` be a proper unfolded equipped quadratic-like family over `Λ`. ... the
> corresponding straightening `χ` is a homeomorphism from `Λ` onto `D_{r^2}`
> mapping `M(g)` onto `M`.”

This gives:
- an independently defined parameter family over `Λ`;
- a straightening homeomorphism;
- identification of the connectedness locus `M(g)` with the Mandelbrot set `M`.

#### Corollary 10.3

Extracted around lines 11895ff:

> “The Mandelbrot set `M(g)` is connected and full.”

This is the exact relative connectedness theorem missing from Result 09.

#### Theorem 10.15

Extracted around lines 12149ff:

> “The set `M◦` is canonically homeomorphic to the Mandelbrot set `M`.”

This gives the renormalization-window specialization: a genuine finite parameter
piece candidate already living in the relevant little-copy regime.

### 3.3 Why this is the smallest viable first model

Compared with other candidates:

- **ambient window `Λ` / `W°`:** too weak; `Λ ∩ M` connected does not follow.
- **frozen translated Green target:** not classically sourced as a moving-parameter
  parapuzzle object.
- **full parameter rays/equipotentials graph first:** mathematically natural but a
  larger formalization commitment.

By contrast, `M(g)` / `M◦` already come with the exact connectedness conclusion the
consumer needs, while still being defined from genuine parameter geometry rather
than from connectedness witnesses or exact-image packaging.

## 4. Independent set definition

## 4.1 Mathematical target definitions

The right independent replacement is a two-layer object:

```text
ParameterGraph(base, depth)
ParameterPiece(base, depth)
```

but for the first Lean-facing model the sourced object naturally appears through a
**window + connectedness locus** pair.

A faithful first specification is:

```text
ParameterWindow(base, depth) : Set ℂ
```

an independently defined finite-level parameter domain/window `Λ(base, depth)`
coming from a chosen finite combinatorics class (e.g. a proper unfolded equipped
quadratic-like family or renormalization window);

```text
ParameterGraph(base, depth) : Set ℂ
```

a finite boundary graph/ray-equipotential package cutting out that window,
whenever the source gives it explicitly;

```text
ConnectednessLocus(base, depth) : Set ℂ
```

the locus `M(g)` inside the window, defined by fiber connectedness /
renormalizability of the moving family;

```text
ParameterPiece(base, depth) : Set ℂ := ConnectednessLocus(base, depth) ∩ MandelbrotSet
```

for the first migration target.

### 4.2 Boundary/open/closed convention

For the first consumer-compatible model:
- `ParameterWindow(base, depth)` should be treated as the ambient open/Jordan-like
  domain `Λ` (or renormalization window interior when the source distinguishes
  interior/boundary);
- `ConnectednessLocus(base, depth)` is the closed/full little-copy locus `M(g)` or
  `M◦` inside that window;
- `ParameterPiece(base, depth)` should be the **relative connectedness locus inside
  `M`**, i.e. either exactly `ConnectednessLocus(base, depth)` when it is already a
  subset of `M`, or `ConnectednessLocus(base, depth) ∩ MandelbrotSet` as the safe
  interface.

This avoids defining the piece by connectedness witnesses; instead it is defined
from the moving family’s combinatorial/geometric connectedness locus.

### 4.3 What is explicitly avoided

I do **not** define the piece by:
- `IsConnected` data;
- image of a connected source;
- the frozen Green function `G_c(c' - c)`;
- equality to the current downstream target.

## 5. Theorem matching against task requirements

### 5.1 Component/topology of the parameter object

Exact sourced statements available:

1. **Connected/open/Jordan ambient family domain:**
   Theorem 10.1 gives a parameter domain `Λ` carrying a proper unfolded equipped
   quadratic-like family and a homeomorphism to a disk `D_{r^2}`.
   This gives disk topology for the ambient window.

2. **Relative connectedness locus:**
   Corollary 10.3 states `M(g)` is connected and full.

3. **Canonical little-copy case:**
   Theorem 10.15 states `M◦` is canonically homeomorphic to `M`.

### 5.2 Basepoint membership

At the mathematical level, basepoint membership is immediate once the basepoint is
chosen inside the connectedness locus / little copy corresponding to the selected
finite combinatorics. In Lean terms this should be an explicit hypothesis/field:

```text
base_mem_piece : base ∈ ParameterPiece base depth
```

rather than a hidden consequence.

### 5.3 Antitone nesting

This is **not** supplied directly by the extracted Theorem 10.1 / 10.15 text.
It belongs to the finite-level parapuzzle / parapiece apparatus rather than the
single-window connectedness-locus theorem.

So for Task C:
- connectedness of the candidate piece is sourced now;
- nesting requires either a more refined source theorem for a family of windows, or
  a later formalization of the finite graph/wake structure.

### 5.4 Shrinkage / singleton intersection

Also **not** supplied directly by Theorem 10.1 / 10.15.
Shrinkage remains deep Yoccoz / phase-parameter input, separate from elementary
component topology. This matches the task instruction to distinguish elementary
component facts from deeper theory.

### 5.5 Relative connectedness inside `M`

The strongest currently verified statement is:
- `M(g)` is connected and full (Corollary 10.3);
- `M◦` canonically homeomorphic to `M` (Theorem 10.15).

Thus in the intended renormalization/little-copy setting the candidate piece is
already a connected subset of `M`, not merely an ambient open set.

## 6. Lean-facing API and existing support

## 6.1 Existing repository support

### Existing

- `Mlc/LcAtOfShrink.lean` consumes open sets `ParaPuzzlePieceAt c n` and uses
  connectedness of `ParaPuzzlePieceAt c n ∩ MandelbrotSet`.
- `Mlc/ParaPuzzleConnectivity.lean` proves current connectivity only for the
  frozen-base surrogate.
- `Mlc/Quadratic/Complex/ParaPuzzle.lean` defines the surrogate
  ```lean
  def ParaPuzzlePieceAt (c : ℂ) (n : ℕ) : Set ℂ :=
    {c' | c' - c ∈ DynamicalPuzzlePiece c n 0}
  ```
- Mathlib/repo already support connected components and `connectedComponentIn`, so
  a component-based consumer layer is feasible.

### Missing foundation

- no formalized parameter-ray/equipotential parapuzzle graph family producing real
  finite-level moving parameter pieces;
- no Lean definition yet of proper unfolded equipped quadratic-like family or its
  connectedness locus `M(g)`;
- no sourced theorem yet encoded connecting such a locus to a concrete nested
  depth-indexed family consumed by `LcAtOfShrink`.

## 6.2 Compile-tested prospective signatures

I compile-tested the following shell API in `/tmp/task25_probe.lean`:

```lean
import Mlc.LcAtOfShrink

namespace MLC
open Set
open Quadratic Complex

structure GenuineFiniteParameterPieceFamily where
  ParameterGraph : ℂ → ℕ → Set ℂ
  ParameterPiece : ℂ → ℕ → Set ℂ
  mem_self : ∀ c n, c ∈ ParameterPiece c n
  isOpen_piece : ∀ c n, IsOpen (ParameterPiece c n)
  connected_inter_mandelbrot : ∀ {c : ℂ}, c ∈ MandelbrotSet → ∀ n,
    IsConnected (ParameterPiece c n ∩ MandelbrotSet)
  antitone : ∀ c, Antitone (ParameterPiece c)

structure ConnectednessLocusFamily where
  ParameterWindow : ℂ → ℕ → Set ℂ
  ConnectednessLocus : ℂ → ℕ → Set ℂ
  piece : ℂ → ℕ → Set ℂ
  piece_eq_locus_inter_mandelbrot : ∀ c n,
    piece c n = ConnectednessLocus c n ∩ MandelbrotSet
```

This compiled successfully.

### Classification of declarations

- `GenuineFiniteParameterPieceFamily`: **compile-ready shell**, but mathematically
  still an abstract interface.
- `ConnectednessLocusFamily`: **compile-ready shell** and closer to the sourced
  object because it separates ambient window, connectedness locus, and exported
  piece.
- actual definitions of `ParameterWindow`, `ConnectednessLocus`, and finite
  `ParameterGraph`: **missing foundation**.
- connectedness theorems for concrete instances: **sourced theorem to formalize**.
- elementary membership and “component containing basepoint” lemmas: **elementary**
  once the concrete sets are defined.

## 7. Smallest migration plan for `LcAtOfShrink`

The current consumer needs only:
- openness of neighborhood pieces in ambient parameter space;
- connectedness of the relative piece inside `M`;
- basepoint membership;
- antitone nesting;
- shrinkage.

Therefore the smallest code change is **not** to redefine `ParaPuzzlePieceAt`
immediately. The best migration is:

### Recommended migration option

**Generalize `LcAtOfShrink` over an abstract piece family with separately proved
hypotheses.**

Why this is smallest:
- it preserves already-proved generic topology in `LcAtOfShrink`;
- it detaches the local-connectivity consumer from the frozen Green-translate
  surrogate;
- it allows the first concrete moving-parameter family to be introduced later,
  theorem-by-theorem.

### Theorems that currently depend on the frozen connectivity hook

From `Mlc/LcAtOfShrink.lean`, the pieces fed by
`green_sublevel_translate_inter_mandelbrot_connected` propagate through:
- `para_puzzle_piece_induced_connected_of_data`
- `para_puzzle_piece_induced_connected`
- `lc_at_of_shrink_of_data`
- `lc_at_of_shrink`
- the transport/subset variants derived from these same hooks.

Those are the minimal interface points to decouple from
`Quadratic.ParaPuzzlePieceAt`.

## 8. Bounded first Lean implementation task

The first non-axiomatic implementation step should be:

> **Introduce an abstract component-based local-connectivity consumer for a generic
> parameter piece family, separating ambient window, exported piece, relative
> connectedness, and nesting from the current frozen `ParaPuzzlePieceAt`.
>**

This is better than immediately chasing parameter rays/equipotentials in Lean,
because it creates the correct consumer shape for the sourced object `M(g)` / `M◦`
without pretending the geometry is already formalized.

Concretely, the next worker should implement a generic theorem schema replacing
hard-coded uses of `ParaPuzzlePieceAt` in `LcAtOfShrink` by a family parameter.
That is real progress and does not merely rename the connectivity assumption.

## 9. Parameter-class limitations

This specification honestly covers only the first sourced finite-level model:
- proper unfolded equipped quadratic-like families and renormalization windows;
- connectedness-locus / little-copy pieces given by Theorem 10.1, Corollary 10.3,
  and Theorem 10.15.

It does **not yet** supply:
- a full depth-indexed nested parapuzzle family;
- shrinkage to a singleton;
- the remaining pseudo-Siegel / virtual Molecule program from `2512.24171`.

The survey `2512.24171v1.pdf` remains supportive background only: it confirms the
centrality of puzzle-parapuzzle relations and documents that remaining cases are
still programmatic (`Problem 4.3`, `Problem 4.4`), so it should not be used to
overclaim current finite-level coverage.

## 10. Exact commands run

```bash
git --no-pager status --short
pdftotext 'refs/Conformal Geometry and Dynamics of Quadratic Polynomials.pdf' /tmp/cgdqp.txt
grep -n "Theorem 10.1\|Theorem 10.15\|Corollary 10.3\|connectedness locus\|proper unfolded equipped quadratic-like family\|renormalization locus\|homeomorphic to the Mandelbrot\|M(g)\|M◦\|M^o" /tmp/cgdqp.txt | head -80
sed -n '11750,11815p' /tmp/cgdqp.txt
sed -n '11888,11910p' /tmp/cgdqp.txt
sed -n '12140,12175p' /tmp/cgdqp.txt
pdftotext 'refs/2512.24171v1.pdf' /tmp/2512.txt
grep -n "parapuzzle\|Almost-Linear puzzle-parapuzzle relation\|bounded-type\|virtual Molecule\|Problem 4.3\|Problem 4.4\|Theorem 4.1\|Molecule" /tmp/2512.txt | head -80
lake env lean /tmp/task25_probe.lean
```

## 11. Complete `git status --short`

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
?? plan/GPT54_PROMPT_22_CONCRETE_TUBE_LOCAL_TRIVIALIZATION_ADAPTER.md
?? plan/GPT54_PROMPT_23_CORRECT_CONCRETE_TUBE_CHART_HOMEOMORPH.md
?? plan/GPT54_PROMPT_24_PROVE_TUBE_FIBER_HOMEOMORPH_DISK.md
?? plan/GPT54_PROMPT_25_SPECIFY_GENUINE_FINITE_PARAMETER_PIECE.md
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
?? plan/GPT54_RESULT_21_QUADRATIC_LIKE_TUBE_BUNDLE_AUDIT.md
?? plan/GPT54_RESULT_22_CONCRETE_TUBE_LOCAL_TRIVIALIZATION_ADAPTER.md
?? plan/GPT54_RESULT_23_CORRECT_CONCRETE_TUBE_CHART_HOMEOMORPH.md
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
?? plan/GPT54_REVIEW_21_QUADRATIC_LIKE_TUBE_BUNDLE_AUDIT.md
?? plan/GPT54_REVIEW_22_CONCRETE_TUBE_LOCAL_TRIVIALIZATION_ADAPTER.md
?? plan/GPT54_REVIEW_23_CORRECT_CONCRETE_TUBE_CHART_HOMEOMORPH.md
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
?? plan/GPT54_TASK_22_CONCRETE_TUBE_LOCAL_TRIVIALIZATION_ADAPTER.md
?? plan/GPT54_TASK_23_CORRECT_CONCRETE_TUBE_CHART_HOMEOMORPH.md
?? plan/GPT54_TASK_24_PROVE_TUBE_FIBER_HOMEOMORPH_DISK.md
?? plan/GPT54_TASK_25_SPECIFY_GENUINE_FINITE_PARAMETER_PIECE.md
```

## 12. Compliance confirmation

- I did **not** edit repository Lean sources.
- I did **not** edit prior plan artifacts or `plan.md`.
- I used `/tmp` for source extraction and Lean probes.
- The only repository write for this task is this result file.
- No commit was made.

## 13. Exact next worker task

**Next worker task:** define a generic `LcAtOfShrink` consumer interface for a
connectedness-locus-backed parameter piece family, separating ambient window,
connectedness locus, exported piece, relative connectedness, nesting, and
shrinkage; then identify the minimal theorem package needed for a first concrete
`M(g)` / `M◦` instance.
