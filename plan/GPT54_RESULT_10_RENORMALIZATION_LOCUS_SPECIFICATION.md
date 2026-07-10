# GPT-5.4 Result 10: Specify the connected renormalization locus inside a window

## 1. Executive decision

**Decision:** **(2) architecture ready but quadratic-like family foundations missing.**

Task 09’s “connected window” formulation was too coarse. The source-backed object
relevant to little Mandelbrot copies is not just the open complex renormalization
window `W° = Λ`, but the **renormalization / connectedness locus inside that
window**:

- for a proper unfolded equipped quadratic-like family `g` over `Λ`, the source
  defines the connectedness locus
  `M(g) = {λ ∈ Λ | J(g_λ) is connected}`;
- for the concrete quadratic family over a primitive complex renormalization
  window, Lyubich defines
  `M° = {c ∈ Λ : f_c is renormalizable with combinatorics c°} ∪ {root, tip}`;
- Theorem 10.15 says **`M°`**, not `Λ` and not merely `Λ ∩ M`, is canonically
  homeomorphic to the Mandelbrot set `M`.

This gives a genuine, source-matched **restricted parameter continuum** with
connectedness/fullness coming from a canonical homeomorphism to `M`.

However, one such little-copy locus does **not** by itself provide the neighborhood
basis or shrink-to-point family required by `LcAtOfShrink`. It is useful as a
foundation for the infinitely-renormalizable nested little-copy route, not as an
immediate replacement for the full local-connectivity consumer.

So the mathematical architecture is now clearer, but the repo lacks the necessary
**quadratic-like family / connectedness-locus / straightening** foundations.

## 2. Three-set comparison with exact sources

Fix a **primitive superattracting** base parameter `c°` of period `p > 1` and the
associated complex renormalization window `Λ = Λ_{c°}` from Chapter 7 §45.2.1.

### 2.1 Set A: the open complex renormalization window `W° = Λ`

**Source:** `refs/Conformal Geometry and Dynamics of Quadratic Polynomials.pdf`
- Chapter 7 §45.2.1, PDF pages around 205–206
- Proposition 7.41 / Proposition 7.42

**Definition from source:**
Lyubich defines an **open parameter domain** `W° ≡ W_{c°}` / `Λ` attached to the
base hyperbolic map. It is bounded by finitely many parameter rays and truncated
by equipotential arcs, with boundary points named **root** and **tip**.

Permitted short quote:
- “open parameter domain `W◦`”
- “bounded by two parameter rays … and two … rays … truncated by the equipotential”

**What is proved:**
- Proposition 7.41: the almost-renormalization boundary configuration moves
  holomorphically over `W°`.
- Proposition 7.42: all `f_c`, `c ∈ W°`, are renormalizable with period `p`;
  the tip is also renormalizable; the root is renormalizable iff the component is
  primitive.

### 2.2 Set B: `Λ ∩ MandelbrotSet`

**Source status:** not defined as the main object in these sections.

This is the naive “window intersected with `M`” subset:

```text
Λ ∩ M.
```

What the source sections used here **do not** state:
- no theorem in the extracted text says `M° = Λ ∩ M`;
- no theorem in the extracted text identifies `Λ ∩ M` as canonically homeomorphic
  to `M`;
- no theorem in the extracted text says `Λ ∩ M` is the connectedness locus of the
  quadratic-like family over `Λ`.

What is indirectly plausible but must not be asserted without proof:
- because every parameter in `Λ` is period-`p` renormalizable (Prop. 7.42), one may
  be tempted to identify `Λ ∩ M` with the renormalization locus. But that is not the
  theorem actually stated in Chapter 10 §43, and the root/tip completion issue shows
  the distinction matters.

### 2.3 Set C: the connectedness / renormalization locus `M(g)` or `M°`

There are two closely related source objects.

#### 2.3.1 General connectedness locus `M(g)`

**Source:** Chapter 10 §42.1–42.3

For a quadratic-like family `g` over parameter domain `Λ`, Lyubich defines:

```text
M(g) = { λ ∈ Λ : J(g_λ) is connected }.
```

Short quote:
- “The Mandelbrot set of the quadratic-like family is defined as `M(g) = {λ ∈ Λ : J(g_λ) is connected}`.”

Under Theorem 10.1 assumptions, `χ : Λ → D_{r^2}` is a homeomorphism sending
`M(g)` onto `M`, and Corollary 10.3 says `M(g)` is connected and full.

#### 2.3.2 Concrete complex-window renormalization locus `M°`

**Source:** Chapter 10 §43, Theorem 10.15

For the quadratic family over the complex renormalization window `Λ`, Lyubich defines:

```text
M° = { c ∈ Λ : f_c is renormalizable with combinatorics c° } ∪ {root, tip}.
```

Short quote:
- “`M◦ = {c ∈ Λ : f_c is renormalizable with combinatorics c◦ } ∪ {root, tip}`.”

Then:
- **Theorem 10.15:** “The set `M◦` is canonically homeomorphic to the Mandelbrot set `M`.”

### 2.4 Exact inclusions/equalities we can honestly state

From the pinned text:

1. `M(g) ⊆ Λ` by definition.
2. `M° ⊆ Λ ∪ {root, tip}`, and since root/tip lie on `∂Λ`, `M°` is a completed
   renormalization locus attached to `Λ`.
3. Theorem 10.1 gives `χ(M(g)) = M` for proper unfolded equipped families.
4. Theorem 10.15 gives a canonical homeomorphism `M° ≃ M`.
5. In the primitive case, root-completion can be fixed; in the satellite case, the
   root is **not** renormalizable with period `p`, so raw family-locus and completed
   copy differ.

What I **cannot** claim from the pinned text:
- `M° = Λ ∩ M`;
- `M° = M(g)`;
- `M(g) = Λ ∩ M` for the window family;
- `Λ` itself is canonically homeomorphic to `M`.

### 2.5 Why Theorem 10.15 yields connectedness

Theorem 10.15 says **`M°`** is canonically homeomorphic to the Mandelbrot set `M`.
Since `M` is connected/full in the classical theory, connectedness/fullness of `M°`
follow by transport through homeomorphism.

Crucially, this connectedness belongs to the **completed renormalization locus**
`M°`, not merely to the ambient open window `Λ`.

## 3. Normalized Theorem 10.1 / 10.15 inputs

## 3.1 Theorem 10.1 input package

**Source:** Chapter 10 §42.1–42.3, especially Theorem 10.1 and surrounding setup.

The theorem requires a **proper unfolded equipped quadratic-like family** `g` over
parameter domain `Λ`.

### (a) Parameter domain `Λ`
A planar parameter domain carrying the family.

### (b) Quadratic-like family `g_λ : U_λ → U'_λ`
For each `λ ∈ Λ`, a quadratic-like map between Jordan disks/tubes.

### (c) Properness
The family is proper in the sense that the critical value hits the outer boundary on
`∂Λ`; Lyubich explicitly verifies this for the restricted quadratic family.

### (d) Unfolded / winding-one condition
The critical value winds once around `0` as the parameter traverses `∂Λ`.
The text phrases this as “winding number … equal to 1”.

### (e) Equipment: holomorphic motion of the fundamental annulus
A holomorphic motion `h_λ : A° → A_λ`, equivariant on the boundary, plus
Assumption H that motions of compact subsets extend over a slightly larger disk.
This yields natural tubing via formula `(42.1)`.

### (f) Tubing and connectedness locus
With that tubing, define the straightening map `χ`, and define
`M(g) = { λ ∈ Λ | J(g_λ) is connected }`.

### (g) Theorem 10.1 conclusion
The straightening `χ` is a homeomorphism `Λ → D_{r^2}` mapping `M(g)` onto `M`.

### (h) Corollary 10.3 conclusion
`M(g)` is connected and full.

## 3.2 How Chapter 7 §45.2.1 supplies a concrete family shape

For a primitive superattracting center `c°` of period `p > 1`:
- Proposition 7.41 supplies holomorphic motion of the canonical almost
  renormalization boundary configuration over the complex window `W° = Λ`;
- Proposition 7.42 supplies period-`p` renormalizability throughout `Λ`, plus the
  root/tip distinction.

This is the geometric precursor to the Chapter 10 family over a window.

## 3.3 Where root/tip completion enters Theorem 10.15

Theorem 10.15 does **not** simply apply Theorem 10.1 to the raw family over `Λ`.
The text explicitly says why:
- the quadratic-like family `g_c` over `Λ` “is not full”;
- it “misses the root and the tip of `M°`”;
- the tip can be fixed;
- in the primitive case the root can also be fixed;
- in the satellite case it cannot, because the root is not period-`p` renormalizable.

So the source-prescribed object for little copies is the **completed locus** `M°`,
not the raw family locus alone.

## 4. Repository foundation inventory

## 4.1 Existing repository support

### `Mlc/RenormalizationTypes.lean`
This file already contains:
- `BMol`-based renormalization packaging;
- `parameterToBMol`;
- `RenormalizationTower`-facing placeholder interfaces;
- primitive/satellite predicates.

But this is **not** yet a theorem-faithful `QuadraticLikeFamilyData` over a parameter
window. It packages a single quadratic-like map attached to one parameter, not a
holomorphic family over `Λ` with tubing and straightening.

### `Mlc/LcAtOfShrink.lean`
This is the real downstream consumer. It wants:
- a set family `piece n : Set ℂ`;
- basepoint membership;
- open/relative-neighborhood behavior;
- connectedness on `M`;
- antitone nesting;
- intersection/shrink to `{c}`.

A single little-copy continuum `M°` does not yet satisfy this consumer.

### Files on the current frozen para-puzzle route
- `Mlc/Quadratic/Complex/ParaPuzzle.lean`
- `Mlc/ParaPuzzleConnectivity.lean`
- `Mlc/Quadratic/Complex/PuzzleLemmas2.lean`
- `Mlc/Quadratic/Complex/PuzzleBoundaryMotion.lean`
- `Mlc/ParaPuzzleContainment.lean`

These are mostly built around the wrong frozen object or transport-style packaging.
They are not direct foundations for Theorem 10.1 / 10.15.

## 4.2 Existing Mathlib support

Likely reusable:
- `Homeomorph`, `IsConnected`, `IsCompact`, `closure`, `IsOpen`, `ConnectedSpace`;
- topology of images/preimages/homeomorphisms;
- generic lemmas transporting connectedness/fullness under homeomorphism.

## 4.3 Missing foundation in repo

Not currently formalized in a theorem-faithful way:
- a **quadratic-like family over parameter domain**;
- holomorphic motion / equipped family data over `Λ`;
- tubing as explicit structure data;
- connectedness locus `M(g)`;
- straightening map of a family;
- root/tip completed renormalization copy `M°`;
- theorem shape corresponding to Theorem 10.15.

## 4.4 Open mathematics vs missing formal foundations

For the restricted primitive-window copy, the mathematics is **classical and sourced**.
The blocker is not open math; it is missing formal foundations.

For using nested copies to prove local connectivity in the full MLC program,
serious mathematics remains beyond this task. But Task 10 itself is not blocked by
open-source mathematics.

## 5. Lean-facing definitions and dependency labels

Below are **proposed signatures only**. I follow the task instruction to use
`def`/`structure`, not bare `constant`s.

## 5.1 Quadratic-like family data

```lean
structure QuadraticLikeFamilyData where
  Λ : Set ℂ
  U : Set (ℂ × ℂ)
  U' : Set (ℂ × ℂ)
  g : ℂ → ℂ → ℂ
  base : ℂ
  -- fiber conditions
  fiberU  : ℂ → Set ℂ := fun λ => {z | (λ, z) ∈ U}
  fiberU' : ℂ → Set ℂ := fun λ => {z | (λ, z) ∈ U'}
  mapsTo  : ∀ {λ}, λ ∈ Λ → MapsTo (g λ) (fiberU λ) (fiberU' λ)
  -- placeholder fields for Jordan-disk / quadratic-like conditions
  quadraticLike : Prop
  proper : Prop
  unfolded : Prop
```

Dependency labels:
- structure shell: **genuinely missing definition**.
- `Set (ℂ × ℂ)` / fiber API: **existing Mathlib**.
- real meaning of `quadraticLike`, `proper`, `unfolded`: **sourced classical theorem / definition to formalize**.

## 5.2 Equipped family data

```lean
structure EquippedQuadraticLikeFamilyData extends QuadraticLikeFamilyData where
  annulusBase : Set ℂ
  motion : Prop
  motion_extension : Prop
  tubing : ℂ → Set ℂ → ℂ
```
```

Better split:

```lean
structure HolomorphicMotionData where
  support : Set ℂ
  move : ℂ → ℂ → ℂ
  properties : Prop

structure EquippedQuadraticLikeFamilyData extends QuadraticLikeFamilyData where
  annulusBase : Set ℂ
  motion : HolomorphicMotionData
  equivariant : Prop
  assumptionH : Prop
  tubingData : Prop
```

Dependency labels:
- shell structures: **genuinely missing definition**.
- detailed holomorphic-motion facts: partly **missing foundation**, partly already
  gestured at elsewhere in repo, but not in the required family-over-`Λ` form.

## 5.3 Connectedness locus

```lean
def connectednessLocus (F : QuadraticLikeFamilyData) : Set ℂ :=
  {λ | λ ∈ F.Λ ∧ IsConnected (filledJuliaSetOfFamilyMap F λ)}
```

More faithful to source wording:

```lean
def connectednessLocus (F : QuadraticLikeFamilyData) : Set ℂ :=
  {λ | λ ∈ F.Λ ∧ JuliaSetConnected (F.familyMap λ)}
```

Dependency labels:
- definition shell: **genuinely missing definition**.
- `JuliaSetConnected` / family filled Julia set predicate: **missing foundation**.
- once that predicate exists, set construction is **existing Mathlib**.

## 5.4 Concrete primitive-window family constructor

```lean
structure PrimitiveWindowData where
  center : ℂ
  period : ℕ
  isSuperattracting : Prop
  isPrimitive : Prop


def primitiveWindowFamily (W : PrimitiveWindowData) :
    EquippedQuadraticLikeFamilyData :=
  -- constructor built from Lyubich §45.2.1 / §43 data
  sorry
```

For this task I only specify the target; no implementation.

Dependency labels:
- `PrimitiveWindowData`: **genuinely missing definition**.
- `primitiveWindowFamily`: **sourced theorem to formalize**, with **missing foundation**
  because the repo lacks parameter-window and ql-family infrastructure.

## 5.5 Source-prescribed root/tip completion

```lean
structure PrimitiveRenormalizationLocus where
  window : PrimitiveWindowData
  carrier : Set ℂ
  source_def :
    carrier =
      {c | c ∈ primitiveWindowCarrier window ∧
        RenormalizableWithCombinatorics c window.center} ∪
      {primitiveRoot window, primitiveTip window}
```

or definition-first:

```lean
def primitiveRenormalizationLocusCarrier (W : PrimitiveWindowData) : Set ℂ :=
  {c | c ∈ primitiveWindowCarrier W ∧
      RenormalizableWithCombinatorics c W.center} ∪
  {primitiveRoot W, primitiveTip W}
```

Dependency labels:
- shell: **genuinely missing definition**.
- `RenormalizableWithCombinatorics`: **sourced classical theorem / definition to formalize**.
- root/tip selectors and window carrier: **missing foundation**.

## 5.6 Straightening map and homeomorphism theorem

```lean
def straighteningMap
    (F : EquippedQuadraticLikeFamilyData) :
    connectednessLocus F → MandelbrotSet :=
  fun λ => sorry
```

Better theorem-facing pair:

```lean
def straighteningMap (F : EquippedQuadraticLikeFamilyData) : ℂ → ℂ

theorem straightening_homeomorph_window
    (F : EquippedQuadraticLikeFamilyData)
    (hF : ProperUnfoldedEquipped F) :
    Homeomorph F.Λ (parameterSubpotentialDisk F)

theorem straightening_homeomorph_connectedness_locus
    (F : EquippedQuadraticLikeFamilyData)
    (hF : ProperUnfoldedEquipped F) :
    Homeomorph (connectednessLocus F) MLC.Quadratic.MandelbrotSet
```

and the concrete little-copy theorem:

```lean
theorem primitive_renormalization_locus_homeomorph_mandelbrot
    (W : PrimitiveWindowData) :
    Homeomorph (primitiveRenormalizationLocusCarrier W)
      MLC.Quadratic.MandelbrotSet
```

Dependency labels:
- homeomorphism target type: **existing Mathlib**.
- `straighteningMap` definition: **missing foundation**.
- Theorem 10.1 / 10.15 formal statements: **sourced classical theorem to formalize**.

## 5.7 Connectedness/fullness corollaries derived, not stored

```lean
theorem connectednessLocus_isConnected_of_homeomorph_mandelbrot
    {S : Set ℂ}
    (h : Homeomorph S MLC.Quadratic.MandelbrotSet) :
    IsConnected S

theorem connectednessLocus_isFull_of_homeomorph_mandelbrot
    {S : Set ℂ}
    (h : Homeomorph S MLC.Quadratic.MandelbrotSet) :
    IsFull S
```

These should be generic topology lemmas, not structure fields.

Dependency labels:
- connectedness transport: **existing Mathlib support** or easy generic lemma.
- fullness transport: likely **small missing project lemma** about homeomorphisms of
  planar continua / complements, but not deep dynamics.

## 6. Downstream usefulness analysis

## 6.1 Does the locus contain the chosen base parameter?

Yes, for a primitive superattracting center `c°`, the little copy `M°` is designed
around that combinatorics and contains the center/base parameter.

## 6.2 Is it a relative neighborhood of the base in `M`?

**Not in the sense needed by `LcAtOfShrink`.**

`M°` is a compact little Mandelbrot copy inside parameter space. It is connected
and canonically homeomorphic to `M`, but it is not automatically an **open relative
neighborhood** of `c°` inside `M`. In fact, as a little copy, it behaves more like a
compact embedded continuum than a local open neighborhood basis element.

So one fixed `M°` is **not** the right direct input to `LcAtOfShrink`.

## 6.3 Can varying depth/combinatorics give an antitone family?

Potentially yes, but only along a **nested little-copy / renormalization-tower**
construction:
- choose successively deeper primitive/satellite renormalization combinatorics;
- obtain nested copies `M°_n` containing the target parameter;
- then seek a theorem that intersection shrinks to `{c}`.

This is qualitatively the infinitely-renormalizable route, not a single-window
validation route.

## 6.4 What theorem would show intersection shrinks to `{c}`?

Something of the form:

```lean
theorem iInter_primitiveRenormalizationLocus_eq_singleton
```

for a canonical nested sequence of loci determined by the combinatorics of `c`.

But that is **not** provided by Theorem 10.15. Theorem 10.15 only gives one copy’s
homeomorphism to `M`.

## 6.5 Which classes can use this family?

- **Finite hyperbolic / explicit primitive window:** good for validating the family
  and straightening infrastructure.
- **Infinitely renormalizable parameters:** potentially useful via nested little-copy
  route.
- **Arbitrary finitely renormalizable/non-renormalizable parameters:** not directly;
  those are better handled by Yoccoz puzzle shrink arguments rather than one copy.

## 6.6 Honest conclusion for `LcAtOfShrink`

A single renormalization locus `M°` is **insufficient** for `LcAtOfShrink`.
It does not itself give:
- relatively open neighborhoods in `M`;
- an antitone neighborhood basis;
- shrink to `{c}`.

Its honest use is as a **foundational building block** for the nested-copy branch of
infinitely-renormalizable parameters.

## 7. First honest milestone and feasibility

## 7.1 Best first milestone

The most honest first Lean milestone is **not** Theorem 10.15 itself.
It is a generic topology lemma that will later consume the source theorem without
packaging it as an axiom bundle.

Proposed theorem:

```lean
theorem isConnected_of_homeomorph_mandelbrot
    {S : Set ℂ}
    (hS : Nonempty S)
    (h : S ≃ₜ MLC.Quadratic.MandelbrotSet) :
    IsConnected S
```

and possibly its fullness companion.

Why this is honest:
- it adds actual reusable foundations;
- it does not assume straightening or connectivity via a bespoke structure field;
- it will be the downstream consumer once `primitive_renormalization_locus_homeomorph_mandelbrot`
  is formalized.

## 7.2 Slightly stronger alternative milestone

If we want one dynamics-facing step, then:

```lean
def connectednessLocus (F : QuadraticLikeFamilyData) : Set ℂ := ...
```

plus a purely definitional membership lemma:

```lean
theorem mem_connectednessLocus_iff
```

This is also honest, but needs more new definitions.

## 7.3 Feasibility

- generic topology transport lemma: **high**;
- `connectednessLocus` data shell: **medium**;
- full primitive-window family constructor: **low-medium** now;
- Theorem 10.15 formalization: **low** without substantial new family foundations.

## 7.4 First missing foundation after the milestone

After the generic topology lemma, the first real missing foundation is:

**a theorem-faithful `QuadraticLikeFamilyData` / equipped-family infrastructure**
for parameter families over `Λ`, including a connectedness-locus definition.

That is the correct next foundation layer.

## 8. Final decision and next task

**Final decision:** **(2) architecture ready but quadratic-like family foundations missing.**

The source picture is now clear:
- the right connected object is the renormalization locus `M°` / `M(g)` inside a
  window, not the ambient window itself;
- Theorem 10.15 gives a genuine little Mandelbrot copy;
- but one copy is not yet a neighborhood basis for `LcAtOfShrink`.

### Exact next worker task

Audit existing `BMol` / renormalization structures and draft a non-axiomatic
`QuadraticLikeFamilyData` + `connectednessLocus` foundation layer, together with
one generic topology lemma transporting connectedness from a homeomorphism to
`MandelbrotSet`, without attempting Theorem 10.15 yet.

## 9. Exact commands / search limitations

Commands used:

```bash
cd /home/kir/pers/mlc && git --no-pager status --short

cd /home/kir/pers/mlc && rg -n 'QuadraticLike|quadratic-like|straightening|renormalization locus|connectednessLocus|M\(g\)|PrimitiveRenormalization' Mlc/**/*.lean

cd /home/kir/pers/mlc && pdftotext 'refs/Conformal Geometry and Dynamics of Quadratic Polynomials.pdf' - | \
  grep -n 'Theorem 10\.1\|Corollary 10\.3\|Theorem 10\.15\|M(g)\|connectedness locus\|straightening' | head -n 120

cd /home/kir/pers/mlc && pdftotext 'refs/Conformal Geometry and Dynamics of Quadratic Polynomials.pdf' - | sed -n '10580,10740p'

cd /home/kir/pers/mlc && pdftotext 'refs/Conformal Geometry and Dynamics of Quadratic Polynomials.pdf' - | sed -n '11670,11740p'

cd /home/kir/pers/mlc && pdftotext 'refs/Conformal Geometry and Dynamics of Quadratic Polynomials.pdf' - | sed -n '11720,11920p'

cd /home/kir/pers/mlc && pdftotext 'refs/Conformal Geometry and Dynamics of Quadratic Polynomials.pdf' - | sed -n '12130,12210p'
```

Files read:
- `plan/GPT54_TASK_10_RENORMALIZATION_LOCUS_SPECIFICATION.md`
- `plan/GPT54_RESULT_09_SPECIFY_CANONICAL_PARAMETER_PIECE.md`
- `Mlc/RenormalizationTypes.lean`
- `Mlc/LcAtOfShrink.lean`

Search limitations / honesty notes:
- I relied on the local Lyubich survey text requested by the task.
- I did not extract additional primary-source pages from DH/Orsay references in this task.
- I did not attempt theorem proving or Lean edits.
- I did not resolve whether a later source proves `M° = M(g)` for the primitive
  completed family; I therefore did not assert that equality.

## 10. Complete `git status --short` and no-edit/no-commit confirmation

```text
?? plan/GPT54_RESULT_09_SPECIFY_CANONICAL_PARAMETER_PIECE.md
?? plan/GPT54_REVIEW_09_SPECIFY_CANONICAL_PARAMETER_PIECE.md
?? plan/GPT54_TASK_10_RENORMALIZATION_LOCUS_SPECIFICATION.md
```

Safety / integrity confirmation:
- I wrote only this result artifact.
- I did not edit Lean sources, docs, prior result files, or plan files.
- I did not update `plan.md` because this task explicitly allowed only the result report.
- I did not commit.
- No `axiom`, `sorry`, or `admit` were introduced.