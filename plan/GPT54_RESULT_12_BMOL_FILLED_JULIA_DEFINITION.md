# GPT-5.4 Result 12: BMol filled Julia definition

## 1. Executive decision

**Decision:** **(3) the intrinsic definition works, but normalized-quadratic compatibility needs a separate strengthening first.**

The honest next foundation is an intrinsic BMol non-escaping / filled Julia set
built from the actual `QuadraticLikeMap` data `(g.U, g.f)`, not from
`MLC.Quadratic.K (criticalValue g)`.

A minimal declaration package for

- `Molecule.filledJuliaSet : BMol → Set ℂ`,
- `Molecule.FilledJuliaConnected : BMol → Prop`,
- `Molecule.BMolParameterFamily`, and
- `BMolParameterFamily.connectednessLocus`

**temp-compiles successfully** under `lake env lean`.

However, current compatibility with the normalized quadratic family is only
partial:

- for `parameterToBMol c`, the current spec exposes `g.f = (fun z => z^2 + c)` and
  `criticalValue g = c`;
- it does **not** expose `g.U = Set.univ` or `g.V = Set.univ` for the chosen witness;
- therefore equality of the intrinsic BMol filled Julia set with `MLC.Quadratic.K c`
  is **not currently provable from the published spec**.

So the definition itself is ready, but normalized compatibility needs one small
specification-strengthening task first.

## 2. Mathematical definition

### 2.1 Source convention

The local source already present in `refs/2512.24171v1.txt` states:

> `Kf := {z ∈ U : f^n(z) ∈ U ∀ n ≥ 1}`

(§3.1, quadratic-like maps).

The local Dudko reference `refs/Dudko_2309.02107.txt` states equivalently:

> `K(f) := {z : f^n z ∈ X, n = 0, 1, 2, ...}`

(§2.2. Quadratic-like maps).

These are the same convention, because the `n = 0` clause is exactly `z ∈ U` / `z ∈ X`.

### 2.2 Recommended intrinsic Lean definition

The cleanest intrinsic definition for current `BMol := QuadraticLikeMap` is:

```lean
def filledJuliaSet (g : BMol) : Set ℂ :=
  {z : ℂ | ∀ n : ℕ, (g.f^[n]) z ∈ g.U}
```

This uses the globally represented function `g.f : ℂ → ℂ`, but membership is
forced at every iterate into the intended domain `g.U`. That is the correct way
to express the restricted-map dynamics using the current representation.

### 2.3 Comparison of the candidate forms

Task 12 asked to compare:

```text
A := {z | ∀ n, (g.f^[n]) z ∈ g.U}
B := {z ∈ g.U | ∀ n, (g.f^[n]) z ∈ g.U}
C := ⋂ n, (g.f^[n]) ⁻¹' g.U
```

#### A vs C

These are definitionally/propositionally equivalent by set extensionality and `simp`:

```lean
lemma filledJuliaSet_eq_iInter_preimage (g : BMol) :
    filledJuliaSet g = ⋂ n : ℕ, (g.f^[n]) ⁻¹' g.U
```

This compiled in the temporary Lean test.

#### A vs B

As written, `B` is redundant rather than different **only if** the second conjunct
is interpreted with positive times, i.e.

```text
{z ∈ g.U | ∀ n, (g.f^[n+1]) z ∈ g.U}
```

because `A` already includes `n = 0`, and `(g.f^[0]) z = z`.

By contrast, the literal form

```text
{z ∈ g.U | ∀ n, (g.f^[n]) z ∈ g.U}
```

is stronger-looking but actually just duplicates the `n = 0` clause. It is fine
mathematically, but not a useful separate membership lemma.

My first temporary proof attempt of a direct `A = {z ∈ U ∧ ∀ n, f^[n] z ∈ U}`
failed exactly because the right side duplicated the `n = 0` clause without
rewriting it into a positive-time form. This was a useful check that the clean
canonical declaration is the `∀ n` form above.

### 2.4 Global `f` vs restricted `U → V`

`QuadraticLikeMap` currently stores

```lean
f : ℂ → ℂ
maps_to : MapsTo f U V
```

rather than a bundled restricted map. This does **not** block the definition.
The filled Julia set only needs a predicate saying that every forward iterate stays
inside `U`; using the global iterate is honest because every accepted orbit point is
explicitly re-certified as lying in `U` at each time.

This representation issue matters later for theorem statements about restricted
iterates, invariance, or conjugacy, but not for the bare definition.

## 3. Existing API and naming audit

### 3.1 Existing quadratic-family dynamical set API

`Yoccoz/Quadratic/Complex/Basic.lean` contains:

```lean
def boundedOrbit (c z : ℂ) : Prop :=
  ∃ M : ℝ, ∀ n, ‖orbit c z n‖ ≤ M

def K (c : ℂ) : Set ℂ := { z | boundedOrbit c z }
def J (c : ℂ) : Set ℂ := frontier (K c)
def MandelbrotSet : Set ℂ := { c | boundedOrbit c 0 }
```

This is the existing normalized quadratic filled Julia infrastructure, but it is
**not** intrinsic to `BMol`.

### 3.2 Existing BMol API

`Molecule/BMol.lean` defines:

- `structure QuadraticLikeMap`
- `criticalPoint : QuadraticLikeMap → ℂ`
- `criticalValue : QuadraticLikeMap → ℂ`
- `def BMol := QuadraticLikeMap`

There is **no** existing `filledJuliaSet`, `FilledJulia`, or `nonEscapingSet` for `BMol`
in the repository or vendored dependencies found in this audit.

### 3.3 Iterate usage / imports

The project already uses the iterate notation `f^[n]` in multiple places, e.g.

- `Mlc/SatelliteRenormalizationTower.lean`
- `Mlc/RenormalizationTypes.lean`

The temp file compiled with:

```lean
import Mlc.RenormalizationTypes
import Mathlib.Topology.Connected.Basic
open Function
```

So no extra exotic import appears necessary beyond files already pulling in the
core function-iterate machinery transitively.

### 3.4 Compact containment issue

`QuadraticLikeMap` stores only:

```lean
closure_subset : closure U ⊆ V
```

not a bundled theorem that `closure U` is compact in `V` or a literal notation `U ⋐ V`.

This **does not affect the definition** of the intrinsic filled Julia set. The
non-escaping set only depends on `(U, f)` and iteration. It **will** affect later
mathematical theorems where genuine polynomial-like/quadratic-like compact
containment is required.

So this is a theorem-level and architecture-level warning, not a definition-level blocker.

## 4. Compile-oriented proposal

### 4.1 Proposed declarations

```lean
import Mlc.RenormalizationTypes
import Mathlib.Topology.Connected.Basic

open Set
open Complex
open Function

namespace Molecule

/-- Intrinsic non-escaping / filled Julia set of a quadratic-like map. -/
def filledJuliaSet (g : BMol) : Set ℂ :=
  {z : ℂ | ∀ n : ℕ, (g.f^[n]) z ∈ g.U}

lemma mem_filledJuliaSet_iff (g : BMol) (z : ℂ) :
    z ∈ filledJuliaSet g ↔ ∀ n : ℕ, (g.f^[n]) z ∈ g.U := Iff.rfl

lemma filledJuliaSet_eq_iInter_preimage (g : BMol) :
    filledJuliaSet g = ⋂ n : ℕ, (g.f^[n]) ⁻¹' g.U := by
  ext z
  simp [filledJuliaSet]

/-- Intrinsic connected-fiber predicate for a quadratic-like map. -/
def FilledJuliaConnected (g : BMol) : Prop :=
  IsConnected (filledJuliaSet g)

/-- Minimal BMol-valued parameter family. -/
structure BMolParameterFamily (α : Type*) where
  parameterSet : Set α
  map : α → BMol

/-- Parameters whose intrinsic BMol filled Julia sets are connected. -/
def BMolParameterFamily.connectednessLocus {α : Type*} (F : BMolParameterFamily α) : Set α :=
  {a : α | a ∈ F.parameterSet ∧ FilledJuliaConnected (F.map a)}

lemma mem_connectednessLocus_iff {α : Type*} (F : BMolParameterFamily α) (a : α) :
    a ∈ F.connectednessLocus ↔ a ∈ F.parameterSet ∧ FilledJuliaConnected (F.map a) := Iff.rfl

end Molecule
```

### 4.2 Temporary compilation result

I tested the above declarations in `/tmp/task12_bmol_filled_julia.lean` using:

```bash
cd /home/kir/pers/mlc && lake env lean /tmp/task12_bmol_filled_julia.lean
```

Result: **success** (exit code 0).

I also tested an intermediate variant trying to package a redundant “`z ∈ U ∧ ∀ n, ...`”
lemma naively; Lean rejected that proof, which helped isolate the cleaner final API.
The temp file was deleted afterward.

## 5. Normalized quadratic compatibility

### 5.1 What current `parameterToBMol_spec` gives

`Mlc/RenormalizationTypes.lean` currently proves:

```lean
theorem parameterToBMol_spec (c : ℂ) :
    ∃ g : BMol, g.f = (fun z : ℂ => z^2 + c) ∧ criticalValue g = c
```

The implementation witness is visibly built with `U = Set.univ` and `V = Set.univ`,
but these equalities are **not exported in the theorem statement**.

### 5.2 What would be needed to identify `filledJuliaSet (parameterToBMol c)` with `K c`

The intrinsic BMol set is

```lean
{z | ∀ n, ((parameterToBMol c).f^[n]) z ∈ (parameterToBMol c).U}
```

To compare it honestly with `MLC.Quadratic.K c = {z | boundedOrbit c z}`, one would
need at minimum the parameter witness to expose:

- `g.f = fun z => z^2 + c`
- `g.U = Set.univ`
- ideally also `g.V = Set.univ`

But if `U = univ`, the intrinsic BMol filled Julia set becomes `Set.univ`, since every
iterate lands in `univ`. That is **not** `K c` in general.

So the honest conclusion is stronger than “current spec is too weak”:

1. **From the current exported spec, equality is not provable** because domain data are hidden.
2. **Even if the hidden domains were exposed as `U = univ`, equality would be false**, since the
   current `parameterToBMol` is a coarse global packaging, not a polynomial-like restriction whose
   intrinsic non-escaping set recovers bounded orbits.

Therefore Task 12 must not claim any present compatibility theorem.

### 5.3 Exact missing strengthening / architectural note

There are really two distinct future needs:

#### (a) Specification strengthening for the current constructor

If later code needs direct access to the chosen witness shape, the immediate theorem should be:

```lean
theorem parameterToBMol_spec_full (c : ℂ) :
  ∃ g : BMol,
    g.U = Set.univ ∧
    g.V = Set.univ ∧
    g.f = (fun z : ℂ => z^2 + c) ∧
    criticalValue g = c
```

This would expose the actual present implementation.

#### (b) Separate honest normalized-quadratic compatibility object

To recover `MLC.Quadratic.K c`, one needs a **different BMol-style constructor or family** whose
chosen domain `U` encodes a genuine polynomial-like restriction / escape control region, not `univ`.
Only for such a constructor could one aim for a proposition like:

```lean
theorem parameterToBMolFilledJulia_eq_K (c : ℂ) :
  Molecule.filledJuliaSet (parameterToBMolRestricted c) = MLC.Quadratic.K c
```

That is a later architecture task, not something available from the current `parameterToBMol`.

## 6. Scope boundary

This Task 12 milestone is only the intrinsic-definition layer. It does **not** prove any of:

- connectedness iff the critical point does not escape;
- hybrid-conjugacy invariance or straightening compatibility;
- connectedness/fullness of a parameter locus;
- holomorphic dependence of BMol families.

Those are later theorem tasks. The current result is just that the honest intrinsic objects can be
introduced now, without axioms and without misidentifying them with normalized quadratic objects.

## 7. Exact next worker task

Next worker task:

> Implement the intrinsic `Molecule.filledJuliaSet`, `FilledJuliaConnected`,
> `BMolParameterFamily`, and `connectednessLocus` declarations in Lean, and separately replace or
> supplement `parameterToBMol` with an honestly specified restricted quadratic-family constructor so
> that any future compatibility theorem with `MLC.Quadratic.K c` is mathematically meaningful.

## 8. Commands run

```bash
cd /home/kir/pers/mlc && sed -n '1,220p' /tmp/copilot-tool-output-1783793601859-937f3680.txt
cd /home/kir/pers/mlc && sed -n '440,470p' refs/2512.24171v1.txt
cd /home/kir/pers/mlc && sed -n '388,405p' refs/Dudko_2309.02107.txt
cd /home/kir/pers/mlc && git --no-pager status --short
cd /home/kir/pers/mlc && lake env lean /tmp/task12_bmol_filled_julia.lean
```

Temporary compile attempts:

- first attempt failed on an over-strong/redundant separator lemma;
- final minimal declaration package compiled successfully.

## 9. Git status and write confirmation

`git status --short` at audit time:

```text
?? plan/GPT54_PROMPT_11_QUADRATIC_LIKE_FAMILY_FOUNDATION_AUDIT.md
?? plan/GPT54_PROMPT_12_BMOL_FILLED_JULIA_DEFINITION.md
?? plan/GPT54_RESULT_09_SPECIFY_CANONICAL_PARAMETER_PIECE.md
?? plan/GPT54_RESULT_10_RENORMALIZATION_LOCUS_SPECIFICATION.md
?? plan/GPT54_RESULT_11_QUADRATIC_LIKE_FAMILY_FOUNDATION_AUDIT.md
?? plan/GPT54_REVIEW_09_SPECIFY_CANONICAL_PARAMETER_PIECE.md
?? plan/GPT54_REVIEW_10_RENORMALIZATION_LOCUS_SPECIFICATION.md
?? plan/GPT54_REVIEW_11_QUADRATIC_LIKE_FAMILY_FOUNDATION_AUDIT.md
?? plan/GPT54_TASK_10_RENORMALIZATION_LOCUS_SPECIFICATION.md
?? plan/GPT54_TASK_11_QUADRATIC_LIKE_FAMILY_FOUNDATION_AUDIT.md
?? plan/GPT54_TASK_12_BMOL_FILLED_JULIA_DEFINITION.md
```

During this task I wrote only this result artifact and removed the temporary `/tmp`
Lean file after compilation. I did **not** edit Lean source files, plans, docs, or
vendored dependencies, and I did **not** make a commit.
