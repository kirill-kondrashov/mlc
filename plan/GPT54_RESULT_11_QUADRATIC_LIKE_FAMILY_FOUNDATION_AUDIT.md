# GPT-5.4 Result 11: Quadratic-like family foundation audit

## 1. Executive decision

**Decision:** **(1) signatures are ready for a small Lean implementation task.**

After auditing the current repository plus the vendored `molecule-conjecture` and
`yoccoz-theorem` dependencies, the smallest honest non-axiomatic milestone is now
clear:

- reuse **`Molecule.BMol`** as the fiber type;
- define a minimal parameter-family shell whose fibers are `BMol` objects over a
  chosen parameter domain;
- define the connectedness locus using the already non-axiomatic fiber predicate
  `IsConnected (MLC.Quadratic.K (criticalValue (F.toBMol p)))`;
- prove the membership lemma by `Iff.rfl` / set-theoretic simplification.

This stays below straightening, holomorphic motion, and Theorem 10.15, introduces
no axioms, and does not rely on `mandelbrot_set_connected`.

The audit also shows an important correction to Result 10’s tentative foundation
story:

- the repository **already has** a non-axiomatic theorem that the filled Julia set
  `K c` is connected for `c ∈ MandelbrotSet`;
- but there is **not yet** a general BMol-level filled-Julia set object or a
  BMol-level connected-fiber predicate intrinsic to arbitrary quadratic-like maps.

So the most faithful first family milestone is a **parameter family of `BMol`
objects whose connected-fiber predicate is defined via their critical value and the
existing quadratic-family filled Julia set**. It is mathematically narrower than a
fully intrinsic quadratic-like family theory, but honest, compilable, and axiom-free.

## 2. Existing-type audit

I audited the exact declarations relevant to a first parameter-family API.

### 2.1 Quadratic dynamical sets in the Yoccoz dependency

#### `Yoccoz/Quadratic/Complex/Basic.lean:33-43`

```lean
def boundedOrbit (c z : ℂ) : Prop :=
  ∃ M : ℝ, ∀ n, ‖orbit c z n‖ ≤ M

def K (c : ℂ) : Set ℂ := { z | boundedOrbit c z }

def J (c : ℂ) : Set ℂ := frontier (K c)

def MandelbrotSet : Set ℂ := { c | boundedOrbit c 0 }
```

Status:
- **definitional**;
- lives in namespace `MLC.Quadratic` via the imported Yoccoz package;
- non-axiomatic;
- fully reusable.

Reuse judgment:
- `K` and `MandelbrotSet` are the only existing non-axiomatic connected-fiber-facing
  objects in the repository.
- They are parameterized by a quadratic-family parameter `c : ℂ`, not by an
  arbitrary `BMol` map.

### 2.2 Filled Julia connectedness theorem already proved in-repo

#### `Mlc/FilledJuliaConnected.lean:277-381`

Key theorem endpoints:

```lean
theorem filled_julia_set_connected_proved {c : ℂ} (hc : c ∈ MandelbrotSet) :
    IsConnected (K c)

theorem filled_julia_set_connected {c : ℂ} (hc : c ∈ MandelbrotSet) :
    IsConnected (K c)
```

Status:
- **theorem-backed and non-axiomatic** in the current repo;
- the proof is explicit and does not use `axiom`, `sorry`, or `admit` in this file;
- reusable.

Reuse judgment:
- this is enough to support a first non-axiomatic connected-fiber theorem for any
  family whose fibers expose a parameter `c` with `criticalValue = c`.
- it is **not** an intrinsic theorem about the filled Julia set of a general `BMol`.

### 2.3 BMol / quadratic-like map in molecule-conjecture dependency

#### `.lake/packages/molecule-conjecture/Molecule/BMol.lean:28-66`

```lean
structure QuadraticLikeMap where
  U : Set ℂ
  V : Set ℂ
  f : ℂ → ℂ
  isOpen_U : IsOpen U
  isOpen_V : IsOpen V
  isConnected_U : IsConnected U
  isConnected_V : IsConnected V
  simplyConnected_U : SimplyConnectedSpace U
  simplyConnected_V : SimplyConnectedSpace V
  subset : U ⊆ V
  closure_subset : closure U ⊆ V
  differentiable_on : DifferentiableOn ℂ f U
  maps_to : MapsTo f U V
  proper : IsProperMap (maps_to.restrict f U V)
  unique_critical_point : ∃! c ∈ U, deriv f c = 0
  simple_critical_point : ∀ c ∈ U, deriv f c = 0 → deriv (deriv f) c ≠ 0

noncomputable def criticalPoint (g : QuadraticLikeMap) : ℂ :=
  Classical.choose g.unique_critical_point

noncomputable def criticalValue (g : QuadraticLikeMap) : ℂ :=
  g.f (criticalPoint g)

def BMol := QuadraticLikeMap
```

Status:
- **definitional**, not axiomatic;
- mathematically meaningful as a single quadratic-like map shell;
- reusable as a fiber type.

Important caveat:
- the same file equips `BMol` with a **discrete topology** (`TopologicalSpace BMol`
  at lines 73-79). That topology is a placeholder and must **not** be treated as the
  honest notion of holomorphic/continuous family dependence.

Reuse judgment:
- `BMol` is reusable as a **fiber type only**.
- Its current topology must not be used for a theorem-faithful parameter-family
  continuity story.

### 2.4 Renormalization relation and fast renormalizability

#### `.lake/packages/molecule-conjecture/Molecule/Rfast.lean:15-43`

```lean
structure RenormalizationRelation (g g' : BMol) where
  p : ℕ
  p_pos : p ≥ 2
  U' : Set ℂ
  V' : Set ℂ
  ψ : ℂ → ℂ
  U'_sub : U' ⊆ g.U
  V'_sub : V' ⊆ g.V
  rescaling_affine : ∃ a b : ℂ, a ≠ 0 ∧ ∀ z, ψ z = a * z + b
  maps_U : MapsTo ψ g'.U U'
  maps_V : MapsTo ψ g'.V V'
  surj_U : ψ '' g'.U = U'
  surj_V : ψ '' g'.V = V'
  eq_f : ∀ z ∈ g'.U, ψ (g'.f z) = (g.f^[p] (ψ z))

def IsFastRenormalizable (g : BMol) : Prop :=
  ∃ g' : BMol, Nonempty (RenormalizationRelation g g')
```

Status:
- **definitional**;
- not axiom-backed in these files;
- reusable for later renormalization consumers.

Reuse judgment:
- useful for later tower/renormalization work;
- not directly needed for the first `connectednessLocus` milestone.

### 2.5 Current repository bridge from parameter to BMol

#### `Mlc/RenormalizationTypes.lean:57-173`

Key declarations:

```lean
theorem parameterToBMol_spec (c : ℂ) :
    ∃ g : BMol, g.f = (fun z : ℂ => z^2 + c) ∧ criticalValue g = c

noncomputable def parameterToBMol (c : ℂ) : BMol :=
  Classical.choose (parameterToBMol_spec c)

lemma parameterToBMol_criticalValue (c : ℂ) :
    criticalValue (parameterToBMol c) = c
```

Status:
- `parameterToBMol_spec`: **theorem-backed**, proof in file;
- `parameterToBMol`: **noncomputable def** built from choice;
- `parameterToBMol_criticalValue`: theorem-backed;
- no local axioms used in the declaration itself.

Reuse judgment:
- currently the strongest in-repo bridge from a complex parameter to a `BMol` fiber;
- mathematically narrow (`U = V = univ` construction), so not theorem-faithful for a
  later Lyubich-style family over a window;
- still reusable for the first non-axiomatic family shell and locus definition.

### 2.6 Existing family-like renormalization structures

#### `Mlc/MoleculeRenormalizationTower.lean:20-33`

```lean
structure RenormalizationTower (g : BMol) where
  gₙ : ℕ → BMol
  g0 : gₙ 0 = g
  step : ∀ n : ℕ, Nonempty (RenormalizationRelation (gₙ n) (gₙ (n + 1)))
```

Status:
- **definitional**;
- reusable as a combinatorial tower shell.

Reuse judgment:
- not a parameter family over a domain;
- not suitable as the first family foundation for Task 11.

### 2.7 Placeholder / conclusion-facing renormalization interfaces

Relevant declarations in `Mlc/RenormalizationTypes.lean`:

```lean
def PrimitiveRenormalizable (c : ℂ) : Prop :=
  ∀ (hc : c ∈ MLC.Quadratic.MandelbrotSet),
    MLC.LocallyConnectedAt MLC.Quadratic.MandelbrotSet ⟨c, hc⟩

def SatelliteRenormalizable (c : ℂ) : Prop :=
  ∀ n : ℕ, IsFastRenormalizable ((Rfast^[n]) (parameterToBMol c))

def IsSatellite {f g : BMol} (rel : RenormalizationRelation f g) : Prop :=
  f.fixed_point ∈ closure rel.U'

def IsPrimitive {f g : BMol} (rel : RenormalizationRelation f g) : Prop :=
  ¬ IsSatellite rel

def PrimitiveRenormalizableData (c : ℂ) : Prop :=
  ∃ T : RenormalizationTower (parameterToBMol c),
    {n | IsPrimitive (T.rel n)}.Infinite
```

Status:
- mixed: definitional, but some are clearly **placeholder or conclusion-facing** rather
  than theorem-faithful source objects.

Reuse judgment:
- `PrimitiveRenormalizable` is not a foundation object; it already asks for local
  connectivity.
- `IsSatellite` / `IsPrimitive` are lightweight placeholders.
- these should **not** be the basis of the first family API.

## 3. Axiom / sorry audit

### 3.1 Connectedness of `MandelbrotSet`

#### `Mlc/Quadratic/Complex/Axioms.lean:23`

```lean
axiom mandelbrot_set_connected : IsConnected MandelbrotSet
```

Status:
- **axiom-dependent**.

Consequence:
- any milestone whose only connectivity theorem is obtained by transporting from
  `MandelbrotSet` using `mandelbrot_set_connected` is **not** a non-axiomatic milestone.
- this confirms the supervisor review of Result 10.

### 3.2 Connectedness of `K c`

The in-repo theorem `filled_julia_set_connected` in `Mlc/FilledJuliaConnected.lean`
is proved directly and is **not** axiomatized.

Consequence:
- a connected-fiber predicate based on `K c` is available non-axiomatically.

### 3.3 Conversion from parameter to BMol

`parameterToBMol` itself is choice-based but not axiom-backed. The supporting
`parameterToBMol_spec` proof is explicit.

Consequence:
- it is acceptable for a first non-axiomatic API milestone.
- however, it does not provide a theorem-faithful parameter-window family with
  honest holomorphic dependence.

### 3.4 Search for `sorry` / `admit`

I searched `Mlc/**/*.lean` and the relevant `molecule-conjecture` dependency slices
for `axiom|sorry|admit`.

Findings relevant to this milestone:
- `mandelbrot_set_connected` is an explicit axiom.
- I found **no** `sorry` / `admit` in the declarations proposed for reuse here:
  `BMol`, `criticalValue`, `RenormalizationRelation`, `IsFastRenormalizable`,
  `parameterToBMol`, `K`, `MandelbrotSet`, `filled_julia_set_connected`.

## 4. Minimal family data

The smallest honest family object should reuse `BMol` directly and avoid fake
property placeholders.

### 4.1 Proposed family shell

```lean
structure BMolParameterFamily where
  α : Type
  paramSet : Set α
  toBMol : α → BMol
```

Why this is the smallest honest shell:
- it records exactly the parameter carrier/type, the chosen parameter domain, and
  the fiber map into an existing quadratic-like object;
- it does **not** pretend to encode holomorphic dependence using the current fake
  discrete topology on `BMol`;
- it is enough to define a connectedness locus.

### 4.2 Intentional deferral

The following are intentionally **deferred** at this milestone:
- continuity of `α → BMol`;
- holomorphic motion / tubing;
- straightening;
- proper unfolded equipped family predicates in the Lyubich sense.

This deferral is necessary because the current `BMol` topology is explicitly a
placeholder and cannot honestly support those notions.

### 4.3 Honest connected-fiber predicate

There is **no intrinsic BMol filled Julia set definition** in the current repo.
So the smallest honest connected-fiber predicate must be defined through the
existing quadratic-family filled Julia set at the fiber’s critical value:

```lean
def BMolFiberConnected (g : BMol) : Prop :=
  IsConnected (MLC.Quadratic.K (criticalValue g))
```

This is mathematically narrower than “the filled Julia set of `g` is connected” for
arbitrary quadratic-like maps, but it is the honest current expansion from existing
objects.

Because `parameterToBMol_criticalValue` proves `criticalValue (parameterToBMol c) = c`,
we also get the concrete bridge

```lean
BMolFiberConnected (parameterToBMol c) ↔ IsConnected (MLC.Quadratic.K c)
```

by simplification.

### 4.4 Why not a more ambitious predicate now?

I do **not** propose a field like

```lean
connectedFiber : BMol → Prop
```

without definition, nor a placeholder `quadraticLike : Prop`, because Task 11
explicitly forbids hiding missing mathematics behind opaque `Prop` fields.

I also do **not** propose `IsConnected (K (criticalValue g))` as an intrinsic theorem
about arbitrary quadratic-like maps: it is only the exact current repository-level
expansion available from existing objects.

## 5. Connectedness-locus milestone

### 5.1 Required imports

The minimal implementation task would likely need:

```lean
import Molecule.BMol
import Mlc.FilledJuliaConnected
```

Possibly also:

```lean
import Mathlib.Topology.Connected.Basic
```

if not already pulled transitively.

### 5.2 Compile-oriented declarations

Proposed declarations:

```lean
namespace MLC
n
open Molecule Set

structure BMolParameterFamily where
  α : Type
  paramSet : Set α
  toBMol : α → BMol


def BMolFiberConnected (g : BMol) : Prop :=
  IsConnected (MLC.Quadratic.K (criticalValue g))


def connectednessLocus (F : BMolParameterFamily) : Set F.α :=
  {a | a ∈ F.paramSet ∧ BMolFiberConnected (F.toBMol a)}

@[simp] theorem mem_connectednessLocus_iff
    (F : BMolParameterFamily) (a : F.α) :
    a ∈ connectednessLocus F ↔
      a ∈ F.paramSet ∧ IsConnected (MLC.Quadratic.K (criticalValue (F.toBMol a))) :=
  Iff.rfl

end MLC
```

Minor correction before implementation: remove the stray `n` after `namespace MLC`.
The intended declarations themselves are collision-safe on current repo search.

### 5.3 Concrete future consumer

A concrete and useful next consumer is the family induced by the current bridge
`parameterToBMol` on a chosen parameter domain `S : Set ℂ`:

```lean
def parameterToBMolFamily (S : Set ℂ) : BMolParameterFamily where
  α := ℂ
  paramSet := S
  toBMol := parameterToBMol
```

Then

```lean
connectednessLocus (parameterToBMolFamily S)
```

is exactly

```lean
{c | c ∈ S ∧ IsConnected (MLC.Quadratic.K c)}
```

after rewriting with `parameterToBMol_criticalValue`.

This gives an immediate non-axiomatic consumer theorem on any `S ⊆ MandelbrotSet`:

```lean
theorem subset_mandelbrot_mem_connectednessLocus
    {S : Set ℂ} {c : ℂ}
    (hcS : c ∈ S) (hcM : c ∈ MLC.Quadratic.MandelbrotSet) :
    c ∈ connectednessLocus (parameterToBMolFamily S)
```

proved using `filled_julia_set_connected hcM`.

This is a real downstream use: it packages “fiber connectedness along a parameter
family” without assuming any connectedness of the parameter **locus** itself.

## 6. Correct topology boundary

### 6.1 Connectedness transport under homeomorphism

Yes: an abstract homeomorphism between subspaces transports `IsConnected` once the
target connectedness theorem is available. This is standard topology and does not
require special planar structure.

### 6.2 Fullness does **not** transport under abstract subspace homeomorphism

Correctly per Review 10:
- planar fullness is extrinsic, about the complement in ambient `ℂ`;
- a bare homeomorphism `S ≃ₜ T` between subspaces does **not** imply fullness of `S`
  from fullness of `T`.

Therefore the generic fullness lemma proposed in Result 10 must **not** be used.

### 6.3 Current repository status of non-axiomatic connectedness of `MandelbrotSet`

Current status:
- **not available non-axiomatically** in this repo segment;
- the active declaration is the axiom
  `Mlc/Quadratic/Complex/Axioms.lean:23 : mandelbrot_set_connected`.

So a topology milestone depending on connectedness of `MandelbrotSet` is not
currently non-axiomatic.

### 6.4 What stronger data would be needed for fullness

To transport fullness from a model copy to an embedded parameter subset, one would
need substantially stronger ambient control, e.g.:
- an ambient homeomorphism of the plane or sphere extending the copy embedding; or
- a direct sourced theorem that the particular embedded renormalization locus is full.

A bare subspace homeomorphism is insufficient.

## 7. Final recommendation

The first honest implementation should define only:
- `BMolParameterFamily`;
- `BMolFiberConnected`;
- `connectednessLocus`;
- `mem_connectednessLocus_iff`.

This is enough to establish a clean, non-axiomatic “family + fiber-connectedness
locus” layer, while postponing all fake continuity/holomorphic-structure claims.

## 8. Decision and exact next worker task

**Decision:** **(1) signatures are ready for a small Lean implementation task.**

### Exact next worker task

Create a small Lean implementation task that adds a new file defining
`BMolParameterFamily`, `BMolFiberConnected`, `connectednessLocus`,
`mem_connectednessLocus_iff`, and one theorem showing that parameters in a set
`S ⊆ MandelbrotSet` belong to the connectedness locus of the induced
`parameterToBMol` family, using only `filled_julia_set_connected` and
`parameterToBMol_criticalValue`, with no axioms and no straightening machinery.

## 9. Exact commands used

```bash
cd /home/kir/pers/mlc && git --no-pager status --short

cd /home/kir/pers/mlc && grep -RIn --include='*.lean' \
  'structure BMol\|def criticalValue\|def criticalPoint\|structure RenormalizationRelation\|def IsFastRenormalizable' \
  .lake/packages/molecule-conjecture/Molecule | head -n 200

cd /home/kir/pers/mlc && grep -RIn --include='*.lean' \
  '^def MandelbrotSet\|^abbrev MandelbrotSet\|^def K ' \
  . .lake/packages | head -n 200

cd /home/kir/pers/mlc && grep -RIn --include='*.lean' 'axiom|sorry|admit' Mlc/**/*.lean

cd /home/kir/pers/mlc && nl -ba .lake/packages/molecule-conjecture/Molecule/BMol.lean | sed -n '20,90p'
cd /home/kir/pers/mlc && nl -ba .lake/packages/molecule-conjecture/Molecule/Rfast.lean | sed -n '1,90p'
cd /home/kir/pers/mlc && nl -ba .lake/packages/yoccoz-theorem/Yoccoz/Quadratic/Complex/Basic.lean | sed -n '30,55p'
cd /home/kir/pers/mlc && nl -ba Mlc/RenormalizationTypes.lean | sed -n '1,260p'
cd /home/kir/pers/mlc && nl -ba Mlc/FilledJuliaConnected.lean | sed -n '277,390p'
cd /home/kir/pers/mlc && nl -ba Mlc/Quadratic/Complex/Axioms.lean | sed -n '1,40p'
```

## 10. Files inspected

- `plan/GPT54_TASK_11_QUADRATIC_LIKE_FAMILY_FOUNDATION_AUDIT.md`
- `plan/GPT54_RESULT_10_RENORMALIZATION_LOCUS_SPECIFICATION.md`
- `plan/GPT54_REVIEW_10_RENORMALIZATION_LOCUS_SPECIFICATION.md`
- `Mlc/RenormalizationTypes.lean`
- `Mlc/MoleculeRenormalizationTower.lean`
- `Mlc/FilledJuliaConnected.lean`
- `Mlc/LcAtOfShrink.lean`
- `Mlc/Quadratic/Complex/Axioms.lean`
- `Mlc/ParaPuzzleConnectivity.lean`
- `.lake/packages/molecule-conjecture/Molecule/BMol.lean`
- `.lake/packages/molecule-conjecture/Molecule/Rfast.lean`
- `.lake/packages/molecule-conjecture/Molecule/Mol.lean`
- `.lake/packages/yoccoz-theorem/Yoccoz/Quadratic/Complex/Basic.lean`

## 11. Full `git status --short`

```text
?? plan/GPT54_PROMPT_11_QUADRATIC_LIKE_FAMILY_FOUNDATION_AUDIT.md
?? plan/GPT54_RESULT_09_SPECIFY_CANONICAL_PARAMETER_PIECE.md
?? plan/GPT54_RESULT_10_RENORMALIZATION_LOCUS_SPECIFICATION.md
?? plan/GPT54_REVIEW_09_SPECIFY_CANONICAL_PARAMETER_PIECE.md
?? plan/GPT54_REVIEW_10_RENORMALIZATION_LOCUS_SPECIFICATION.md
?? plan/GPT54_TASK_10_RENORMALIZATION_LOCUS_SPECIFICATION.md
?? plan/GPT54_TASK_11_QUADRATIC_LIKE_FAMILY_FOUNDATION_AUDIT.md
```

## 12. Integrity confirmation

- I wrote only the result artifact for Task 11.
- I did not edit Lean sources, plans, docs, notebooks, or previous artifacts.
- I did not commit.
- I did not introduce any `axiom`, `sorry`, or `admit`.
