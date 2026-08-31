# GPT-5.4 Result 14: Genuine BMol family refinement audit

## Executive decision

**Decision: (2)** — a small honest local refinement for genuine compact containment is ready, but the analytic-family representation should remain a separate focused implementation/audit step.

This is not a verdict that the vendored `BMol` is unusable. It is usable as the fiber core for intrinsic filled Julia definitions, and it can be locally refined without vendored edits. However, the honest Lyubich-style family layer cannot be represented by continuity/holomorphy into vendored `BMol`, because `BMol` currently carries a discrete placeholder topology.

## Sources inspected

Required files read:

- `Mlc/BMolFilledJulia.lean`
- `plan/GPT54_RESULT_13_IMPLEMENT_BMOL_FILLED_JULIA_FOUNDATION.md`
- `plan/GPT54_REVIEW_13_IMPLEMENT_BMOL_FILLED_JULIA_FOUNDATION.md`
- `.lake/packages/molecule-conjecture/Molecule/BMol.lean`
- `plan/GPT54_RESULT_10_RENORMALIZATION_LOCUS_SPECIFICATION.md`
- `plan/GPT54_TASK_14_GENUINE_BMOL_FAMILY_REFINEMENT_AUDIT.md`

Additional audits/tests:

- searched vendored `Mathlib`/package sources for ready-made relative-compactness names;
- temporary Lean compilation tests under `/tmp` with `lake env lean`.

## A. Mathematical and Mathlib audit

### A.1 What the vendored `QuadraticLikeMap` already stores

From `Molecule/BMol.lean`, `QuadraticLikeMap` currently has concrete fields:

- `U V : Set ℂ`
- `f : ℂ → ℂ`
- `isOpen_U`, `isOpen_V`
- `isConnected_U`, `isConnected_V`
- `simplyConnected_U`, `simplyConnected_V`
- `subset : U ⊆ V`
- `closure_subset : closure U ⊆ V`
- `differentiable_on : DifferentiableOn ℂ f U`
- `maps_to : MapsTo f U V`
- `proper : IsProperMap (maps_to.restrict f U V)`
- degree-two encoding via unique simple critical point:
  - `unique_critical_point : ∃! c ∈ U, deriv f c = 0`
  - `simple_critical_point : ∀ c ∈ U, deriv f c = 0 → deriv (deriv f) c ≠ 0`

So the vendored fiber already represents most of the bare *fiberwise* quadratic-like data:

- topological-disk-style openness/connectedness/simple connectedness of `U`, `V`;
- holomorphicity on `U` (via `DifferentiableOn ℂ`);
- proper restricted map;
- degree-two critical-point encoding.

### A.2 Exact missing property for honest quadratic-like compact containment

The missing item is not a strict subset condition; it is **genuine relative compactness / compact containment** of `U` in `V`.

Why `closure_subset : closure U ⊆ V` is not enough by itself:

- in an arbitrary ambient topological space, `closure U ⊆ V` only says the closure lies inside `V`;
- it does **not** imply `closure U` is compact;
- on an unbounded ambient space such as `ℂ`, one can have `closure U ⊆ V` with `closure U` still noncompact.

Thus the honest extra condition needed locally is:

- `IsCompact (closure g.U)`

combined with the already-stored `closure_subset : closure g.U ⊆ g.V`.

That pair expresses the standard compact-containment content `U ⊂⊂ V` in the ambient plane.

### A.3 Mathlib naming audit

I searched vendored package sources for ready-made named predicates such as “relatively compact”, “compact containment”, “precompact”, etc. I did **not** find an obvious existing convenience predicate already available under those names in this environment.

So the compile-oriented honest formulation is to write the topology directly:

```lean
IsCompact (closure g.U)
```

with no opaque placeholder.

Imports actually observed as sufficient in temp tests were lightweight; no special relative-compactness API surface was needed beyond the ordinary topology/analysis imports already present through `Molecule.BMol` and the tested skeleton imports.

## B. Refinement design without vendored edits

I compared the three local designs requested.

### B.1 Design 1 — named predicate on `BMol`

Compile-oriented shape:

```lean
abbrev HasCompactClosureInV (g : BMol) : Prop :=
  IsCompact (closure g.U)
```

Pros:

- smallest statement layer;
- easy to apply to existing `g : BMol`;
- reuses vendored fields directly.

Cons:

- downstream functions repeatedly need both `g` and the proof;
- theorem statements become proof-argument-heavy;
- less ergonomic for parameter families whose fibers should already be refined.

### B.2 Design 2 — wrapper structure bundling `g : BMol` with proof

Compile-tested shape:

```lean
structure GenuineBMol where
  toBMol : BMol
  compact_closure : IsCompact (closure toBMol.U)

instance : Coe GenuineBMol BMol := ⟨GenuineBMol.toBMol⟩
```

Pros:

- best balance of explicitness and ergonomics;
- coercion lets existing `filledJuliaSet : BMol → Set ℂ` be reused unchanged;
- namespace is clearer than a raw subtype when later adding fiber-specific helper lemmas;
- avoids opaque family fields while keeping the refinement local and honest.

Cons:

- one more wrapper layer.

### B.3 Design 3 — subtype of `BMol`

Shape:

```lean
{g : BMol // IsCompact (closure g.U)}
```

Pros:

- mathematically minimal;
- automatic projection to underlying `BMol`.

Cons:

- poorer namespacing/readability for a foundation layer expected to grow;
- less pleasant field names in theorem statements;
- tends to produce more subtype-transport friction in downstream code/documentation.

### B.4 Recommendation

**Recommend design 2: a wrapper structure** `GenuineBMol` with a coercion to `BMol`.

Reason: it keeps the enhancement concrete and topology-based, reuses `filledJuliaSet` untouched, and gives a stable place for future local lemmas without committing the project to vendored edits.

### B.5 Degree-two encoding judgment

For this foundation layer, the current degree-two encoding is **sufficient**.

Reason:

- Task 14 is about honest compact containment and honest parameter dependence;
- the existing fields already encode “quadratic-like of degree 2” in a usable local way;
- any future mismatch with source-level normalization/equipment is a **separate** refinement question, not a blocker for this immediate compact-containment layer.

So no correction is required before introducing `GenuineBMol`.

## C. Honest parameter dependence

### C.1 What must not be done

The vendored topology on `BMol` is explicitly discrete:

```lean
instance : TopologicalSpace BMol := ... True
instance : DiscreteTopology BMol := ⟨rfl⟩
```

Therefore statements such as

- `Continuous F.map`
- `AnalyticOn ℂ F.map ...`
- “holomorphic family valued in `BMol`”

would be mathematically dishonest as a model of Lyubich-style analytic family dependence.

### C.2 Honest family representation

The honest family should make parameter dependence explicit through the *joint evaluation map*, not through the placeholder topology on `BMol`.

Compile-tested skeleton:

```lean
structure AnalyticBMolFamily where
  parameterSet : Set ℂ
  fiber : ℂ → GenuineBMol
  jointMap : ℂ → ℂ → ℂ
  jointMap_agrees : ∀ c, c ∈ parameterSet → jointMap c = (fiber c : BMol).f
  jointMap_analytic :
    AnalyticOn ℂ (fun p : ℂ × ℂ => jointMap p.1 p.2) (parameterSet ×ˢ Set.univ)
```

Interpretation:

- `parameterSet : Set ℂ` is the parameter domain `Λ`;
- `fiber c : GenuineBMol` supplies the fiberwise domains `U_c`, `V_c`, properness, etc.;
- `jointMap c z` is the actual two-variable family map;
- `jointMap_agrees` ties the explicit analytic family map to the fiber’s stored `f`;
- `jointMap_analytic` is the honest currently expressible analytic predicate.

### C.3 What is ready now vs deferred

**Ready now:**

- explicit parameter domain `Λ : Set ℂ`;
- refined fibers with genuine compact closure;
- a joint map `Λ × ℂ → ℂ`;
- analytic dependence expressed directly as `AnalyticOn ℂ` on the product set.

**Still deferred / needs separate foundations:**

- fiber-domain variation laws for `U λ`, `V λ` beyond merely storing them fiberwise;
- unfolded/winding-number-one conditions;
- equipment / holomorphic motion of the fundamental annulus;
- tubing data;
- straightening map and its theorem package.

### C.4 Relation to implemented `BMolParameterFamily`

Current `BMolParameterFamily` is still useful as a **minimal set-theoretic connectedness-locus shell**. It should **not** be upgraded in place to mean an analytic family.

Recommendation:

- keep `BMolParameterFamily` as the minimal family shell already implemented;
- introduce a **separate** analytic family structure (`AnalyticBMolFamily` over `GenuineBMol`) for true parameter dependence.

This avoids conflating two distinct roles:

1. “a parameterized collection of fibers”;
2. “a holomorphic quadratic-like family in the Lyubich/Douady–Hubbard sense”.

## D. Import and compilation audit

### D.1 Import minimization for `Mlc/BMolFilledJulia.lean`

Task requirement: test whether `Mlc/BMolFilledJulia.lean` can replace
`import Mlc.RenormalizationTypes` with a smaller direct import.

Temp test command:

```bash
cd /home/kir/pers/mlc && cat > /tmp/task14_import_test.lean <<'EOF'
import Molecule.BMol
import Mathlib.Topology.Connected.Basic

open Set
open Complex
open Function

namespace Molecule

def filledJuliaSet (g : BMol) : Set ℂ :=
  {z : ℂ | ∀ n : ℕ, (g.f^[n]) z ∈ g.U}

@[simp] lemma mem_filledJuliaSet_iff (g : BMol) (z : ℂ) :
    z ∈ filledJuliaSet g ↔ ∀ n : ℕ, (g.f^[n]) z ∈ g.U := Iff.rfl

lemma filledJuliaSet_eq_iInter_preimage (g : BMol) :
    filledJuliaSet g = ⋂ n : ℕ, (g.f^[n]) ⁻¹' g.U := by
  ext z
  simp [filledJuliaSet]

end Molecule
EOF
cd /home/kir/pers/mlc && lake env lean /tmp/task14_import_test.lean
```

Outcome:

- **passed** (`exit code 0`).

Conclusion:

- yes, the current file’s declarations do **not** require `Mlc.RenormalizationTypes`;
- a later narrow implementation pass can safely test replacing that import with the smaller direct import `Molecule.BMol` plus the basic topology import.

No repo edit was made in this audit task.

### D.2 Compile test for recommended refinement/family skeleton

Temp test command:

```bash
cd /home/kir/pers/mlc && cat > /tmp/task14_refinement_test2.lean <<'EOF'
import Molecule.BMol
import Mlc.BMolFilledJulia
import Mathlib.Topology.Connected.Basic
import Mathlib.Analysis.Analytic.Basic

open Set
open Complex
open Function

namespace Molecule

abbrev HasCompactClosureInV (g : BMol) : Prop :=
  IsCompact (closure g.U)

structure GenuineBMol where
  toBMol : BMol
  compact_closure : HasCompactClosureInV toBMol

instance : Coe GenuineBMol BMol := ⟨GenuineBMol.toBMol⟩

@[simp] lemma genuine_filledJuliaSet_def (g : GenuineBMol) :
    filledJuliaSet (g : BMol) = {z : ℂ | ∀ n : ℕ, (((g : BMol).f)^[n]) z ∈ (g : BMol).U} := rfl

structure AnalyticBMolFamily where
  parameterSet : Set ℂ
  fiber : ℂ → GenuineBMol
  jointMap : ℂ → ℂ → ℂ
  jointMap_agrees : ∀ c, c ∈ parameterSet → jointMap c = (fiber c : BMol).f
  jointMap_analytic : AnalyticOn ℂ (fun p : ℂ × ℂ => jointMap p.1 p.2) (parameterSet ×ˢ Set.univ)

end Molecule
EOF
cd /home/kir/pers/mlc && lake env lean /tmp/task14_refinement_test2.lean
```

Outcome:

- **passed** (`exit code 0`).

## E. Source-to-field map for Theorem 10.1 inputs

Using Result 10’s normalized theorem package:

### E.1 Already represented faithfully

At the **fiber** level, the vendored `BMol` already represents:

- open domains `U`, `V`;
- connected / simply connected domains;
- holomorphic map on `U` (`DifferentiableOn ℂ`);
- `MapsTo f U V`;
- properness of the restricted map;
- degree-two critical-point package.

### E.2 Handled by the proposed refinement

Handled by local wrapper `GenuineBMol`:

- genuine compact containment via `IsCompact (closure U)` together with existing `closure U ⊆ V`.

### E.3 Intentionally deferred

Still intentionally outside this local refinement:

- proper **family** over parameter domain `Λ`;
- unfolded / winding-number-one condition;
- equipment (holomorphic motion of fundamental annulus);
- tubing;
- connectedness locus theorem package `M(g)`;
- straightening map/homeomorphism package;
- root/tip completion package `M°` from Theorem 10.15 context.

### E.4 Blocked by named missing foundation

Blocked or at least not honestly expressible through the current vendored family shell:

- analytic dependence encoded as maps into `BMol` (blocked by the discrete placeholder topology);
- any theorem requiring genuine holomorphic motion/tubing foundations as structured data;
- any attempt to claim the skeleton already satisfies Theorem 10.1.

So the honest status is:

- **fiber compact-containment refinement:** ready;
- **analytic-family foundation:** shape is clear, but deserves a separate implementation/audit pass;
- **Theorem 10.1 package:** still far beyond the current skeleton.

## Recommended next worker task

Create a small implementation task that does exactly two things and nothing more:

1. introduce a new local refinement module with
   - `HasCompactClosureInV : BMol → Prop`,
   - `GenuineBMol`,
   - coercions/lemmas showing reuse of `filledJuliaSet`;
2. reduce `Mlc/BMolFilledJulia.lean`’s import from `Mlc.RenormalizationTypes` to the smaller direct import path verified above.

Do **not** combine that worker with analytic-family machinery, tubing, or Theorem 10.1 claims.

## Commands run

```bash
cd /home/kir/pers/mlc && git --no-pager status --short
cd /home/kir/pers/mlc && lake env lean /tmp/task14_import_test.lean
cd /home/kir/pers/mlc && lake env lean /tmp/task14_refinement_test2.lean
```

I also ran grep-style audits over vendored package sources for relative-compactness / compact-containment naming and over the repo/result files named above.

## Full `git status --short`

```text
 M Mlc.lean
?? Mlc/BMolFilledJulia.lean
?? plan/GPT54_PROMPT_11_QUADRATIC_LIKE_FAMILY_FOUNDATION_AUDIT.md
?? plan/GPT54_PROMPT_12_BMOL_FILLED_JULIA_DEFINITION.md
?? plan/GPT54_PROMPT_13_IMPLEMENT_BMOL_FILLED_JULIA_FOUNDATION.md
?? plan/GPT54_PROMPT_14_GENUINE_BMOL_FAMILY_REFINEMENT_AUDIT.md
?? plan/GPT54_RESULT_09_SPECIFY_CANONICAL_PARAMETER_PIECE.md
?? plan/GPT54_RESULT_10_RENORMALIZATION_LOCUS_SPECIFICATION.md
?? plan/GPT54_RESULT_11_QUADRATIC_LIKE_FAMILY_FOUNDATION_AUDIT.md
?? plan/GPT54_RESULT_12_BMOL_FILLED_JULIA_DEFINITION.md
?? plan/GPT54_RESULT_13_IMPLEMENT_BMOL_FILLED_JULIA_FOUNDATION.md
?? plan/GPT54_REVIEW_09_SPECIFY_CANONICAL_PARAMETER_PIECE.md
?? plan/GPT54_REVIEW_10_RENORMALIZATION_LOCUS_SPECIFICATION.md
?? plan/GPT54_REVIEW_11_QUADRATIC_LIKE_FAMILY_FOUNDATION_AUDIT.md
?? plan/GPT54_REVIEW_12_BMOL_FILLED_JULIA_DEFINITION.md
?? plan/GPT54_REVIEW_13_IMPLEMENT_BMOL_FILLED_JULIA_FOUNDATION.md
?? plan/GPT54_TASK_10_RENORMALIZATION_LOCUS_SPECIFICATION.md
?? plan/GPT54_TASK_11_QUADRATIC_LIKE_FAMILY_FOUNDATION_AUDIT.md
?? plan/GPT54_TASK_12_BMOL_FILLED_JULIA_DEFINITION.md
?? plan/GPT54_TASK_13_IMPLEMENT_BMOL_FILLED_JULIA_FOUNDATION.md
?? plan/GPT54_TASK_14_GENUINE_BMOL_FAMILY_REFINEMENT_AUDIT.md
```

## Confirmation

- Only the present result artifact was written in this task.
- No Lean source, vendored dependency, or prior plan artifact was edited.
- No commit was made.
