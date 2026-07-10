# GPT-5.4 Result 26 — Pin a finite parameter graph or its exact blocker

## 1. Executive decision

**Decision:** **(3)** the **parameter external coordinate itself is the immediate missing foundation**.

After auditing the checked repository APIs and the local source text, I do **not** find a genuine checked Lean parameter-plane uniformization
`Φ_M : ℂ \ MandelbrotSet → ℂ \ closedDisk`, nor its inverse, nor parameter rays/equipotentials/landing/wakes built from it. The repository does contain substantial **dynamical-plane** Böttcher/external-ray machinery for a **fixed parameter** `c`, but that is not a parameter-plane external-coordinate layer and cannot be reinterpreted as one without the missing phase–parameter theorem.

Therefore the finite moving-parameter graph is **not** ready for direct implementation now. The first honest implementation task is to define and build the parameter external coordinate from already sourced mathematics, then derive parameter rays/equipotentials, then finite graphs/components.

## 2. Read set and audit scope

Per task instructions I read:
- `plan/GPT54_PROMPT_26_PIN_FINITE_PARAMETER_GRAPH_OR_BLOCKER.md`
- `plan/GPT54_TASK_26_PIN_FINITE_PARAMETER_GRAPH_OR_BLOCKER.md`
- `plan/GPT54_RESULT_25_SPECIFY_GENUINE_FINITE_PARAMETER_PIECE.md`
- `plan/GPT54_REVIEW_25_SPECIFY_GENUINE_FINITE_PARAMETER_PIECE.md`
- `plan/GPT54_PROGRESS_GREEN_SUBLEVEL_FRONTIER.md`

Primary repository files audited:
- `Mlc/Quadratic/Complex/Bottcher/BottcherMotion.lean`
- `Mlc/Quadratic/Complex/Bottcher/BottcherCore.lean`
- `Mlc/Quadratic/Complex/Bottcher/BottcherAxioms.lean`
- `Mlc/Quadratic/Complex/Bottcher/BottcherRayMap.lean`
- `Mlc/Quadratic/Complex/Bottcher/BottcherParamInverse.lean`
- `Mlc/Quadratic/Complex/Bottcher/BottcherOnMDefs.lean`
- `Mlc/Quadratic/Complex/Bottcher/BottcherOnMTheory.lean`
- `Mlc/Quadratic/Complex/ParaPuzzleBasis.lean`
- `Mlc/Quadratic/Complex/ParaPuzzle.lean`

Primary local source used:
- `refs/Conformal Geometry and Dynamics of Quadratic Polynomials.pdf`
  with extracted text in `/tmp/cgdqp26.txt`.

## 3. Repository capability audit

## 3.1 What does exist

### A. Fixed-parameter dynamical/exterior Böttcher side

The repository has a substantial **fixed-`c` dynamical** external-coordinate layer.
Representative items found during search:

- `Quadratic.proxy_bottcher_map c : ℂ → ℂ`
  in the Böttcher core/theory files; this is a dynamical-plane object for a fixed parameter.
- `Quadratic.external_ray_map c`
  with continuity results on `{w : ℂ | 1 < ‖w‖}` in `Mlc/Quadratic/Complex/Bottcher/BottcherRayMap.lean`.
- `theorem external_ray_map_data_of_mandelbrot (c : ℂ) (hc : c ∈ MandelbrotSet) : ...`
  in `GreenRayDischarge.lean`, again a fixed-parameter dynamical statement.
- `theorem recipBottcher_exists_analytic_inverse (c : ℂ) : ...`
  in `BottcherInverse.lean`, giving a near-infinity analytic inverse of the **fiber** Böttcher coordinate.
- `theorem exists_param_holo_bottcher_inverse ...`
  in `BottcherParamInverse.lean`, giving parameter-holomorphy of the inverse in the **joint `(c,z)` Böttcher setup**.

These are all useful for the route-(C) motion plan, but they are not a parameter-plane uniformization of `ℂ \ M`.

### B. Motion-side placeholder packaging

`Mlc/Quadratic/Complex/Bottcher/BottcherMotion.lean` contains theorem-facing placeholder wrappers such as:

```lean
def equipotential (B : BottcherData) (c : ℂ) (n : ℕ) : Set ℂ :=
  {z | ‖B.phi c z‖ = Real.exp ((1 / 2 : ℝ) ^ n)}
```

and structures like `GenuineBottcherLocalFamilyData`, `GenuineBottcherLocalParameterFamilyData`, etc.

These are still **dynamical-fiber** notions: the set lives in the `z`-plane for a chosen parameter `c`. They do not define parameter-plane equipotentials/rays in the `c'` variable.

## 3.2 Exact non-matches / blockers

### A. No parameter uniformization `Φ_M`

The source search over `Mlc/` found **no checked declaration** implementing a parameter-plane map of the form

```lean
Φ_M : {c : ℂ // c ∉ MandelbrotSet} → {w : ℂ // 1 < ‖w‖}
```

or an equivalent unbundled `ℂ → ℂ` definition on `ℂ \ MandelbrotSet`.

In particular, the searches for `ΦM`, `PhiM`, `parameter external`, `parameter equipotential`, `parameter ray`, and `parameterExternalCoord` produced no defining hits in the repository.

### B. No parameter inverse

Likewise there is no checked parameter-plane inverse declaration corresponding to

```lean
Φ_M_inv : {w : ℂ // 1 < ‖w‖} → {c : ℂ // c ∉ MandelbrotSet}
```

or equivalent.

### C. No parameter rays / equipotentials / landings / wakes

No concrete Lean declarations were found for:
- parameter external rays at angle `θ`;
- parameter equipotentials at level `t` or radius `r`;
- landing points of rational parameter rays;
- parameter wakes;
- connected components of complements of finite parameter graphs built from those objects.

### D. Apparent “On M” support is not this API

`BottcherOnMTheory.lean` still carries placeholder/axiomatic infrastructure tied to the fixed-parameter/dynamical route. The audit found explicit axiom declarations including:
- `axiom bottcher_outside_axiom : ...`
- `axiom proxy_bottcher_map_inj_on_K (c : ℂ) : ...`

These reinforce that the file is not a completed parameter-uniformization API. It is still theorem-facing scaffolding for dynamical-plane Böttcher work.

### E. Why `BottcherParamInverse` is not enough

`BottcherParamInverse.lean` proves c-holomorphy of `c ↦ φ_c⁻¹(w)` in the **joint Böttcher family**. That is a statement about the inverse of the dynamical Böttcher coordinate in the basin of infinity, not the parameter-plane map `c ↦ B_c(c)` on `ℂ \ M`.

Bridging from `φ_c` to a parameter external coordinate requires a separate parameter-plane definition
`Φ_M(c) := B_c(c)` together with its well-definedness exactly on `c ∉ M`, its conformality, inverse, and the phase–parameter identification. None of these are currently present as checked definitions.

## 4. One exact source definition

The local source **does** give a sufficiently concrete classical definition. So decision (4) is not justified.

### 4.1 Parameter external coordinate

From `/tmp/cgdqp26.txt` around the extracted lines for §29.1–§29.2:

> “Recall from Theorem 5.17 that for `c ∈ C \ M`, we have a well-defined function
> `Φ_M(c) := B_c(c)` ...”
>
> “Theorem 6.10. The Mandelbrot set `M` is connected. The function `Φ_M` conformally maps `C \ M` onto `C \ D̄`.”
>
> “Similarly to the dynamical situation ... we can now introduce parameter equipotentials ... and parameter external rays ... by pulling back round circles ... and radial rays ... by means of `Φ_M`.”

This is the precise missing foundation.

### 4.2 Exact finite-graph style description

From `/tmp/cgdqp26.txt` in the extracted §45.2.1 window passage:

> “This domain is bounded by two parameter rays of angle `θ±` and two parameter rays of angle `ψ±` truncated by the equipotential of level `2t`. The former rays land at the root `r◦` ... while the latter land at its tip `t◦`.”

This is already an exact finite graph shape:
- a finite angle set `{θ₊, θ₋, ψ₊, ψ₋}`;
- finitely many **parameter ray segments**;
- truncation by a **parameter equipotential** of specified level `2t`;
- named landing points `root`, `tip`;
- the domain is a connected component cut out by this finite graph.

### 4.3 Wake-based puzzle context

From the extracted §46.1 puzzle text:

> “Let us fix some parameter wake `W_{p/q}` ... and let `c ∈ W_{p/q}` ... Let us select some equipotential `E = E^t` ...”

So the source really does support a finite-graph/component definition in the classical mathematics. The repository problem is not underspecification of the source; it is the absence of a parameter external-coordinate API from which such objects can honestly be defined in Lean.

## 5. Minimal independent Lean definitions

Because the needed API does **not** exist, I do **not** propose compile-tested `finiteParameterGraph`, `openParameterPiece`, `closedParameterPiece` definitions yet. That would force placeholder objects with no mathematical provider.

Instead, the first missing definitions in dependency order are:

### 5.1 First missing foundation

```lean
/-- Parameter external coordinate on the complement of the Mandelbrot set. -/
def parameterExternalCoord : {c : ℂ // c ∉ MandelbrotSet} → ℂ
```

Expected target property later:
```lean
-- theorem parameterExternalCoord_norm_gt_one : 1 < ‖parameterExternalCoord c‖
```

### 5.2 Second: inverse

```lean
/-- Inverse parameter uniformization. -/
def parameterExternalCoordInv : {w : ℂ // 1 < ‖w‖} → ℂ
```

### 5.3 Then parameter rays / equipotentials

```lean
/-- Parameter equipotential of radius r>1 (or level t = log r). -/
def parameterEquipotential (r : ℝ) : Set ℂ :=
  {c | c ∉ MandelbrotSet ∧ ‖parameterExternalCoord ⟨c, ‹_›⟩‖ = r}

/-- Parameter external ray at angle θ. -/
def parameterRay (θ : Real.Angle) : Set ℂ :=
  {c | c ∉ MandelbrotSet ∧ ∃ ρ > (1 : ℝ),
      parameterExternalCoord ⟨c, ‹_›⟩ = Complex.exp (ρ.log + θ * Complex.I)}
```

The exact angle/radius encoding should be adjusted to whatever complex-polar API is most natural in Mathlib, but the dependency direction is fixed.

### 5.4 Then finite parameter graph

After rays/equipotentials/landing points exist:

```lean
structure FiniteParameterGraphData where
  angles : Finset Real.Angle
  truncationRadius : ℝ
  rootPoints : Finset ℂ


def finiteParameterGraph (G : FiniteParameterGraphData) : Set ℂ :=
  parameterEquipotential G.truncationRadius ∪
  ⋃ θ ∈ (G.angles : Set Real.Angle), parameterRay θ ∪
  (G.rootPoints : Set ℂ)
```

### 5.5 Then pieces as connected components of complements

```lean
/-- Open piece: the connected component of the graph complement containing `c₀`. -/
def openParameterPiece (G : FiniteParameterGraphData) (c₀ : ℂ) : Set ℂ :=
  connectedComponentIn (finiteParameterGraph G)ᶜ c₀

/-- Closed piece: closure of the corresponding open component. -/
def closedParameterPiece (G : FiniteParameterGraphData) (c₀ : ℂ) : Set ℂ :=
  closure (openParameterPiece G c₀)
```

These are the first honest consumer-facing definitions once the parameter external-coordinate layer exists.

## 6. Elementary topology boundary

What follows immediately from the connected-component definition is limited but useful.

### 6.1 Immediate consequences

Mathlib provides:
- `mem_connectedComponentIn` in `Topology/Connected/Basic.lean`:
  basepoint membership `c₀ ∈ connectedComponentIn F c₀` once `c₀ ∈ F`.
- `isPreconnected_connectedComponentIn` in the same file:
  the component is preconnected.
- `protected theorem IsOpen.connectedComponentIn` in
  `Topology/Connected/LocallyConnected.lean`:
  if the ambient set `F` is open and the ambient space is locally connected, then each component `connectedComponentIn F x` is open.

Since `ℂ` is locally connected, once `finiteParameterGraph G` is closed, its complement is open, so `openParameterPiece G c₀` is open.

### 6.2 What does not follow

From the component definition alone one does **not** get:
- that the piece lies in `MandelbrotSet` or has any controlled relation with `M`;
- nesting/antitonicity in depth;
- shrinkage to the base parameter;
- any parapuzzle correspondence with dynamical pieces;
- boundary decomposition by rational landing points.

All of those require the genuine parameter external-coordinate/ray/equipotential theory and further dynamical input.

## 7. First implementation milestone

The earliest real, non-axiomatic milestone is:

**Implement the parameter external coordinate**
```lean
parameterExternalCoord : {c : ℂ // c ∉ MandelbrotSet} → ℂ
```
from the sourced formula `Φ_M(c) := B_c(c)` and begin proving its basic target-side properties (`1 < ‖Φ_M(c)‖`, tangent-to-identity at infinity, later conformality/inverse).

This has a concrete downstream consumer chain:
1. `parameterExternalCoord`
2. `parameterEquipotential`, `parameterRay`
3. `finiteParameterGraph`
4. `openParameterPiece := connectedComponentIn (...)ᶜ c₀`
5. `closedParameterPiece := closure ...`

No connectivity field needs to be stored anywhere.

## 8. Exact next worker task

Suggested next worker task:

> Audit whether the current checked dynamical Böttcher family is sufficient to define
> `parameterExternalCoord (c) := B_c(c)` on `c ∉ MandelbrotSet`, and if so specify the first honest Lean definition/proof obligations for that map; otherwise pinpoint the exact missing theorem between `BottcherParamInverse`/near-infinity families and well-defined evaluation at the critical value.

This is the correct immediate follow-up because it attacks the precise blocker identified here.

## 9. Search summary

Searches performed included repository-wide scans for:
- `ΦM|PhiM|parameter external|parameter ray|parameter equipotential|wake|parameterExternal|equipotential`
- `external_ray_map|BottcherOnM|bottcher_outside_axiom|proxy_bottcher_map_inj_on_K|BottcherParamInverse|HolomorphicMotion`
- prospective names `finiteParameterGraph|openParameterPiece|closedParameterPiece`

Outcome:
- no parameter-plane external-coordinate/ray/equipotential definitions found;
- many fixed-parameter dynamical/exterior Böttcher objects found;
- placeholder/axiomatic `BottcherOnM` scaffolding still present.

## 10. Git status and write scope

`git status --short` at report time:

```text
M Mlc.lean
?? Mlc/AnalyticQuadraticLikeFamilyCore.lean
?? Mlc/BMolFilledJulia.lean
?? Mlc/GenuineBMol.lean
?? plan/GPT54_PROGRESS_GREEN_SUBLEVEL_FRONTIER.md
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
?? plan/GPT54_PROMPT_26_PIN_FINITE_PARAMETER_GRAPH_OR_BLOCKER.md
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
?? plan/GPT54_RESULT_25_SPECIFY_GENUINE_FINITE_PARAMETER_PIECE.md
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
?? plan/GPT54_REVIEW_25_SPECIFY_GENUINE_FINITE_PARAMETER_PIECE.md
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
?? plan/GPT54_TASK_26_PIN_FINITE_PARAMETER_GRAPH_OR_BLOCKER.md
```

Confirmation:
- only `plan/GPT54_RESULT_26_PIN_FINITE_PARAMETER_GRAPH_OR_BLOCKER.md` was written for this task;
- no Lean source files were edited;
- no commit was made.
