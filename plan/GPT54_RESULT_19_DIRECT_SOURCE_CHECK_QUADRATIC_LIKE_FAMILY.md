# GPT-5.4 Result 19: Direct source check of quadratic-like family definition

## Executive decision

**Decision: (1)** — direct source confirms the Result 18 skeleton is ready for implementation.

The local Lyubich PDF directly supports the key separation used in Result 18:

- the **bare quadratic-like family** consists of a parameter domain `Λ`, fiberwise quadratic-like maps `g_λ : U_λ → U'_λ`, a total source tube `U ⊂ ℂ²`, and joint holomorphicity in two variables;
- **proper**, **unfolded**, and **equipped** are additional hypotheses layered on top of that bare family;
- tubing is induced only after equipment.

So Result 18’s implementation-ready minimal structure is correctly placed **below** proper/unfolded/equipped/tubing.

## Sources inspected

Repository artifacts:

- `plan/GPT54_TASK_19_DIRECT_SOURCE_CHECK_QUADRATIC_LIKE_FAMILY.md`
- `plan/GPT54_RESULT_18_CORRECT_ANALYTIC_FAMILY_TOTAL_SPACE_SPEC.md`
- `plan/GPT54_REVIEW_18_CORRECT_ANALYTIC_FAMILY_TOTAL_SPACE_SPEC.md`

Direct PDF extraction commands:

```bash
cd /home/kir/pers/mlc && pdftotext 'refs/Conformal Geometry and Dynamics of Quadratic Polynomials.pdf' /tmp/lyubich_full.txt
grep -n -E 'Quadratic-like families|Theorem 10\.1|tube|proper|unfolded|equipped|tubing|M\(g\)|42\.1|42\.2|42\.3' /tmp/lyubich_full.txt | sed -n '1,160p'
sed -n '11656,11718p' /tmp/lyubich_full.txt
```

Compilation re-check:

```bash
cd /home/kir/pers/mlc && lake env lean /tmp/task18_probe.lean
```

## A. Exact definition table from the local PDF text

### 1. Tube over a parameter domain

**Extracted lines:** `/tmp/lyubich_full.txt:11708–11711`

> “Let π : C2 → C stand for the projection onto the ﬁrst coordinate. We call a set `U ⊂ C2` a tube over `Λ = π(U) ⊂ C` if it is a ﬁber bundle over `Λ` whose ﬁbers `U_λ = U ∩ π⁻¹ λ` are Jordan disks (either open or closed). For `X ⊂ Λ`, we let `U|X = U ∩ π⁻¹ X`.”

**Paraphrase:** a tube is not merely an arbitrary subset of `ℂ²`; it is a fiber bundle over its projection, with Jordan-disk fibers. This is stronger than just “scoped total set”, but the stronger bundle/trivialization content is used as **tube structure**, not as the bare family definition itself.

### 2. Quadratic-like family

**Extracted lines:** `/tmp/lyubich_full.txt:11656–11658`

> “• The tube `U = {(λ, z) : λ ∈ Λ, z ∈ U_λ}` is a domain in `C2`;
> • `g_λ(z)` is holomorphic in two variables on `U`.”

**Paraphrase:** the bare family data include parameterized fiber domains `U_λ`, `U'_λ`, a total source tube which is an open domain in `ℂ²`, and a joint holomorphic evaluation map on that total source. This directly supports Result 18’s `totalU`, `eval`, and `AnalyticOn ℂ eval totalU` fields.

### 3. Proper family

**Extracted lines:** `/tmp/lyubich_full.txt:11660–11668`

> “We say that `g` extends beyond `U` if there exists a domain `Λ' ⊋ Λ` and a quadratic-like family `G_λ : V_λ → V'_λ` over `Λ'` such that for `λ ∈ Λ`, `g_λ` is an adjustment … of `G_λ`.
> We call a quadratic-like family `g : U_λ → U'_λ` over `Λ` proper if
> • `g` admits an extension beyond `U`;
> • For `λ ∈ ∂Λ`, `g_λ(0) ∈ ∂U'_λ`.”

**Paraphrase:** properness is definitely **not** part of the bare family core. It is an extra condition involving extension beyond the source tube and a boundary condition on the critical value.

### 4. Unfolded family

**Extracted lines:** `/tmp/lyubich_full.txt:11668–11670`

> “… we have a well deﬁned winding number of the curve `λ ↦ g_λ(0)`, `λ ∈ ∂Λ`, around `0`. We call it the winding number of `g` and denote `w(g)`. A proper family `g` is called unfolded if `w(g) = 1`.”

**Paraphrase:** unfolded is layered on top of properness; it is a winding-number condition, not part of the raw analytic family object.

### 5. Equipped family, holomorphic motion, and tubing

**Extracted lines:** `/tmp/lyubich_full.txt:11673–11689` and `11690–11696`

> “Finally, we want the fundamental annulus `A_λ = Ū'_λ \ U_λ` of `g_λ` to move holomorphically with `λ`. So, assume that there is an equivariant holomorphic motion `h_λ : A_◦ → A_λ` …”
>
> “Denote this holomorphic motion by `h`. We say that the quadratic-like family `g` is equipped with the holomorphic motion `h`.”
>
> “For equipped families, there is a natural choice of tubing … Namely, select any tubing `B_◦ : A_◦ → A[r, r²]` for the base point, and then let
> `(42.1)  B_λ = B_◦ ◦ h⁻¹_λ`.
> These are tubings since the holomorphic motion `h_λ` is equivariant.”

**Paraphrase:** equipment means extra holomorphic-motion structure on the fundamental annulus; tubing is then derived from that equipment. Neither belongs in the minimal bare-family structure.

### 6. Connectedness locus `M(g)`

**Extracted lines:** `/tmp/lyubich_full.txt:11700–11703`

> “The Mandelbrot set of the quadratic-like family is deﬁned as
> `M(g) = {λ ∈ Λ : J(g_λ) is connected}`.
> If `g` is proper, then `M(g)` is compactly contained in `Λ`.”

**Paraphrase:** the connectedness locus is defined for any quadratic-like family; compact containment requires properness.

## B. Field-by-field validation of Result 18

### `parameterSet : Set ℂ` with `isOpen_parameterSet`

**Supported.** The source works over a parameter domain `Λ`, and the total source tube is a domain in `ℂ²`. The minimal Lean representation with `parameterSet` open is appropriate.

### `fiber : parameterSet → GenuineBMol`

**Supported as Lean packaging.** The source is fiberwise: `g_λ : U_λ → U'_λ`. Packaging each fiber as `GenuineBMol` is a faithful local representation of the per-parameter quadratic-like map data.

### `totalU`, `totalV` open and scoped over the parameter domain

**Supported, but source tube language is slightly richer.** The source requires the source/target tubes to live over `Λ`; Result 18’s scoping laws correctly forbid off-domain junk. The source’s “fiber bundle with Jordan-disk fibers” is stronger than current Lean fields, but that stronger structure belongs to a later named tube layer unless and until a theorem needs it.

### Section equality with fiber domains

**Supported.** This is the Lean way to enforce that the total spaces really recover the intended fibers `U_λ`, `U'_λ`.

### Global representative `eval : ℂ × ℂ → ℂ` plus agreement on `totalU`

**Supported.** The source only specifies holomorphicity “in two variables on `U`”. A global representative restricted by `eval_agrees` is a standard Lean encoding of that partial map.

### `AnalyticOn ℂ eval totalU`

**Supported.** This exactly matches “`g_λ(z)` is holomorphic in two variables on `U`.” The previous rejected attempt to impose analyticity on `Λ × ℂ` was too strong; Result 18’s restriction to `totalU` is source-correct.

## C. What the source additionally contains, and where it belongs

The source adds the following beyond the bare family core:

- tube as a **fiber bundle** with Jordan-disk fibers;
- properness (extension beyond `U` plus boundary critical-value condition);
- unfoldedness (`w(g) = 1`);
- equipped family via equivariant holomorphic motion of the fundamental annulus;
- tubing derived from equipment.

These do **not** force a change to Result 18’s minimal structure, because Result 18 was intentionally specifying only the minimal analytic family layer needed before later proper/unfolded/equipped refinements.

## D. Final corrected signature

No change from Result 18 is needed. The implementation-ready signature remains:

```lean
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
  eval_agrees (c : parameterSet) {z : ℂ} (hz : (c.1, z) ∈ totalU) :
    eval (c.1, z) = (fiber c : BMol).f z
  analyticOn_totalU : AnalyticOn ℂ eval totalU
```

External namespace definitions for sections and `[simp]` lemmas remain the correct API shape.

## E. Temporary compile outcome

Re-run command:

```bash
cd /home/kir/pers/mlc && lake env lean /tmp/task18_probe.lean
```

Outcome:

- passed (`exit code 0`)

## F. Exact next worker task

Implement the new Lean module for `AnalyticQuadraticLikeFamily` exactly as in Result 18/19, and leave tube-bundle, proper, unfolded, equipped, and tubing structure for later dedicated layers.

## G. Full git status --short

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
?? plan/GPT54_PROMPT_18_CORRECT_ANALYTIC_FAMILY_TOTAL_SPACE_SPEC.md
?? plan/GPT54_PROMPT_19_DIRECT_SOURCE_CHECK_QUADRATIC_LIKE_FAMILY.md
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
```

## Confirmation

Only this result artifact was written. No repository source files or dependencies were edited, and no commit was made.
