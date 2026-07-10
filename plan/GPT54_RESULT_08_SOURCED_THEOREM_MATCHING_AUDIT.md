# GPT-5.4 Result 08: Sourced theorem-matching audit for Option A versus B

## 1. Executive decision

**Decision:** **(3) Option B required:** classical sourced theorems concern a
**different parameter object** from the repository's frozen-base target, and I did
not find a sourced implication to

```text
IsConnected ({c' | G_c(c' - c) < 2^{-n}} ∩ M).
```

The literature I could verify supports:

- connectivity / topology of **parameter wakes**, **renormalization windows**,
  and **parapuzzle pieces** defined from the **moving parameter** `c'` and its own
  dynamical combinatorics;
- phase-parameter correspondences of the form `Φ_M(c') = B_{c'}(c')` on `ℂ \ M`;
- holomorphic motion of puzzle/parapuzzle boundary configurations over a
  parameter domain.

It does **not** visibly state connectivity for the exact frozen-base set used in
Option A, where `G_c` is evaluated using the **fixed base map** `f_c` while the
ambient parameter variable is `c'`.

So the sourced audit favors **Option B**: replace/mediate through a genuine
finite-level parameter piece defined from parameter geometry, then connect it to
Lean without using the retired packaging routes.

## 2. Normalized-target comparison table

### 2.1 Repository target normalized

For fixed `c ∈ M` and fixed level `n ∈ ℕ`, the repository target is

```text
T(c,n) := {c' ∈ ℂ | G_c(c' - c) < (1/2)^n} ∩ M.
```

Field-by-field:

- **fixed / frozen data:**
  - the base parameter `c`;
  - the polynomial `f_c(z) = z^2 + c` used to define `G_c`;
  - the level `n`.
- **varying data:**
  - the parameter variable `c'`.
- **membership test:**
  - translate by `-c`, then test `c' - c` in the **dynamical Green sublevel of
    the fixed map** `f_c`.
- **final target:**
  - intersect that translated dynamical sublevel with the Mandelbrot set `M`.

In the repository this appears explicitly in
`Mlc/ParaPuzzleConnectivity.lean`:

- `mem_paraPuzzlePieceAt_iff_green`
- `paraPuzzlePieceAt_eq_green_translate`
- `green_sublevel_translate_inter_mandelbrot_connected`

### 2.2 Comparison table

| object in literature | typical definition data | frozen map or moving map? | equals `T(c,n)`? | audit |
| --- | --- | --- | --- | --- |
| dynamical puzzle piece for `f_c` | subset of dynamical plane of one fixed map `f_c`, bounded by rays/equipotentials | fixed map | no | same *phase* object before translation/intersection, not a parameter piece |
| translated dynamical Green sublevel | `{c' | G_c(c'-c) < 2^{-n}}` | fixed map | only before intersecting `M` | repository-specific identification, not a standard classical parameter object I found |
| parameter equipotential / parameter ray / wake | defined in parameter plane using `Φ_M(c')`, rays/equipotentials landing at roots, etc. | moving parameter `c'` | no | depends on external parameter geometry, not frozen `G_c` |
| parapuzzle / parameter puzzle piece containing `c` | parameters `c'` with prescribed combinatorics of `f_{c'}`; bounded by parameter rays/equipotentials and phase-parameter transport | moving map `f_{c'}` | no | the natural classical parameter object |
| phase-parameter relation | identifies parameter external coordinates of `c'` with dynamical external coordinates of the **critical value of `f_{c'}`** | moving map `f_{c'}` | no | matches `G_{c'}(c')`, not frozen `G_c(c'-c)` |

Bottom line: the repository target uses a **frozen** Green function and then cuts
by `M`; classical parapuzzle objects are defined by **moving** parameter geometry.
They are not definitionally the same.

## 3. Primary-source theorem inventory

Below I list the sources I could verify with concrete local refs and/or stable
URLs. I paraphrase rather than quote at length.

### Source A. M. Lyubich, *Dynamics of quadratic polynomials III: parapuzzle and SBR measures*

- Bibliography / URL:
  - Astérisque **261** (2000), pp. 173–200.
  - Stable URL: `https://numdam.org/item/AST_2000__261__173_0/`
- Why relevant:
  - explicitly about **parapuzzle** in the quadratic family.
- Verified support:
  - the Numdam entry confirms the exact bibliographic identity;
  - repository modern survey `refs/2512.24171v1.pdf` cites this as reference `[37]`;
  - this is a primary source for the classical parameter object on the Option B side.
- Theorem-level content used in this audit:
  - parapuzzle methods describe parameter pieces through parameter combinatorics
    and phase-parameter control, not through the frozen-base set `T(c,n)`.
- Dependence on moving map?
  - **yes**: parameter objects are built from `f_{c'}` combinatorics.
- Connectivity statement type:
  - connectedness/topology of **parapuzzle pieces** or associated parameter domains,
    not explicitly `T(c,n)`.

### Source B. M. Lyubich, *Conformal Geometry and Dynamics of Quadratic Polynomials*

- Repository ref:
  - `refs/Conformal Geometry and Dynamics of Quadratic Polynomials.pdf`
- Relevant verified sections:
  - `§29.1`–`§29.2` (parameter uniformization / phase-parameter relation), around
    extracted lines 8988ff.
  - `§45.2.1`, Proposition 7.41 and Proposition 7.42, around extracted lines
    10684ff.
- Faithful paraphrase:
  - `§29.2`: parameter external coordinates of a parameter `c' ∈ ℂ \ M` coincide
    with the dynamical external coordinates of the **critical value** for the same
    map `f_{c'}`; parameter rays/equipotentials are pulled back by `Φ_M`.
  - Proposition 7.41: a ray/equipotential configuration creating canonical almost
    renormalization moves holomorphically over a parameter window.
  - Proposition 7.42: all parameters in that window are renormalizable with a
    specified period.
- Dependence on moving map?
  - **yes**, throughout.
- Connectivity statement type:
  - parameter windows / wakes / renormalization domains and phase-parameter
    relation, not the frozen translated Green-sublevel intersection.

### Source C. 2025 survey / programmatic paper in repository

- Repository refs:
  - `refs/2512.24171v1.pdf`
  - `refs/Dudko_2512.24171.pdf`
- Relevant verified passages:
  - lines around 919 mention an “Almost-Linear puzzle-parapuzzle relation [37]”.
  - lines around 1084–1149 discuss MLC for bounded-type combinatorics and separate
    neutral / near-degenerate cases.
- Role in this audit:
  - secondary/programmatic support that current MLC strategy is framed in terms of
    **puzzles / parapuzzles** and phase-parameter relations.
- Dependence on moving map?
  - **yes**.
- Connectivity statement type:
  - high-level claims about MLC / a priori bounds / puzzle-parapuzzle machinery,
    not an exact theorem for `T(c,n)`.

### Source D. Douady–Hubbard primary references (bibliographic confirmation)

- Stable references found via Numdam / bibliographies:
  - `A. Douady & J. H. Hubbard, Étude dynamique des polynômes complexes`, Orsay,
    84-02 and 85-04;
  - `A. Douady & J. H. Hubbard, On the dynamics of polynomial-like maps`, Ann. ENS
    18 (1985), 287–343.
- Audit status:
  - I could confirm the bibliographic existence and access paths, but I did **not**
    verify a page-level theorem in these works stating connectivity of the exact
    frozen-base target `T(c,n)`.
- Dependence on moving map?
  - the standard puzzle/parapuzzle framework is moving-parameter in nature.
- Connectivity statement type:
  - classical puzzle/parapuzzle / polynomial-like geometry, not visibly `T(c,n)`.

## 4. Exact-match implication audits

I audited the natural candidate implication routes.

### Candidate theorem family 1: phase-parameter relation `Φ_M(c') = B_{c'}(c')`

Representative source support:
- `refs/Conformal Geometry and Dynamics of Quadratic Polynomials.pdf`, §29.2.

Attempted implication:

```text
phase-parameter correspondence
=> parameter equipotential / wake description
=> connectivity of a parameter piece
=> IsConnected T(c,n)
```

Missing steps:

1. Replace moving-map quantity `B_{c'}(c')` / `G_{c'}(c')` by frozen quantity
   `G_c(c'-c)`.
   - classification: **unsupported / suspect**.
2. Identify the resulting parameter domain with the specific translated Green
   sublevel `{c' | G_c(c'-c) < 2^{-n}}`.
   - classification: **unsupported**.
3. Show the `∩ M` cut matches the closure/intersection behavior of the classical
   parameter piece.
   - classification: **unsupported**.

Verdict: **no exact match**.

### Candidate theorem family 2: parapuzzle piece connectivity / topology

Representative source support:
- Lyubich Astérisque 261 (primary);
- modern survey citations to puzzle-parapuzzle relation.

Attempted implication:

```text
connected parapuzzle piece containing c
=> equals T(c,n)
=> IsConnected T(c,n)
```

Missing steps:

1. Equality between the classical parapuzzle piece and the repository’s frozen
   translated Green sublevel.
   - classification: **unsupported**.
2. Alternatively, a proved inclusion/excision theorem showing
   `T(c,n) = parapuzzle_piece ∩ M`.
   - classification: **unsupported**.
3. Any bridge that avoids silently replacing frozen `G_c` with moving geometry of
   `f_{c'}`.
   - classification: **unsupported**.

Verdict: **no exact match**.

### Candidate theorem family 3: holomorphic-motion / tubing / moving boundary results

Representative support:
- `Conformal Geometry and Dynamics of Quadratic Polynomials.pdf`, Proposition 7.41.

Attempted implication:

```text
holomorphic motion of boundary configuration
=> image domain connected
=> equals T(c,n)
```

Missing steps:

1. Produce the exact parameter slice/image equal to `T(c,n)`.
   - classification: **false/suspect as a sourced “classical theorem”**, because
     the repository already audited and retired the exact-image packaging route.
2. Convert moving boundary configuration into frozen `G_c(c'-c)` membership.
   - classification: **unsupported**.

Verdict: not acceptable for Option A matching.

## 5. Parameter-class coverage table

Even ignoring the exact-set mismatch, sourced puzzle/parapuzzle theorems do not
appear to have the universal scope of the current repository frontier axiom.

| sourced theorem family | apparent class coverage | comments relative to Option A axiom |
| --- | --- | --- |
| classical Yoccoz puzzle / parapuzzle results | chiefly finitely renormalizable / bounded combinatorics / non-renormalizable branches, depending on theorem | not obviously all `c ∈ M` |
| bounded-type ql results cited in `2512.24171` | bounded-type combinatorics | explicitly not full MLC |
| neutral / pseudo-Siegel results cited in `2512.24171` | neutral classes | separate branch, still not all `c ∈ M` |
| virtual Molecule / remaining unbounded satellite problems | unresolved programmatic scope | confirms global scope is still an active issue |

Thus even a successful match to a classical parapuzzle theorem would still need a
careful class-by-class scope audit before replacing the universal quantifier in the
Lean axiom.

## 6. Final Option A/B decision

**Option B required.**

Reasoning:

1. The exact repository target is a **frozen-base translated dynamical Green
   sublevel intersected with `M`**.
2. Verified classical sources describe **parameter pieces defined by moving
   parameter geometry**: parameter rays/equipotentials, wakes, windows,
   parapuzzle pieces, and phase-parameter correspondences tied to `f_{c'}`.
3. I found **no sourced theorem** that explicitly identifies those classical
   parameter objects with the exact set
   `{c' | G_c(c'-c) < 2^{-n}} ∩ M`.
4. Therefore Option A is not presently matched by literature in a way that can be
   cited cleanly and imported into Lean without a genuinely new bridge.

Could Option A still be derivable? Possibly, but the bridge is **not** a trivial
citation cleanup; it would need a new theorem proving that the classical
finite-level parameter piece equals or canonically mediates the frozen translated
sublevel. That is exactly why Option B is the more honest plan direction.

## 7. Next bounded task proposal

**Bounded next task:** define, at the plan/research level first, the exact
replacement **finite-level parameter piece object** to use for Option B, with a
field-by-field specification showing:

- how it is built from parameter rays/equipotentials / parapuzzle boundaries,
- the precise sourced theorem giving its connectedness/topology,
- the minimal bridge from that sourced object to the Lean `ParaPuzzlePieceAt`
  interface now used downstream.

This task must **not** use:

- `ParaPieceCarvedByMotion`,
- `ParaPieceIsMotionImage`,
- exact-image connected-source existentials,
- any packaged connectivity hypothesis.

It should only normalize the genuine parameter object and its sourced theorem.

## 8. Exact searches / commands / tool limitations

Repository / local searches run:

```bash
git --no-pager status --short
rg -n 'green_sublevel_translate_inter_mandelbrot|greenSublevel|ParaPiece|translate_inter_mandelbrot|mandelbrot_connected' Mlc/**/*.lean
pdftotext 'refs/Conformal Geometry and Dynamics of Quadratic Polynomials.pdf' - | grep -niE 'parapuzzle|para puzzle|phase-parameter|phase parameter|yoccoz|puzzle piece|equipotential|wake' | head -n 60
pdftotext 'refs/Conformal Geometry and Dynamics of Quadratic Polynomials.pdf' - | sed -n '8968,9065p'
pdftotext 'refs/Conformal Geometry and Dynamics of Quadratic Polynomials.pdf' - | sed -n '10630,10705p'
pdftotext 'refs/2512.24171v1.pdf' - | grep -niE 'Problem 4.3|Problem 4.4|virtual Molecule|parapuzzle|parameter puzzle|phase-parameter|Theorem|Proposition' | head -n 120
```

Web / source lookup used:

- `https://numdam.org/item/AST_2000__261__173_0/`
- `https://www.numdam.org/item/AST_1995__231__1_0/`
- web search for primary-source bibliographic confirmation and stable URLs.

Limitations:

- I did **not** extract page-perfect theorem text from Douady–Hubbard or Yoccoz
  that states the exact Option A target; this negative fact is part of the final
  conclusion.
- Some web-search responses were suggestive but not reliable enough to use as sole
  support; I treated them as leads only.
- The audit is therefore strongest on the **mismatch diagnosis** and weaker on any
  claim that a particular named theorem says exactly “parapuzzle pieces are
  connected” with page precision.

## 9. Complete `git status --short`

```text
M Mlc/ParaPuzzleCarvingReduction.lean
 M Mlc/Quadratic/Complex/Bottcher/Slodkowski.lean
 M plan/PLAN_04_parameter_connectivity.md
?? plan/GPT54_RESULT_01_PARAMETER_CONNECTIVITY_AUDIT.md
?? plan/GPT54_RESULT_02_FORMALIZE_CARVING_NOGO.md
?? plan/GPT54_RESULT_03_PARAPUZZLE_INTERFACE_AUDIT.md
?? plan/GPT54_RESULT_04_PROVE_MOTION_IMAGE_EQUIVALENCE.md
?? plan/GPT54_RESULT_05_REVISE_PLAN_AND_RETIRE_DEAD_ROUTES.md
?? plan/GPT54_RESULT_06_FALSIFIABILITY_AUDIT_FIXED_BASE_TARGET.md
?? plan/GPT54_RESULT_07_REPRODUCIBLE_FULL_DOMAIN_SCREENING.md
?? plan/GPT54_REVIEW_01_PARAMETER_CONNECTIVITY_AUDIT.md
?? plan/GPT54_REVIEW_02_FORMALIZE_CARVING_NOGO.md
?? plan/GPT54_REVIEW_03_PARAPUZZLE_INTERFACE_AUDIT.md
?? plan/GPT54_REVIEW_04_PROVE_MOTION_IMAGE_EQUIVALENCE.md
?? plan/GPT54_REVIEW_05_REVISE_PLAN_AND_RETIRE_DEAD_ROUTES.md
?? plan/GPT54_REVIEW_06_FALSIFIABILITY_AUDIT_FIXED_BASE_TARGET.md
?? plan/GPT54_REVIEW_07_REPRODUCIBLE_FULL_DOMAIN_SCREENING.md
?? plan/GPT54_TASK_01_PARAMETER_CONNECTIVITY_AUDIT.md
?? plan/GPT54_TASK_02_FORMALIZE_CARVING_NOGO.md
?? plan/GPT54_TASK_03_PARAPUZZLE_INTERFACE_AUDIT.md
?? plan/GPT54_TASK_04_PROVE_MOTION_IMAGE_EQUIVALENCE.md
?? plan/GPT54_TASK_05_REVISE_PLAN_AND_RETIRE_DEAD_ROUTES.md
?? plan/GPT54_TASK_06_FALSIFIABILITY_AUDIT_FIXED_BASE_TARGET.md
?? plan/GPT54_TASK_07_REPRODUCIBLE_FULL_DOMAIN_SCREENING.md
?? plan/GPT54_TASK_08_SOURCED_THEOREM_MATCHING_AUDIT.md
```

## 10. Compliance confirmation

- Repository edits made by this task: **only this result file**.
- No Lean sources, plans, docs, notebooks, or prior artifacts were edited.
- No `axiom`, `sorry`, or `admit` were introduced.
- No commit was made.
