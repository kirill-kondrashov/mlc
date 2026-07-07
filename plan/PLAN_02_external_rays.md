# PLAN 02: Prove the external-ray existence and continuity axioms

**Status:** ACTIVE  
**Depends on:** `PLAN_00_frontier_overview.md`

## Goal

Replace the axioms

```lean
MLC.Quadratic.external_ray_map_exists
MLC.Quadratic.extended_ray_map_continuous
```

by theoremized constructions.

## Current formal state

There are already multiple theorem surfaces proving special external-ray existence statements, especially in the `c = 2` route. In particular, the repository contains several theorems of the form

```lean
external_ray_map_exists_two_...
```

in the degree-one and Green-function inversion files.

However the generic reusable layers still consume the arbitrary-parameter axioms

```lean
MLC.Quadratic.external_ray_map_exists
MLC.Quadratic.extended_ray_map_continuous
```

from `Mlc/Quadratic/Complex/Bottcher/BottcherAxioms.lean`.

Representative downstream uses remain genuinely generic in `c`, for example:

- `Mlc/ParaPuzzleConnectivity.lean` derives Böttcher surjectivity from `external_ray_map_exists c`;
- `Mlc/GreenSublevelJoinedToKc.lean` builds radial paths via
  ```lean
  ContinuousOn.comp_continuous (extended_ray_map_continuous c) ...
  ```
- `Mlc/Quadratic/Complex/Bottcher/BottcherOnMTheory.lean` continues to depend on the same generic continuity seam.

So root specialization alone does not reduce the checked frontier.

## Readiness assessment

At present, PLAN 02 is only partially ready.

- **Existence:** medium mathematical readiness, but low interface readiness. Theoremized constructive/global Böttcher packages already exist, and `GreenFunctionRayInversion.lean` already contains bridges from genuine inverse packages to `ExternalRayMapDataFor`. The missing step is surfacing this as an arbitrary-parameter public constructor matching the exact API consumed downstream.
- **Continuity:** still low readiness as a frontier-reducing attack, because `extended_ray_map_continuous c` is defined from the same generic choice-based external-ray package and no arbitrary-parameter theorem currently replaces it.
- **Local refactor potential:** low at the moment, since the visible consumers are parameter-generic rather than root-specialized.

## Constructive true-Böttcher route (active) — analyticity ingredient landed

The `_of_analyticAt_of_injOn_outside_open` constructors in `BottcherOutsidePlan.lean`
reduce axiom 1 at `c = 2` to three residual facts on `{‖z‖ > 4}` for the **true**
holomorphic Böttcher coordinate: analyticity, injectivity, closed range.  (The
default `proxy_bottcher_map = polar_green_map` is the *radial* proxy
`(z/‖z‖)·exp(G)`, which is genuinely non-holomorphic — the `arg z` phase — so those
constructors must be fed the true map, not the radial proxy.)

The true coordinate is the convergent product `φ(z) = z · ∏ₖ (1 + c/z_k²)^{1/2^{k+1}}`,
already scaffolded in `BottcherOutsidePlan.lean`:

- `nearOneCorrectionFactor c N z = (1 + (c/z^{2^{N+1}})/((f^[N]z / z^{2^N})²))^{1/2^{N+1}}`
  — branch-safe factor (fractional power of a term → 1, no sector restriction).
- `finiteProductBottcherRatio c n = ∏_{k<n} nearOneCorrectionFactor c k` — partial products.
- `finiteProductBottcherApprox c n z = z · finiteProductBottcherRatio c n z`.
- Normalization-at-infinity of each partial product is **done**
  (`tendsto_finiteProductBottcherApprox_div_atInfinity`).
- `correctionProductBottcherRatio c` — the infinite ordered product (true ratio).
- **Open convergence seam:** `CorrectionProductConvergesOnExterior c R` (defined, not
  proven) — `HasProdLocallyUniformlyOn` of the correction factors on `{R < ‖z‖}`.

**Landed this iteration** (`Mlc/Quadratic/Complex/Bottcher/BottcherProductAnalytic.lean`,
no new axioms; frontier unchanged at 5):

- `analyticAt_quadratic_map`, `analyticAt_iterate_quadratic_map` — every iterate
  `(quadratic_map c)^[N]` is entire.
- `nearOneCorrectionFactor_analyticAt` — each correction factor is analytic at `z`
  when `z ≠ 0`, the base ratio `(f^[N]z/z^{2^N}) ≠ 0`, and the branch-safe base is in
  `slitPlane` (via Mathlib `AnalyticAt.cpow`).
- `finiteProductBottcherRatio_analyticAt` — each finite partial product is analytic
  under the same pointwise hypotheses (via `Finset.analyticAt_fun_prod`).

**Base-simplification breakthrough (landed).**  The branch-safe base telescopes to the
classical Böttcher form: for `z ≠ 0` and `z_N := (quadratic_map c)^[N] z ≠ 0`,
`(c/z^{2^{N+1}})/(z_N/z^{2^N})² = c/z_N²` (`nearOneCorrectionFactor_base_eq`), hence
`nearOneCorrectionFactor c N z = (1 + c/z_N²)^{1/2^{N+1}}`
(`nearOneCorrectionFactor_eq_orbit`).  This collapses *every* pointwise hypothesis to a
single orbit-norm bound `‖z_N‖`, and `iterate_quadratic_map_norm_ge` gives
`‖z_N‖ ≥ ‖z‖` whenever `‖z‖ ≥ ‖c‖+1`.  Consequently the analyticity hypotheses are now
discharged uniformly on the far exterior:

- `nearOneCorrectionFactor_analyticAt_of_norm_gt` and
  `finiteProductBottcherRatio_analyticAt_of_norm_gt` — analytic on
  `{‖c‖+1 ≤ ‖z‖} ∩ {‖c‖ < ‖z‖²}` with **no** side hypotheses (base arg
  `‖c/z_N²‖ ≤ ‖c‖/‖z‖² < 1` gives slit membership directly).

This supplies the analytic-uniform-limit *input*: once `CorrectionProductConvergesOnExterior 2 R`
is proven, the limit `correctionProductBottcherRatio 2` is analytic on `{‖z‖ > R}` as a
locally-uniform limit of these analytic partial products.

**Remaining decomposition for axiom 1 at `c = 2`:**

1. ~~Uniform base-ratio bound~~ — **DONE** via the base simplification above.  The
   analyticity hypotheses (`z ≠ 0`, base ratio `≠ 0`, slit membership) are all
   discharged on the far exterior `{‖c‖+1 ≤ ‖z‖} ∩ {‖c‖ < ‖z‖²}`.
2. ~~M-test term bound~~ — **DONE** as `nearOneCorrectionFactor_sub_one_norm_le`
   (`BottcherProductAnalytic.lean`): for `‖c‖+1 ≤ ‖z‖` and `‖c‖/‖z‖² ≤ ½`,
   `‖nearOneCorrectionFactor c N z − 1‖ ≤ 3·2^{-(N+1)}·(‖c‖/‖z‖²)`.  Proof writes the
   factor as `exp(a·log(1+w))` (via `cpow_def_of_ne_zero`, base in `slitPlane`), with
   `w = c/z_N²` (`‖w‖ ≤ ‖c‖/‖z‖²`, using `iterate_quadratic_map_norm_ge`) and
   `a = 2^{-(N+1)}`, then combines `Complex.norm_log_one_add_half_le_self`
   (`‖log(1+w)‖ ≤ (3/2)‖w‖`) with `Complex.norm_exp_sub_one_sub_id_le`
   (`‖exp ζ − 1‖ ≤ 2‖ζ‖` for `‖ζ‖ ≤ 1`).  The `∑_N 2^{-(N+1)}` factor makes this
   summable with uniform sum `≤ 3·(‖c‖/‖z‖²) ≤ 3‖c‖/R²`.
3. ~~Convergence seam~~ — **DONE** as `correctionProductConvergesOnExterior_of_norm_bounds`
   (`BottcherProductAnalytic.lean`): for any `c` with `‖c‖+1 ≤ R` and `2‖c‖ ≤ R²`,
   `CorrectionProductConvergesOnExterior c R` holds.  Proof is a Weierstrass M-test:
   `nearOneCorrectionFactor_sub_one_norm_le` majorizes `‖factor − 1‖` by the summable
   geometric sequence `3·2^{-(n+1)}·(‖c‖/R²)`, so Mathlib's
   `Summable.hasProdLocallyUniformlyOn_nat_one_add` gives locally uniform convergence
   to the *unconditional* product `∏' i, nearOneCorrectionFactor c i z`; pointwise
   multipliability then collapses the conditional filter to the unconditional one
   (`tprod_eq_of_multipliable_unconditional`), matching `correctionProductBottcherRatio c`
   via `TendstoLocallyUniformlyOn.congr_right`.  Instantiates at `c=2` for any `R ≥ 3`
   (e.g. `R = 4`, the constructor's `{‖z‖ > 4}` region).
4. ~~Analyticity of the limit~~ — **DONE** as
   `correctionProductBottcherRatio_differentiableOn_exterior` /
   `correctionProductBottcherRatio_analyticAt_of_norm_gt` /
   `correctionProductBottcherApprox_analyticAt_of_norm_gt`
   (`BottcherProductAnalytic.lean`).  The ordered correction product — and hence the
   full candidate coordinate `correctionProductBottcherApprox c z = z·(ratio)` — is
   holomorphic on `{z | R < ‖z‖}` (for `‖c‖+1 ≤ R`, `2‖c‖ ≤ R²`), obtained from the
   convergence seam via `TendstoLocallyUniformlyOn.differentiableOn` (Weierstrass:
   locally-uniform limit of holomorphic partials is holomorphic) then
   `DifferentiableOn.analyticAt`.
5. **Injectivity** on `{‖z‖ > R}` and **closed range**, then feed the
   `_of_analyticAt_of_injOn_outside_open` constructor — after re-plumbing it (or a
   sibling) onto the true coordinate rather than the radial proxy.


## Split subproblems

### A. Existence

Search for reusable theorem data already equivalent to

```lean
Quadratic.ExternalRayMapData c
```

or enough to replace direct use of `external_ray_map_exists`.

### B. Continuity

Construct a theorem route for

```lean
ContinuousOn (Quadratic.extended_ray_map c) {w | 1 ≤ ‖w‖}
```

or refactor generic downstream users to use a weaker theoremized continuity statement that is already available.

## Current blocker

The blocker is sharper than a mere API mismatch. Specializing only the root case does not remove these axioms from the checked frontier because downstream files quantify over arbitrary `c`. A direct attempt to cut over `BottcherAxioms.external_ray_map_exists` to the generic constructor chain was re-tested and immediately hit an import cycle

```lean
BottcherAxioms → ConstructiveBasinCoordinate → BottcherOutsidePlan → … → BottcherOnMTheory → BottcherAxioms.
```

So even before the missing witness construction, the current file graph prevents a direct theorem replacement in `BottcherAxioms.lean` without first extracting a lower-layer interface or moving the constructive route into a dependency that does not import the axiom-facing layer. And although the theoremized infrastructure in `ConstructiveBasinCoordinate.lean` and `GreenFunctionRayInversion.lean` already contains the full conversion chain

```lean
ClassicalGlobalExtensionFromNearInfinityDataFor c
→ ClassicalGlobalBottcherTheoremFor c
→ UnifiedGlobalBottcherTheoremFor c
→ GenuineBottcherRouteFor c
→ ExternalRayMapData c
```

there is still no generic theorem producing any of the precursor packages

```lean
ClassicalGlobalExtensionFromNearInfinityDataFor c
MonodromyTrivializingCoverBasinExtensionDataFor c
PrincipalPullbackCoherentDataFor c
LogSeriesExteriorInverseBasinExtensionDataFor c
```

for arbitrary `c`. The checked repo now does package the principal-pullback route
more cleanly once such coherent data exists:

```lean
PrincipalPullbackCoherentDataFor c
→ LogSeriesBasinExtensionDataFor c
→ ∃ φ, GenuineBottcherNearInfinityDataFor c φ ∧
      GenuineBottcherCoordinateDataFor c φ
→ ClassicalGlobalBottcherTheoremFor c
→ UnifiedGlobalBottcherTheoremFor c   -- after the inverse package is added
```

So the remaining blocker is not near-infinity wiring anymore; it is the actual
construction of generic coherent-data / inverse-package witnesses, plus the newly verified layering seam.

A first workaround step is now complete: the theorem-light proxy/external-ray interface has been split into the lower file `BottcherCore`, and `BottcherAxioms.lean` is thinner. This does not yet remove any axiom, but it isolates the public proxy/data layer from the wrapper axioms.

Reinspection after this split shows the blocker has narrowed but not disappeared. `GreenFunctionRayInversion.lean` already contains the exact theorem surface one would want for the existence cutover,

```lean
GenuineBottcherRouteFor c → ∃ φ, ExternalRayMapDataFor c φ
```

but that file still imports `BottcherOnMTheory.lean`, and `BottcherOnMTheory.lean` still depends on `BottcherAxioms.lean` via `bottcher_seq_converges`, `external_ray_map`, and `extended_ray_map_continuous`. So the remaining cycle is now a more precise constructive-side cycle:

```lean
BottcherAxioms → ConstructiveBasinCoordinate/GreenFunctionRayInversion → BottcherOnMTheory → BottcherAxioms.
```

So the next honest cut is split in three:

1. audit the `BottcherOnMTheory` dependency from `GreenFunctionRayInversion` and remove it if it is only a stale import; this cleanup has now landed, and `GreenFunctionRayInversion.lean` builds without importing `BottcherOnMTheory.lean` at all;
2. expose theorem bridges from the stronger constructive theorem surfaces. This has now also landed: `GreenFunctionRayInversion.lean` proves that both `UnifiedGlobalBottcherTheoremFor c` and `ClassicalGlobalBottcherTheoremFor c` (plus a supplied inverse-package constructor) imply
   ```lean
   ∃ φ, ExternalRayMapDataFor c φ.
   ```
3. the root cutover is still honestly blocked: `ExternalRayMapData c` is specifically the package for `proxy_bottcher_map c`, while the new theorem bridges only produce data for a theorem-facing coordinate `φ`. So replacing
   ```lean
   external_ray_map_exists : ExternalRayMapData c
   ```
   still requires the missing identification/transport step from the constructive `φ` to `proxy_bottcher_map c`.
4. there is now a second explicit workaround route recorded in checked code: instead of proving `φ = proxy_bottcher_map c`, it would also be enough to derive one of the already theoremized proxy-side hypothesis bundles from `BottcherOutsidePlan.lean` (for example closed-range plus outside-open analyticity/injectivity or the local-slit / iterate-left-inverse variants) and then invoke those existing constructors.
5. A fresh audit of that workaround route narrows the smallest plausible target further: the most realistic proxy-side bundle is currently `external_ray_map_data_of_isClosedRange_restrict_of_outsideOpenAnalyticityHypothesis` together with either outside-open injectivity or the iterate-left-inverse route. The file already provides the reductions
   ```lean
   IsProperMap (proxy_bottcher_map_outside_open_to_exterior c)
   → IsClosed (Set.range (proxy_bottcher_map_outside_open_to_exterior c))
   ```
   and
   ```lean
   QuadraticMapIterLeftInverseOnBasin c
   → Set.InjOn (proxy_bottcher_map c) {z | ‖z‖ > ‖c‖ + 2}.
   ```
   So the honest remaining bottleneck on this workaround path is not the final constructor itself, but the absence of a checked derivation of either restricted-map properness / closed range or `QuadraticMapIterLeftInverseOnBasin c` from `UnifiedGlobalBottcherTheoremFor c`.
6. A second freshly audited workaround is to weaken small downstream consumers before replacing the public axiom itself. The first concrete candidate is `MainConjecture.BottcherSurjOnExterior`: it only needs exterior surjectivity, and the current lemma derives that from the stronger proxy-specific package `Quadratic.ExternalRayMapData c`. This suggests a truthful intermediate refactor path: introduce theorem-facing surjectivity extractors from `ExternalRayMapDataFor c φ` or `GenuineBottcherInversePackageFor c φ`, then rewrite consumers that do not actually use `proxy_bottcher_map c` specifically. That would not remove the public axiom yet, but it could shrink the set of generic downstream files that force the cutover to land all at once.
7. This first intermediate step is now implemented in checked code: `MainConjecture.lean` defines the theorem-facing seam
   ```lean
   BottcherSurjOnExteriorFor (φ : ℂ → ℂ) : Prop
   ```
   together with the extractor
   ```lean
   ExternalRayMapDataFor c φ → BottcherSurjOnExteriorFor φ.
   ```
   This is small but real progress: existing constructive theorem bridges in `GreenFunctionRayInversion.lean` can now feed surjectivity-only arguments without first solving the blocked `φ → proxy_bottcher_map c` transport problem.
8. The next root-only attempt was also checked honestly. A direct theorem
   ```lean
   BottcherSurjOnExteriorFor φ → LocallyConnectedSpace mandelbrotSet
   ```
   does **not** typecheck against the existing fiber bridge, because the current checked bridge still expects fibers for the proxy-specific coordinate `proxy_bottcher_map (2 : ℂ)`. So the theorem-facing surjectivity seam is real, but the root-level MLC closure route has not yet been generalized away from the proxy map.
9. The maximal checked root weakening available at that stage was therefore the extractor
   ```lean
   Quadratic.ExternalRayMapData (2 : ℂ) →
     BottcherSurjOnExteriorFor (Quadratic.proxy_bottcher_map (2 : ℂ)).
   ```
   This sharpened the obstruction: the remaining missing step was not surjectivity extraction, but a theorem-facing replacement for the existing proxy-specific fiber package.
10. A further honest workaround step has now landed in `MainConjecture.lean`: besides the surjectivity seam, the file now also contains theorem-facing exact-fiber infrastructure for the canonical sequence `approach_one_seq`, namely
   ```lean
   BottcherApproachOneSeqFiberDataFor (φ : ℂ → ℂ)
   BottcherApproachOneSeqFiberDataFor_of_surjOnExteriorFor
   ```
   together with the induced theorem-facing convergent-preimage-sequence extractor.
11. This still does **not** close the root contradiction theorem in theorem-facing form. The existing `c = 2` contradiction route for approach-to-`1` preimages uses proxy-specific identities such as
   `Quadratic.norm_bottcher_eq_exp_green (2 : ℂ)`, hence it is still tied to
   `proxy_bottcher_map (2 : ℂ)` rather than an abstract coordinate `φ`.
12. So the current honest blocker is now even sharper: to turn the new theorem-facing fiber seam into a root MLC bridge, one needs either
   - a theorem-facing analogue of the Green/Böttcher identities used in the contradiction, or
   - a transport theorem identifying the constructive `φ` with `proxy_bottcher_map (2 : ℂ)` on the needed domain.
   A first checked step in this direction now exists: `MainConjecture.lean` contains an abstract theorem-facing contradiction schema at `c = 2` for any coordinate `φ`, assuming only
   - the modulus identity `‖φ z‖ = exp(green_function (2 : ℂ) z)`,
   - continuity of `φ` on `K(2) \ {0}`,
   - and a new explicit root-obstruction seam
     ```lean
     NoKPointMapsToOneFor (2 : ℂ) φ
     ```
     packaging `∀ z ∈ K(2), φ z ≠ 1`.
   The old proxy contradiction is now just a specialization of that abstract lemma, and the blocker is now stated in theorem-facing form rather than hidden inside the proxy package.
13. A fresh audit also exposes an important consistency constraint on any root-only PLAN 02 shortcut. `GreenFunctionRayInversion.lean` contains several positive constructors for
   ```lean
   Quadratic.ExternalRayMapData (2 : ℂ)
   ```
   but only under additional hypotheses such as outside-open injectivity, strict Green-function radial monotonicity, anchor-gap inequalities, or eventual-injectivity packages. Meanwhile `MainConjecture.lean` proves
   ```lean
   not_externalRayMapData_two
   ```
   for the current proxy setup. So the remaining root seam is not merely “some proof missing”: any successful cutover must identify exactly which extra hypotheses fail for the present proxy package, or else replace the proxy package itself by a theorem-facing coordinate before invoking those constructors.
14. This means the live PLAN 02 existence subproblem has effectively split again into two honest routes:
   - **proxy-side route:** derive one of the existing positive constructor hypothesis bundles from unified/global Böttcher data and explain why this does not contradict `not_externalRayMapData_two` (which would force a hidden hypothesis mismatch to surface explicitly), or
   - **theorem-facing route:** stay with `ExternalRayMapDataFor c φ` and continue refactoring consumers until the proxy-specific contradiction is no longer the gatekeeper.
15. `GreenSublevelJoinedToKc.lean` is currently not such a consumer: its path construction uses `extended_ray_map_continuous c` and `extended_ray_map_lands`, so it still depends on the full axiom-backed wrapper rather than bare surjectivity.
16. A further audit fixes the exact root obstruction more sharply. The legacy wrapper
    ```lean
    UnifiedGenuineRootKernelTwo
    ```
    still contains
    ```lean
    Quadratic.UnifiedGlobalBottcherTheoremFor (2 : ℂ),
    ```
    and `MainConjecture.lean` already records that this statement is mathematically false for `c = 2` because the basin is not simply connected. Therefore PLAN 02 cannot be closed by pushing the root through `UnifiedGlobalBottcherTheoremFor (2 : ℂ)`.
17. The current basin-differentiability seam has also been rechecked more precisely in Lean. `MainConjecture.lean` now contains the helper
    ```lean
    differentiableOn_of_analyticAt_on_open
    ```
    so the missing field for
    ```lean
    Quadratic.GenuineBottcherCoordinateDataFor (2 : ℂ)
      (Quadratic.proxy_bottcher_map (2 : ℂ))
    ```
    has been reduced to pointwise analyticity on `Quadratic.basin_of_infinity (2 : ℂ)`. But the available local theorem in `BottcherOutsidePlan.lean`
    ```lean
    proxy_bottcher_map_analyticAt_of_mem_nhds_slit_basin
    ```
    still requires `slit_orbit c ∈ 𝓝 z`. By contrast, the escape machinery routed through `InverseBranchSlitUse.lean` only gives basin membership in `eventual_slit_set c`, and the file already proves that a generic bridge from outside-open/eventual-slit data to full `slit_orbit` control would force
    ```lean
    {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2} ⊆ slit_orbit (2 : ℂ),
    ```
    which is refuted by checked negative theorems in `BottcherOutsidePlan.lean`. So the next honest formal task is not to search for an omitted neighborhood argument, but to refactor the theorem-facing analyticity package so that it can use weaker eventual-slit / local-tail hypotheses instead of `slit_orbit`-neighborhood assumptions.
17. Consequently the only mathematically coherent continuation of PLAN 02 is the theorem-facing route: refactor root consumers so that they use `ExternalRayMapDataFor (2 : ℂ) φ` together with the explicit root obstruction seam
    ```lean
    NoKPointMapsToOneFor (2 : ℂ) φ,
    ```
    rather than any kernel containing `UnifiedGlobalBottcherTheoremFor (2 : ℂ)`.
18. That refactor has now been started inside `MainConjecture.lean`: the file contains theorem-facing root closure theorems
    ```lean
    mlc_conjecture_of_bottcherSurjOnExteriorFor_two
    mlc_conjecture_of_externalRayMapDataFor_two
    ```
    whose hypotheses are exactly
    - theorem-facing minimal/external surjectivity,
    - the modulus identity `‖φ z‖ = exp(green_function (2 : ℂ) z)`,
    - continuity on `K(2) \ {0}`,
    - and `NoKPointMapsToOneFor (2 : ℂ) φ`.
    Thus the root closure statement no longer requires `UnifiedGlobalBottcherTheoremFor (2 : ℂ)`.
19. The remaining PLAN 02 task is therefore precise: produce those three theorem-facing root hypotheses for the chosen constructive coordinate `φ`, or prove an identification transporting them from an already checked coordinate package.
20. A first transport pattern is now formalized. `MainConjecture.lean` contains a proxy-specialized theorem
    ```lean
    mlc_conjecture_of_externalRayMapData_two_via_theoremFacing
    ```
    showing that the former explicit root closure is an instance of the new abstract theorem-facing bridge, obtained by supplying:
    - `Quadratic.norm_bottcher_eq_exp_green (2 : ℂ)`,
    - `proxy_bottcher_map_continuousAt_of_ne_zero (2 : ℂ)`,
    - `proxy_bottcher_map_eq_one_not_mem_K_two`.
    Thus the root closure mechanism has been separated from the proxy formulas; only the input hypotheses remain proxy-specialized.
21. Since no checked uniqueness theorem identifying a constructive coordinate with `proxy_bottcher_map (2 : ℂ)` is presently available, the missing transport statement is now isolated explicitly as a packaged seam
    ```lean
    RootBottcherTransportDataFor φ,
    ```
    together with the immediate constructor from a pointwise equality
    ```lean
    φ = Quadratic.proxy_bottcher_map (2 : ℂ).
    ```
22. The literature search refines the theorem-facing route. A basin-level uniqueness statement for normalized quadratic Böttcher coordinates may still remain useful as an auxiliary theorem, and the checked file now isolates it as
    ```lean
    RootBottcherUniquenessSeam.
    ```
    This seam expresses agreement of two theorem-facing genuine Böttcher coordinates on `basin_of_infinity (2 : ℂ)`.
23. However the current main blocker is **not** basin-level uniqueness. The missing theorem is a root-side boundary-extension statement, now isolated directly in the checked code through
    ```lean
    RootBottcherBoundaryExtensionHypothesesFor φ,
    RootBottcherBoundaryExtensionSeam,
    RootBottcherBoundaryExtensionDataFor φ.
    ```
    In the literature this is governed by Carathéodory-type extension of the normalized Böttcher coordinate, prime-end boundary identification, and local connectivity of the basin boundary / Julia set at the root parameter.
24. Accordingly the current theorem-facing target is the boundary package
    ```lean
    RootBottcherBoundaryExtensionDataFor φ
    ```
    and its transport into
    ```lean
    RootBottcherTransportDataFor φ.
    ```
    Concretely one must derive
    - `‖φ z‖ = exp(green_function (2 : ℂ) z)` for all `z`,
    - continuity of `φ` on `K(2) \ {0}`,
    - `NoKPointMapsToOneFor (2 : ℂ) φ`.
25. This packaging step has now been carried out in checked code at the theorem-facing level by introducing
    ```lean
    RootBottcherBoundaryExtensionHypothesesFor φ,
    RootBottcherBoundaryExtensionDataFor φ,
    ```
    where the former isolates the explicit extra assumptions and the latter records exactly the three root-side consequences needed for closure.
26. The next formal work on the root branch is therefore now split as follows.
    1. use the bookkeeping theorem
       ```lean
       RootBottcherBoundaryExtensionDataFor φ → RootBottcherTransportDataFor φ;
       ```
    2. isolate the weakest literature-facing seam actually needed by the current root bridge, now recorded as
       ```lean
       RootBottcherBoundaryExtensionSeam,
       ```
       namely:
       ```lean
       GenuineBottcherCoordinateDataFor (2 : ℂ) φ →
         RootBottcherBoundaryExtensionHypothesesFor φ →
         RootBottcherBoundaryExtensionDataFor φ;
       ```
    3. implement the missing explicit-model bridge in checked Lean rather than only in the notebook. The concrete file-by-file target is now:
       - **File 1:** a new root-model file, tentatively
         ```text
         Mlc/Quadratic/Complex/Bottcher/RootChebyshevModel.lean
         ```
         defining the explicit Chebyshev-side maps
         ```lean
         rootChebyshevPsi (w : ℂ) : ℂ := w + w⁻¹
         rootChebyshevPhi (z : ℂ) : ℂ := (z + Complex.sqrt (z^2 - 4)) / 2
         ```
         together with the basic algebraic identities near infinity;
       - **File 2:** a companion boundary file, tentatively
         ```text
         Mlc/Quadratic/Complex/Bottcher/RootBoundaryExtension.lean
         ```
         proving the explicit boundary formulas and packaging them into
         `RootBottcherBoundaryExtensionHypothesesFor φ` /
         `RootBottcherBoundaryExtensionDataFor φ` for the theorem-facing coordinate;
       - **File 3:** the existing bridge file
         ```text
         Mlc/MainConjecture.lean
         ```
         consuming the new boundary package via
         ```lean
         RootBottcherBoundaryExtensionDataFor φ → RootBottcherTransportDataFor φ
         ```
         and then feeding the result into
         `mlc_conjecture_of_externalRayMapDataFor_two_of_transport`.
    4. inside this new root-model branch, the theorem dependencies should be introduced in the following order:
       ```lean
       rootChebyshevPsi_def
       rootChebyshevPhi_def
       rootChebyshevPsi_mul_unitCircle
       rootChebyshevPsi_exp_eq_two_mul_cos
       rootChebyshevPhi_eq_on_rootChebyshevPsi
       rootChebyshevPhi_boundary_eq_exp
       rootChebyshevPhi_boundary_norm_eq_one
       rootChebyshevPhi_boundary_eq_one_iff
       rootChebyshevBoundaryExtensionHypotheses
       rootChebyshevBoundaryExtensionData
       ```
       where the mathematically critical output is the Lean theorem
       ```lean
       rootChebyshevPhi_boundary_eq_exp :
         ∀ {θ : ℝ}, 0 ≤ θ → θ ≤ Real.pi →
           rootChebyshevPhi ((2 * Real.cos θ : ℝ) : ℂ) = Complex.exp (θ * Complex.I)
       ```
       or an equivalent normalization of the same statement.
    5. once the explicit `P(z)=z^2-2` theorem is present, add the affine-conjugacy transport layer with candidate theorem names
       ```lean
       rootAffineConj (z : ℂ) : ℂ := Complex.I * z
       rootAffineConj_inv (w : ℂ) : ℂ := -Complex.I * w
       rootAffineConj_semiconj
       rootBottcher_transport_eq
       ```
       capturing
       ```lean
       A ∘ (fun z => z^2 + 2) = (fun z => z^2 - 2) ∘ A
       ```
       and
       ```lean
       φ_f z = -Complex.I * rootChebyshevPhi (Complex.I * z).
       ```
    6. finally, isolate the remaining proxy-identification seam explicitly instead of hiding it inside the notebook narrative. The current minimal candidate theorem surface is
       ```lean
       rootProxyBottcher_agrees_with_transported_model
       ```
       asserting agreement of the transported explicit coordinate with
       `Quadratic.proxy_bottcher_map (2 : ℂ)` on the domain needed by
       `RootBottcherTransportDataFor φ`; if full pointwise equality is too strong, split it into the three consequence theorems
       ```lean
       rootProxyBottcher_norm_eq_exp_green_of_explicit_model
       rootProxyBottcher_continuousOn_K_two_of_explicit_model
       rootProxyBottcher_noKPointMapsToOne_of_explicit_model.
       ```
    7. only after the root explicit-model bridge is checked should basin-level uniqueness be reconsidered as an auxiliary theorem; it is no longer the primary blocker.
    8. then feed the resulting transport data into
       ```lean
       mlc_conjecture_of_externalRayMapDataFor_two_of_transport.
       ```
27. In particular, the previously attempted derivation from `RootBottcherUniquenessSeam` directly to `RootBottcherTransportDataFor φ` should remain discarded: the checker correctly exposed that basin equality alone does not yield the required statements on `K(2)`.
28. The updated Plan-02 priority is therefore: first close the explicit-root boundary-extension gap in Lean; only after that revisit generic cutover work for `external_ray_map_exists`, and leave `extended_ray_map_continuous` for a second pass.

Only after this existence chain is genuinely theoremized does attacking continuity become realistic.

29. Sharpened analyticity obstruction and new checked tooling (`BottcherOnMTheory.lean`):
    - At `c = 2` the set `slit_orbit (2)` has **empty interior** (complement is a dense union of analytic preimage arcs of the negative real ray). Hence every `slit_orbit c ∈ 𝓝 z` hypothesis in the analyticity API is vacuous at `c = 2`, so the `slit_orbit`-based route cannot establish basin analyticity anywhere at `c = 2`. This also explains the checked negative theorems (`not_outside_open_subset_slit_orbit_two`).
    - The power-approximation route `proxy_bottcher_map_differentiableOn_open` is inadequate for the same structural reason: each approximant `F_n(z) = (f^[n] z)^{1/2^n}` is differentiable only on `{z | f^[n] z ∈ slitPlane}` (now recorded honestly as `bottcher_approx_differentiableOn_single_slit`), and this branch cut sweeps across every fixed neighbourhood as `n → ∞`. The honest weakest hypothesis is `proxy_bottcher_map_differentiableOn_open_of_eventually_iter_slit`, which is still unsatisfiable on a fixed neighbourhood of a generic-angle basin point.
    - New checked complex-analytic tool: `differentiableAt_of_continuousAt_kth_root` (with `exists_holomorphic_kth_root`, `finite_kth_rootsOfUnity`) — a continuous non-vanishing `k`-th root of a locally holomorphic non-vanishing function is holomorphic.
    - New checked pointwise reduction: `proxy_bottcher_map_differentiableAt_of_iterate` — if `proxy_bottcher_map c` is holomorphic near a forward iterate `f^[n] z₀`, it is holomorphic at `z₀`. Uses `bottcher_conj_iter`, `proxy_bottcher_map_ne_zero_of_mem_basin`, and `proxy_bottcher_map_continuousAt_of_ne_zero`. This transports holomorphy inward with a **fixed** escape time, avoiding the moving branch cut.
    - Remaining single ingredient: a base region of unconditional analyticity near infinity from the log-series Böttcher product (`logSeriesBottcherApprox`, `nearOneLogCorrection_simple_arg_mem_slitPlane_of_large_radius`), whose factors `1 + c/(f^[m] z)^2` stay near `1` (in `slitPlane`) for large `m` on outside-open regardless of the iterate's argument. Proving `∀ z, ‖z‖ > ‖c‖ + 2 → AnalyticAt (proxy_bottcher_map c) z` from this product, then feeding it through the reduction + `basin_escape_outside_open`, yields `BasinAnalyticityHypothesis (2)` and then the missing `DifferentiableOn` field.

## Success criterion

1. both axioms are removed from `make check`;
2. the remaining frontier is strictly smaller;
3. no replacement non-core theorem-hook axiom appears.
