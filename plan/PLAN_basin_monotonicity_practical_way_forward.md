# Plan: Basin Monotonicity Practical Way Forward

---
**Status:** `███████░░░` **68%** | **Relevance:** ⭐⭐⭐ | **Effort Remaining:** ~30-60 lines, 1-2 hrs
**Target Axiom:** `green_function_strictMono_along_ray_basin_seam`
**Last Updated:** 2026-02-26
---

## Goal
- [ ] Remove dependence on `MLC.Quadratic.green_function_strictMono_along_ray_basin_seam`
  by replacing Euclidean-ray monotonicity requirements with a true Böttcher-ray
  monotonicity/inversion path.

## Progress Implemented
- [x] Added a seam-free conditional Green-inversion route in
  `GreenFunctionRayInversion`:
  `external_ray_map_exists_two_via_green_function_of_injOn_outside_open`.
- [x] Added a MainConjecture wrapper:
  `external_ray_map_exists_two_constructive_of_green_function_of_injOn_outside_open`.
- [x] Re-routed
  `external_ray_map_exists_two_constructive_of_green_function_of_iter_left_inverse`
  through outside-open injectivity (instead of the strict-mono uniqueness seam).
- [ ] Root theorem `external_ray_map_exists_two_constructive` still uses the
  legacy strict-mono path and is the remaining call site to replace.

## Remaining Work (~30-60 lines)

### A. Replace Theorem Target
- [ ] Introduce a new seam/target statement for strict monotonicity along
  Böttcher rays (not Euclidean rays `ρ • u`).
- [ ] Mark/deprecate the Euclidean-ray seam usage points in
  `GreenFunctionRayInversion` and downstream call sites.

### Exact Replacement (Current Draft)
- [x] Introduced seam-free conditional replacement already implemented:
  `external_ray_map_exists_two_via_green_function_of_injOn_outside_open`
  with signature:
  `theorem ... (hlog_gt_anchor : GreenRayLogGtAnchorTwoSeam)
               (h_inj_outside : InjOn bottcher_map outside_open) :
               ExternalRayMapData (2 : ℂ)`.
- [ ] Final target still to implement:
  replace Euclidean-ray strict-mono uniqueness with a Böttcher-ray uniqueness
  theorem, then make `external_ray_map_exists_two_via_green_function` itself
  seam-free (no injectivity assumption needed).

### Call-Site Patch Status
- [x] Added MainConjecture wrapper:
  `external_ray_map_exists_two_constructive_of_green_function_of_injOn_outside_open`.
- [x] Patched
  `external_ray_map_exists_two_constructive_of_green_function_of_iter_left_inverse`
  to route through the wrapper above.
- [x] Added rooted conditional wrappers:
  `mlc_conjecture_of_green_function_of_injOn_outside_open_two` and
  `mlc_conjecture_of_green_function_of_iter_left_inverse_two`.
- [x] Added CP5/direct-witness Green-route wrappers.
- [x] Closed strict-mono CP5 branch-seam combiner and rerouted the unconditional
  CP5 residual function through branch seams (no explicit no-landing dependency):
  `cp5ResidualInjOnOutsideOpenSeamTwo_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam`,
  `cp5ResidualInjOnOutsideOpenSeamTwo_strictMono`,
  `external_ray_map_exists_two_constructive_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam_of_cp5ResidualTwo_unconditional_fn`.
- [x] Rewired theorem-level unconditional CP5 Green-route wrappers off the
  explicit no-landing detour:
  `external_ray_map_exists_two_constructive_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam_of_cp5ResidualTwo_unconditional`,
  `mlc_conjecture_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam_of_cp5ResidualTwo_unconditional`.
- [x] Removed dead strict-mono no-landing helper aliases made obsolete by the
  branch-combined unconditional seam path.
- [x] Extended constructive monotonicity base on real-axis directions with:
  `green_function_neg_real_eq_two`,
  `green_function_strictMono_along_neg_real_ray_two`.
- [x] Added quantitative large-norm anchor-gap discharge and cutoff-band
  reduction (`greenRayLogGtAnchorTwoCutoff`,
  `greenRayLogGtAnchorTwo_of_norm_gt_cutoff`,
  `greenRayLogGtAnchorTwoSeam_of_cutoff_band`) to isolate remaining seam debt
  to bounded annulus data.
- [x] Added `not_greenRayLogGtAnchorTwoSeam`, proving the old global
  anchor-gap seam is inconsistent and must be replaced rather than proved.
- [x] Added packaged ingress:
  `GreenFunctionDegreeOneIngressTwo` and root wrapper
  `mlc_conjecture_of_green_function_degreeOneIngressTwo`.
  Axiom scan shows this route uses only
  `Quot.sound`, `propext`, `Classical.choice`, and
  `greenRayLogGtAnchorTwo_axiom_seed` (no `external_ray_map_exists`,
  no `green_function_strictMono_along_ray_basin_seam`).
- [x] Verified that routing root through
  `injOn_outside_open_two_axiom_seed` is frontier-unsafe:
  it reintroduces `MLC.Quadratic.external_ray_map_exists`, so this route is
  blocked.

## Blockers
All strict-mono-free injectivity sources are blocked:
- `not_outsideOpenAnalyticityHypothesisTwo`
- `not_greenFunctionDegreeOneIngressTwo`
- `not_knownInjOnOutsideOpenSourceCandidateTwo`

**Only path forward: prove monotonicity directly.**
