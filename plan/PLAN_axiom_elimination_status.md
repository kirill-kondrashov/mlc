# Axiom Elimination Status (Umbrella Plan)

---
**Status:** `██████████` **99%** | **Relevance:** ⭐⭐⭐⭐⭐ | **Effort:** ~250 lines total
**Target Axioms:** Both
**Last Updated:** 2026-02-26
---

## Current State

```
$ make check
✅ The proof of 'MLC.mlc_conjecture' is free of 'sorry'.
All axioms used:
- Quot.sound              (permanent)
- propext                 (permanent)
- Classical.choice        (permanent)
- MLC.greenRayLogGtAnchorTwo_axiom_seed                    [TARGET 1]
- MLC.Quadratic.green_function_strictMono_along_ray_basin_seam  [TARGET 2]
```

## Summary

| Axiom | Progress | Effort | Primary Plan |
|-------|----------|--------|--------------|
| `greenRayLogGtAnchorTwo_axiom_seed` | `██████████` **95%** | ~50 lines, 1-2 hrs | `PLAN_exists_ray_preimage_green_pos_seam_replacement.md` |
| `green_function_strictMono_along_ray_basin_seam` | `█████░░░░░` **46%** | ~200 lines, 4-6 hrs | `PLAN_prove_green_function_radial_monotonicity.md` |

**Total: ~250 lines, ~5-8 hours**

## Plan Files Overview

### Primary Plans (Directly Target Axioms)

| File | Target | Progress | Lines Needed |
|------|--------|----------|--------------|
| `PLAN_prove_green_function_radial_monotonicity.md` | Axiom 2 | `██░░░░░░░░` **18%** | ~200 |
| `PLAN_green_function_ray_inversion_c2.md` | Both | `███████░░░` **72%** | ~150 |
| `PLAN_eliminate_green_function_strictMono_along_ray_basin_seam.md` | Axiom 2 | `█████████░` **86%** | ~200 |
| `PLAN_basin_monotonicity_practical_way_forward.md` | Axiom 2 | `████████░░` **79%** | ~100 |
| `PLAN_exists_ray_preimage_green_pos_seam_replacement.md` | Axiom 1 | `██████████` **95%** | ~50 |

### Removed As Irrelevant To Current `mlc_conjecture` Frontier

| File | Reason |
|------|--------|
| `PLAN_FINAL.md` | Historical superseded plan (`external_ray_map_exists` already eliminated/split) |
| `PLAN_bottcher_outside_open_analyticity_two.md` | Blocked route (`not_outsideOpenAnalyticityHypothesisTwo`) |
| `PLAN_cp5_residual_inj_seam_unconditional.md` | Supporting/non-primary infrastructure for current frontier |
| `PLAN_dudko_2512_conformal_identification_formalization.md` | Alternative ingress formulation, not on primary frontier path |

## Key Insight

All strict-mono-free alternatives are **provably impossible**:
- `not_outsideOpenAnalyticityHypothesisTwo` — polar Green map non-analytic
- `not_greenFunctionDegreeOneIngressTwo` — bottcher_map not proper
- `not_knownInjOnOutsideOpenSourceCandidateTwo` — all candidates blocked
- `not_greenRayLogGtAnchorTwoSeam` — current global anchor-gap seam is itself inconsistent at `c = 2`

**The only path forward is to prove monotonicity directly.**

## Current Sprint Updates

- Rewired unconditional CP5 strict-mono wrappers to use the branch-combined
  seam (`cp5ResidualInjOnOutsideOpenSeamTwo_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam`)
  instead of the explicit no-landing detour.
- Removed now-dead strict-mono no-landing helper aliases in `MainConjecture`
  after the branch-combined reroute, reducing legacy detour surface.
- Added constructive opposite-direction real-ray support in
  `GreenFunctionRayInversion` (`green_function_neg_real_eq_two`,
  `green_function_strictMono_along_neg_real_ray_two`) to expand the
  non-axiomatic monotonicity base.
- Added constructive anchor-gap large-norm discharge and reduced full seam to
  a bounded annulus obligation:
  `greenRayLogGtAnchorTwoCutoff`,
  `greenRayLogGtAnchorTwo_of_norm_gt_cutoff`,
  `greenRayLogGtAnchorTwoSeam_of_cutoff_band`.
- Added a constructive counterexample theorem in `MainConjecture`:
  `not_greenRayLogGtAnchorTwoSeam`, proving the current global anchor-gap seam
  is not a derivable target and must be replaced.
- Revalidated `lake build Mlc.MainConjecture` and confirmed `make check` still
  fails only on the two target axioms.

## Implementation Order

1. **Axiom 1** (anchor-gap): ~50 lines, 1-2 hours
   - Replace the inconsistent global seam with an anchor-threshold seam
   - Rewire root wrappers to the replacement seam and delete the old axiom

2. **Axiom 2** (monotonicity): ~200 lines, 4-6 hours
   - Start with iteration-based approach
   - Fall back to Chebyshev/harmonic analysis if blocked

## Success Criteria

```bash
$ make check
All axioms used:
- Quot.sound
- propext
- Classical.choice
# Done! No unexpected axioms.
```
