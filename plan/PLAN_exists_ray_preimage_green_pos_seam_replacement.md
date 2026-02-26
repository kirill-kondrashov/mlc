# Plan: Replace `exists_ray_preimage_green_pos_seam` With a Provable Target

## Goal
- [x] Replace the over-strong global-positive seam with an anchor-threshold seam.
- [x] Keep the external-ray constructive path independent of
  `MLC.Quadratic.external_ray_map_exists`.

## Parallel Placement
- [x] Assigned to **Track B (Anchor-Gap Elimination)** in
  `PLAN_axiom_elimination_status.md`.
- [x] Coupled with `PLAN_green_function_ray_inversion_c2.md` call-site work.

## Statement Replacement (Final Target)
- [x] Replace:
  `∀ c u (‖u‖ = 1) t>0, ∃ ρ>0, G_c((ρ:ℂ) * u) = t`
- [x] With:
  `∀ c u (‖u‖ = 1) t,`
  `t > G_c(((‖c‖+2):ℝ) * u) →`
  `∃ ρ, ρ > ‖c‖+2 ∧ G_c((ρ:ℂ) * u) = t`.

## Call-Site Patch List
- [x] `GreenFunctionRayInversion.exists_ray_preimage_green_pos`
  - change hypothesis to anchor-threshold form.
  - change conclusion radius bound to `ρ > ‖c‖ + 2`.
- [x] `GreenFunctionRayInversion.exists_unique_ray_preimage_green_pos`
  - mirror thresholded hypothesis and stronger radius bound.
- [x] `GreenFunctionRayInversion.external_ray_map_exists_two_via_green_function`
  - use explicit seam payload:
    `hlog_gt_anchor : ∀ w, 1 < ‖w‖ → G₂(anchor(w)) < log ‖w‖`.
- [x] `Mlc/MainConjecture.lean`
  - pass rooted seam payload through existing seeded constructor chain.

## Current Status
- [x] Draft replacement is validated against existing outside-open IVT lemma
  `exists_ray_preimage_green`.
- [x] Constructive `c = 2` endpoint already accepts `hlog_gt_anchor`.
- [x] Generalized statement and call sites are aligned in the current `c = 2`
  constructive path.

## Next Steps
- [x] Remove or rename legacy comments/names that still describe this as a
  "replacement draft" now that it is live.
- [x] Run `lake build Mlc.Quadratic.Complex.Bottcher.GreenFunctionRayInversion`.
- [x] Re-run `make check` and verify frontier remains exactly the two target axioms.
