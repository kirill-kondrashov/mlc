# Plan: Replace `exists_ray_preimage_green_pos_seam` With a Provable Target

## Why this plan

The current unrestricted seam

`∀ c u (‖u‖ = 1) t>0, ∃ ρ>0, G_c((ρ:ℂ) * u) = t`

is too strong globally. For some parameters/directions (e.g. numerically at
`c = 2` and non-real directions), the ray profile can have a positive minimum,
so small positive `t` may not be attained.

## Exact statement replacement (draft)

Replace the global-positive target with an anchor-threshold target:

`∀ c u (‖u‖ = 1) t,`
`  t > G_c(((‖c‖+2):ℝ) * u) →`
`  ∃ ρ, ρ > ‖c‖+2 ∧ G_c((ρ:ℂ) * u) = t`

This is aligned with the already formalized outside-open IVT lemma
`exists_ray_preimage_green`.

## Patch call sites (draft)

1. `GreenFunctionRayInversion.exists_ray_preimage_green_pos`
   - Change hypothesis from `0 < t` to
     `t > green_function c ((‖c‖ + 2 : ℝ) * u)`.
   - Change output from `ρ > 0` to `ρ > ‖c‖ + 2`.
   - Implement by delegating to `exists_ray_preimage_green`.

2. `GreenFunctionRayInversion.exists_unique_ray_preimage_green_pos`
   - Mirror the same thresholded hypothesis/output.
   - Implement by delegating to `exists_unique_ray_preimage_green`.

3. `GreenFunctionRayInversion.external_ray_map_exists_two_via_green_function`
   - Add explicit seam parameter
     `hlog_gt_anchor : ∀ w, 1 < ‖w‖ → G_2(((‖2‖+2):ℝ) * (w/‖w‖)) < log ‖w‖`.
   - Use this seam where the old proof previously used `Real.log_pos`.
   - Convert `ρ > ‖2‖ + 2` to `ρ > 0` when needed.

4. `MainConjecture.external_ray_map_exists_two_constructive`
   - Add a new rooted seam proposition/axiom for the `hlog_gt_anchor` payload.
   - Pass that seam to
     `external_ray_map_exists_two_via_green_function`.

## Notes

- This replacement keeps the development independent of
  `MLC.Quadratic.external_ray_map_exists`.
- It separates the genuinely hard part (anchor lower-bound along all normalized
  exterior directions at `c=2`) into an explicit seam, rather than encoding it
  as an over-strong existence axiom.
