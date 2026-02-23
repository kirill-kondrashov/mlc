# PLAN: CP5 residual injectivity seam (unconditional)

## Goal
Prove:

`CP5ResidualInjOnOutsideOpenSeamTwo`

and then instantiate:

`external_ray_map_exists_two_constructive_of_cp5ResidualTwo`

to obtain:

`CP5ResidualTwo → Quadratic.ExternalRayMapData (2 : ℂ)`.

## Proof decomposition
Split the seam into two branch obligations:

1. `CP5ResidualLocalHomeomorphInjSeamTwo`
   - Input: `IsClosed(range) ∧ IsLocalHomeomorph(restrict-map)`.
   - Target: `Set.InjOn (Quadratic.bottcher_map (2 : ℂ)) outside_open`.
   - Candidate route: proper/local-homeomorph + degree-one fiber seed route from `BottcherOutsidePlan`.
   - **Update:** Created `Mlc/Quadratic/Complex/Bottcher/DegreeOneInj.lean` to prove `injOn_of_proper_localHomeomorph_asymptotic_at_infinity`. This is the intended constructive closure for this branch.

2. `CP5ResidualLandingInjSeamTwo`
   - Input: `ExternalRayLandsOutsideOpen (2 : ℂ)`.
   - Target: same outside-open injectivity.
   - Candidate route: landing -> refinement plus a refinement-to-injectivity bridge (currently missing).

Then combine both branch seams via:

`cp5ResidualInjOnOutsideOpenSeamTwo_of_branchSeams`.

## Current implementation status
- Added global seam and CP5 wiring in `Mlc/MainConjecture.lean`.
- Added branch seam definitions and branch-combiner theorem:
  - `CP5ResidualLocalHomeomorphInjSeamTwo`
  - `CP5ResidualLandingInjSeamTwo`
  - `cp5ResidualInjOnOutsideOpenSeamTwo_of_branchSeams`
- Added equivalence and branch-consumer wrappers:
  - `cp5ResidualInjOnOutsideOpenSeamTwo_iff_branchSeams`
  - `external_ray_map_exists_two_constructive_of_cp5ResidualTwo_of_branchSeams`
- Added explicit axiom-seeded fallback witness (for isolation, not closure):
  - `injOn_outside_open_two_axiom_seed`
  - `cp5ResidualInjOnOutsideOpenSeamTwo_axiom_seed`
  - `cp5ResidualLocalHomeomorphInjSeamTwo_axiom_seed`
  - `cp5ResidualLandingInjSeamTwo_axiom_seed`
  - `cp5ResidualInjOnOutsideOpenSeamTwo_axiom_seed_of_branchSeams`
  - `external_ray_map_exists_two_constructive_of_cp5ResidualTwo_axiom_seam`
- Branch proofs themselves remain open.
