# Plan: Eliminate `MLC.Quadratic.external_ray_map_exists`

## Scope
- Remove `MLC.Quadratic.external_ray_map_exists` from the axiom footprint of
  `MLC.mlc_conjecture`.
- Keep top-level theorem signatures stable.
- Avoid introducing replacement axioms.

## Current Status (2026-02-17)
- `make check` for `MLC.mlc_conjecture` currently reports only:
  - `Quot.sound`
  - `propext`
  - `Classical.choice`
  - `MLC.Quadratic.external_ray_map_exists`
- `external_ray_map_exists` is used by:
  - `Quadratic.external_ray_map` (choice of inverse branch)
  - `MLC.false_of_external_ray_axioms` in `Mlc/MainConjecture.lean`
  - several Böttcher helper lemmas (`bottcher_left_inv`, `bottcher_map_surj`, etc.)

## Root Cause
- The current `mlc_conjecture` closes by contradiction via
  `false_of_external_ray_axioms`.
- That contradiction explicitly uses `Classical.choose_spec (external_ray_map_exists (2 : ℂ))`.
- Therefore this axiom is currently the single non-core dependency.

## Strategy Options
1. **Primary target (recommended): remove contradiction route dependency**
   - Refactor top-level closure to avoid `false_of_external_ray_axioms`.
   - Replace with a constructive/parameterized route whose assumptions are
     already represented as data structures in `MainConjecture`.
   - This is likely the fastest way to remove the axiom from
     `MLC.mlc_conjecture` footprint.

2. **Secondary target (harder): prove an inverse-map existence theorem**
   - Replace axiom `external_ray_map_exists` in
     `Mlc/Quadratic/Complex/Bottcher/BottcherAxioms.lean` with a theorem.
   - Build from existing local inverse infrastructure:
     - `InverseBranchSlit.lean` / `InverseBranchSlitUse.lean`
     - outside-disk injectivity/local-homeomorph routes in
       `BottcherOnMTheory.lean` and `BottcherOutsidePlan.lean`
   - Upgrade local/eventual inverse data to a global exterior inverse with:
     - right inverse on `{w | 1 < ‖w‖}`
     - left inverse on sufficiently large `z`.

## Concrete Milestones
- [ ] **M1 (footprint):** isolate all `mlc_conjecture` references to
  `false_of_external_ray_axioms`; introduce an alternate closure path and re-run
  `make check`.
- [ ] **M2 (API hygiene):** split Böttcher helper lemmas into:
  - ones requiring explicit inverse data
  - ones independent of `external_ray_map_exists`
- [ ] **M3 (constructive inverse package):** define a replacement data target:
  - `ExternalRayMapData c : Prop`
  capturing the two properties currently returned by
  `external_ray_map_exists c`.
- [ ] **M4:** prove `external_ray_map_exists_of_data` and thread data through
  call sites.
- [ ] **M5:** either:
  - prove `ExternalRayMapData c` from existing inverse-branch machinery, or
  - keep it as an explicit parameter and ensure `mlc_conjecture` no longer
    depends on the axiom.
- [ ] **M6:** remove/replace the axiom declaration and update README output.

## Validation
- [ ] `make build`
- [ ] `make check`
- [ ] `scripts/verify_output.sh`
- [ ] Confirm `MLC.Quadratic.external_ray_map_exists` is absent from
  `check_axioms.lean` output for `MLC.mlc_conjecture`.

## Risks
- Existing contradiction-based top-level wiring may still import helper theorems
  that reference `external_ray_map_exists` in proof terms.
- Some inverse-branch routes in `InverseBranchSlitUse.lean` have formal
  obstruction lemmas; these may block a direct constructive proof in current
  model and require route redesign rather than theorem completion.
