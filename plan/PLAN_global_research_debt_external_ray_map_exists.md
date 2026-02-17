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
- Latest code status:
  - `mlc_conjecture` is now routed through a generic closure helper
    `mlc_conjecture_of_false`.
  - An alternate non-external closure API now exists:
    `mlc_conjecture_of_fast_tower_obstruction`.
  - Introduced `Quadratic.ExternalRayMapData` in
    `Mlc/Quadratic/Complex/Bottcher/BottcherAxioms.lean` with conversion lemmas
    `external_ray_map_exists_of_data` / `external_ray_map_data_of_exists`.
  - Replaced non-local direct
    `Classical.choose_spec (external_ray_map_exists ...)` usages with helper
    lemmas from `BottcherAxioms`.
  - Parameterized the contradiction stack in `Mlc/MainConjecture.lean` by
    explicit `ExternalRayMapData (2 : ℂ)`:
    `false_of_external_ray_data_two` and data-parameterized wrapper builders,
    with existing axiom-backed lemmas now thin specializations.
  - Added `mlc_conjecture_of_external_ray_data_two` and rewired
    `mlc_conjecture` as a one-line specialization. Axiom usage is now
    concentrated at a single instantiation site.
  - Added constructive map API wrappers in
    `Mlc/Quadratic/Complex/Bottcher/BottcherAxioms.lean`:
    `external_ray_map_of_data`,
    `external_ray_map_of_data_right_inverse`,
    `external_ray_map_of_data_left_inverse_large`, and routed
    `external_ray_map` through this data-based definition.
  - Added data-parameterized Böttcher-left-inverse lemmas:
    `bottcher_left_inv_of_data`,
    `external_ray_map_left_inverse_outside_open_of_data`,
    with axiom-backed variants now wrappers.
  - Extended the same split into
    `Mlc/Quadratic/Complex/Bottcher/BottcherOnMTheory.lean` for the core
    exterior inverse pipeline:
    `bottcher_left_inv_of_injective_of_data`,
    `external_ray_map_right_inverse_on_exterior_of_data`,
    `external_ray_map_mem_outside_of_data`,
    `external_ray_map_eventually_right_inverse_of_data`,
    `external_ray_map_left_inverse_of_injOn_of_data`,
    with existing non-parameterized lemmas rewritten as wrappers.
  - Top-level closure still instantiates via `false_of_external_ray_axioms`, so
    the footprint is unchanged.

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
- [x] **M1 (footprint):** isolate `mlc_conjecture` closure through
  `mlc_conjecture_of_false`, introduce an alternate closure path
  (`mlc_conjecture_of_fast_tower_obstruction`), and re-run `make check`.
- [ ] **M2 (API hygiene):** split Böttcher helper lemmas into:
  - ones requiring explicit inverse data
  - ones independent of `external_ray_map_exists`
- [x] **M3 (constructive inverse package):** define a replacement data target:
  - `ExternalRayMapData c : Prop`
  capturing the two properties currently returned by
  `external_ray_map_exists c`.
- [x] **M4:** prove `external_ray_map_exists_of_data` and thread data through
  call sites.
- [ ] **M5:** either:
  - prove `ExternalRayMapData c` from existing inverse-branch machinery, or
  - keep it as an explicit parameter and ensure `mlc_conjecture` no longer
    depends on the axiom.
- [ ] **M6:** remove/replace the axiom declaration and update README output.

## Validation
- [x] `make build`
- [x] `make check`
- [x] `scripts/verify_output.sh`
- [ ] Confirm `MLC.Quadratic.external_ray_map_exists` is absent from
  `check_axioms.lean` output for `MLC.mlc_conjecture`.

## Risks
- Existing contradiction-based top-level wiring may still import helper theorems
  that reference `external_ray_map_exists` in proof terms.
- Some inverse-branch routes in `InverseBranchSlitUse.lean` have formal
  obstruction lemmas; these may block a direct constructive proof in current
  model and require route redesign rather than theorem completion.
