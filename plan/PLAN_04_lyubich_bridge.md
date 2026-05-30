# PLAN 04: Attack `MLC.lyubich_conformal_bridge`

**Status:** COMPLETE
**Frontier role:** root attack finished
**Primary files:** `Mlc/MainConjecture.lean`, `Mlc/Quadratic/Complex/Bottcher/BottcherAxioms.lean`, `README.md`, `check_axioms.lean`

---

## Root result of this plan

`MLC.lyubich_conformal_bridge` is no longer in `Axioms(MLC.mlc_conjecture)`.
The frontier has now been reduced all the way to a single project axiom:

1. `MLC.restrictedWindingKernelTwo`

This plan first removed the old hidden Lyubich/tower contradiction route, then
collapsed the wider explicit chosen-true / residual-open frontier, and finally
rerouted the root through the narrowed `c = 2` degree-one kernel.

---

## Final root route

`MLC.mlc_conjecture` now runs through:

1. `mlc_conjecture_of_finalAxiomCoreConstructiveGapV16`
2. `finalAxiomCoreConstructiveGapV16_of_restricted_winding`
3. `MLC.restrictedWindingKernelTwo`

---

## Meaning of the old bridge now

The old bridge is still present in `PrimitiveModulusDivergence.lean` and
`InconsistencyRoute.lean`, but it is no longer root-facing. It is now a
quarantined legacy route that can be deleted, deprecated, or further shrunk
without affecting the checked root frontier.

## Next plan surface

The remaining repo-facing target is no longer the Lyubich bridge. The next plan
should attack:

1. `MLC.restrictedWindingKernelTwo`

## Success criterion achieved

1. `MLC.lyubich_conformal_bridge` stays absent from `Axioms(MLC.mlc_conjecture)`.
2. the root frontier is reduced to one project axiom.
