# PLAN 04: Attack `MLC.lyubich_conformal_bridge`

**Status:** COMPLETE
**Frontier role:** root attack finished
**Primary files:** `Mlc/MainConjecture.lean`, `Mlc/Quadratic/Complex/Bottcher/BottcherAxioms.lean`, `README.md`, `check_axioms.lean`

---

## Root result of this plan

`MLC.lyubich_conformal_bridge` is no longer in `Axioms(MLC.mlc_conjecture)`.
The frontier has now been reduced all the way to a single project axiom:

1. `MLC.basinExternalRayKernelTwo`

This plan first removed the old hidden Lyubich/tower contradiction route, then
collapsed the wider explicit chosen-true / residual-open frontier, and finally
rerouted the root away from the false full-exterior degree package to the honest
`c = 2` basin-valued external-ray kernel.

---

## Final root route

`MLC.mlc_conjecture` now runs through:

1. `mlc_conjecture_of_basinExternalRayMapData_two`
2. `Quadratic.externalRayMapData_of_basinExternalRayMapData`
3. `MLC.basinExternalRayKernelTwo`

The monodromy / covering-degree route from Problem A remains formalized in
`Mlc.Bottcher.DegreeOne`, but it is no longer the live root because its former
Problem B input is false as stated. The checked root now ends at the codomain-
correct basin-valued inverse package for the actual `proxy_bottcher_map`.

---

## Meaning of the old bridge now

The old bridge is still present in `PrimitiveModulusDivergence.lean` and
`InconsistencyRoute.lean`, but it is no longer root-facing. It is now a
quarantined legacy route that can be deleted, deprecated, or further shrunk
without affecting the checked root frontier.

## Next plan surface

The remaining repo-facing target is no longer the Lyubich bridge and no longer
the old degree-one proxy route in isolation. The live next plan is now:

1. `PLAN_06_global_bottcher_package.md`

That plan attacks `MLC.basinExternalRayKernelTwo` through the theorem-facing
global Bottcher coordinate package. `PLAN_05_restricted_winding_degree_one.md`
remains only as a downstream auxiliary route once the genuine coordinate exists.

## Success criterion achieved

1. `MLC.lyubich_conformal_bridge` stays absent from `Axioms(MLC.mlc_conjecture)`.
2. the root frontier is reduced to one project axiom.
