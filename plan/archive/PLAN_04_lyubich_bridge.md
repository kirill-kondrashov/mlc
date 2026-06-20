# PLAN 04: Attack `MLC.lyubich_conformal_bridge`

**Status:** COMPLETE
**Frontier role:** root attack finished
**Primary files:** `Mlc/MainConjecture.lean`, `Mlc/Quadratic/Complex/Bottcher/BottcherAxioms.lean`, `README.md`, `check_axioms.lean`

---

## Root result of this plan

`MLC.lyubich_conformal_bridge` is no longer in `Axioms(MLC.mlc_conjecture)`.
This plan successfully removed the old bridge from the checked root, but the
root frontier did **not** collapse to a single project axiom. The checked root
now has two non-core axioms:

1. `MLC.residualOpenVirtualNearMoleculeAxiom`
2. `MLC.unifiedGenuineRootKernelTwo`

This plan first removed the old hidden Lyubich/tower contradiction route, then
collapsed the wider explicit chosen-true / residual-open frontier as far as the
current formal reductions allow, and finally rerouted the root away from the
false full-exterior degree package to the honest `c = 2` genuine-route kernel.

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

## Residual audit: why the bridge is not an immediate remaining reduction

There is no honest immediate Lean reduction of
`MLC.residualOpenVirtualNearMoleculeAxiom` through
`MLC.lyubich_conformal_bridge`.

What remains is exactly the renormalization-theory seam packaging Dudko Problem
4.3 and Problem 4.4. The current repo already shows that the Gaussian proxy
framework is hostile to a genuine Track-2 proof: the proxy conformal-modulus
target is formally false in `Mlc/MoleculeGroetzschConnection.lean`. One can
swap the Track-2 burden to the separate axiom `MLC.lyubich_conformal_bridge`,
making the satellite-tower branch vacuous, but that only changes the shape of
the frontier:

1. Track-2 can be discharged only by adding `MLC.lyubich_conformal_bridge` back
   into the proof chain.
2. Track-1 still requires the Virtual Molecule near-degenerate regime and is
   not vacuous.
3. So the checked root would still retain a genuine open non-core axiom.

Therefore the live theorem-proving work splits into two independent axes:

1. `PLAN_06_global_bottcher_package.md` / PLAN 08 / PLAN 09 for
   `MLC.unifiedGenuineRootKernelTwo`;
2. an external renormalization-theory barrier at
   `MLC.residualOpenVirtualNearMoleculeAxiom`, not attacked by the frontier
   notebook.

## Success criterion achieved

1. `MLC.lyubich_conformal_bridge` stays absent from `Axioms(MLC.mlc_conjecture)`.
2. the checked root is honestly documented as still depending on
   `MLC.residualOpenVirtualNearMoleculeAxiom` and
   `MLC.unifiedGenuineRootKernelTwo`.
