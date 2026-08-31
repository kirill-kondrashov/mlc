# Supervisor Review 22: Concrete tube local-trivialization adapter

**Verdict:** not accepted; the proposed chart does not encode local triviality.

Result 22 improves on opaque `Prop` fields by introducing map data, but several
essential conditions are still absent:

1. `toFun` and `invFun` have inverse laws but no continuity. They form an
   equivalence, not a homeomorphism.
2. `source : Set total` is arbitrary and is not required to equal the inverse image
   of `baseSet` under the tube projection.
3. `target : Set (baseSet × DiskType model)` is arbitrary and is not required to be
   the full product `baseSet × DiskType model`.
4. `openBase`, `open_base_eq`, and `baseSet` redundantly represent the same set,
   while `open_baseSet` is phrased as a preimage of a set already living in the
   subtype.
5. Consequently, chart coverage does not imply projection surjectivity or that an
   entire fiber is homeomorphic to the disk model.

A concrete local chart should instead contain a genuine `Homeomorph` of the exact
restricted total subtype:

```lean
{p : total // proj p ∈ baseSet} ≃ₜ (baseSet × DiskType model)
```

and a law that the first component of the homeomorphism equals `proj p`. The target
must be the full product by type, not a freely chosen subset. The source must be the
projection preimage by type, not a freely chosen set.

The fixed disk-model idea is acceptable, but the extra manually declared topology
instance should be checked carefully: subtype disk types already inherit topology,
and an unnecessary second instance risks conflicts.

Decision (2) remains appropriate, but the project-local chart layer needs one more
compile-tested correction before implementation.
