# Supervisor Review 21: Quadratic-like tube bundle audit

**Verdict:** source/API audit accepted; proposed implementation rejected.

Result 21 correctly establishes that the source means a locally trivial fiber
bundle, not a globally trivial product, and that Mathlib's full `FiberBundle`
machinery is representation-mismatched with the current concrete subset of
`ℂ × ℂ`. It also correctly rejects a global trivialization as an unjustified
strengthening.

However, the proposed project-local structure is not an honest implementation:

```lean
fiber_is_jordan_disk : Prop
local_trivial : Prop
```

These fields hide the two missing mathematical definitions behind opaque generic
propositions. Task 21 explicitly required concrete fields where supported and
forbade this form of placeholder. Merely naming “local triviality” does not supply
charts, a model fiber, projection compatibility, or any theorem a future consumer
can use. The same objection applies to `fiber_is_jordan_disk`.

The separate `proj : total → Λ` is also largely redundant once total-space scoping
is known: the first coordinate canonically gives the parameter subtype. If retained
in an adapter, it needs a concrete reason beyond restating that projection.

The decision is changed from **(1)** to **(2): Mathlib bundle machinery needs a
preliminary adapter**, or equivalently a concrete project-local atlas modeled on
Mathlib's `Pretrivialization`. The next audit must compile a real local chart with:

- an open base neighborhood;
- a homeomorphism between the restricted concrete total space and the base
  neighborhood times a fixed disk model;
- exact source/target equalities;
- commutation with first-coordinate projection;
- a chart at every base point.

No `Prop` field whose body is merely a name such as `local_trivial` or
`fiber_is_jordan_disk` is acceptable.
