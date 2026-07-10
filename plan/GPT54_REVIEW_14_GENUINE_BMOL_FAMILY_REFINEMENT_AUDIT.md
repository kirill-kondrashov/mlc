# Supervisor Review 14: Genuine BMol family refinement audit

**Verdict:** compact-containment refinement accepted for implementation; analytic
family skeleton requires correction before use.

Result 14 correctly identifies the missing fiber condition. The vendored field
`closure U ⊆ V` does not imply relative compactness in `ℂ`; adding
`IsCompact (closure U)` supplies the missing content. A local wrapper around
`BMol` is preferable to editing the vendored dependency and allows reuse of the
intrinsic `filledJuliaSet` API.

The implementation should use naming that exposes the complete mathematical
meaning. In particular, a predicate named `HasCompactClosureInV` should either
expand to both

```lean
IsCompact (closure g.U) ∧ closure g.U ⊆ g.V
```

or be renamed to say only that the source closure is compact. Although the second
conjunct is already available as `g.closure_subset`, keeping the complete
compact-containment predicate explicit avoids a misleading standalone API.

Two conclusions in the report must remain provisional:

1. The proposed `jointMap_analytic` condition on
   `parameterSet ×ˢ Set.univ` is generally too strong for a quadratic-like family.
   The stored global function is only a representation of a map on the varying
   source domain; its arbitrary extension outside that domain need not be analytic.
   A future family structure needs a total-space domain such as
   `{p : ℂ × ℂ | p.1 ∈ Λ ∧ p.2 ∈ U p.1}` and analyticity on an appropriate open
   version of that set.

2. A unique simple critical point is plausible degree-two data in the intended
   proper simply-connected setting, but the current repository has not exhibited
   the theorem identifying that encoding with topological degree two. It is enough
   to preserve the vendored fiber for this refinement; it must not yet be cited as
   a proved degree theorem.

The import audit is accepted: `Mlc/BMolFilledJulia.lean` can depend directly on
`Molecule.BMol` rather than `Mlc.RenormalizationTypes`.

Decision **(2)** is accepted. The next task is a narrow implementation of explicit
compact containment plus import cleanup. It must not add the analytic-family
skeleton from Result 14.
