# Supervisor Review 13: BMol filled Julia foundation implementation

**Verdict:** accepted.

The implementation matches the approved intrinsic definition:

- `filledJuliaSet g` checks every forward iterate of `g.f` against `g.U`;
- the membership and intersection-of-preimages lemmas are definitional/elementary;
- `FilledJuliaConnected` is only a predicate and asserts no theorem;
- `BMolParameterFamily` is explicitly minimal;
- `connectednessLocus` uses the intrinsic fiber predicate rather than the unrelated
  normalized polynomial at the critical value.

Independent verification passed:

```text
lake env lean Mlc/BMolFilledJulia.lean   exit 0
lake build                              exit 0, 7978 jobs
```

The full build emitted only pre-existing warnings in other modules. No
`axiom`, `sorry`, or `admit` was added by the new file.

One minor dependency issue is recorded but is not grounds for rejection:
`Mlc/BMolFilledJulia.lean` imports the broad `Mlc.RenormalizationTypes` although
the declarations appear to need only the underlying `Molecule.BMol` and topology
API. This should be tested and reduced in a later implementation pass so the new
foundation does not depend upward on unrelated parameter/tower placeholders.

The next architectural blocker is now precise. `BMol` stores only
`closure U ⊆ V`, not genuine relative compactness, and carries a deliberately
discrete placeholder topology. Therefore the minimal arbitrary family shell must
not yet be used as Lyubich's holomorphic proper unfolded equipped family. The next
audit should design a local, non-vendored refinement layer for genuine
quadratic-like fibers and explicit parameter dependence.
