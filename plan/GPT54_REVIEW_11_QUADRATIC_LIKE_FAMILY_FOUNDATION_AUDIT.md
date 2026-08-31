# Supervisor Review 11: Quadratic-like family foundation audit

**Verdict:** existing-type audit accepted; proposed implementation rejected as
mathematically misidentified.

Result 11 usefully establishes that `Molecule.BMol` can serve as a raw fiber type,
that its discrete topology cannot model holomorphic family dependence, and that
the repository has no intrinsic filled Julia set for a general `BMol`.  It also
correctly identifies `parameterToBMol` and the non-axiomatic theorem
`filled_julia_set_connected` for the normalized quadratic family.

The proposed declaration

```lean
def BMolFiberConnected (g : BMol) : Prop :=
  IsConnected (MLC.Quadratic.K (criticalValue g))
```

must not be implemented.  For an arbitrary quadratic-like map `g`, the set
`MLC.Quadratic.K (criticalValue g)` is the filled Julia set of the *different map*
`z ↦ z² + criticalValue g`.  Equality of a critical value does not identify the
dynamics, domains, filled Julia sets, or hybrid class of these maps.  Thus this
predicate is not even a narrow version of “the fiber of `g` is connected”; it is
an unrelated normalized-polynomial predicate with a misleading name.

The proposed consumer through `parameterToBMol` is tautologically recoverable
because that chosen fiber has global map `z²+c`, but it does not advance the
Lyubich family foundation.  Moreover, `parameterToBMol` uses `U = V = univ`, while
the current `QuadraticLikeMap.closure_subset` field records only `closure U ⊆ V`,
not genuine compact containment.  It therefore must not be presented as the
restricted quadratic-like family over a renormalization window.

The correct preliminary foundation is an intrinsic non-escaping set for
`QuadraticLikeMap`, defined from `g.U`, `g.f`, and iteration, for example the set
of points whose every forward iterate remains in `g.U`.  The exact convention
(including whether membership at time zero is explicit and whether `U` or the
domain of successive restricted iterates is used) must be checked against a
standard polynomial-like definition and against later renormalization relations.
Once fixed, `BMolFilledJuliaConnected g := IsConnected (filledJuliaSet g)` is an
honest definitional predicate.  No theorem that this set is connected is required
for the first milestone.

Accordingly Result 11's decision is changed from (1) to **(2): `BMol` needs one
preliminary filled-Julia/connected-fiber definition**.  Only after that definition
is reviewed should the parameter-family shell and connectedness locus be
implemented.
