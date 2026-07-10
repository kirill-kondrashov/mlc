# Supervisor Review 20: Analytic quadratic-like family core implementation

**Verdict:** accepted.

The new module implements exactly the approved analytic core:

- parameters and fibers are scoped correctly;
- total source and target spaces are open and have no off-domain components;
- total-space sections agree with the bundled `GenuineBMol` domains;
- the global evaluation representative agrees with each fiber on the source;
- joint analyticity is restricted to the actual total source;
- all derived sections and membership lemmas live outside the structure.

The name and documentation correctly state that this is not yet the complete
source-defined quadratic-like family because tube fiber-bundle/local-triviality
and all proper/unfolded/equipped layers are absent.

Independent verification passed:

```text
lake env lean Mlc/AnalyticQuadraticLikeFamilyCore.lean   exit 0
lake build                                              exit 0, 7980 jobs
```

Only pre-existing warnings appeared. No axioms or placeholders were introduced.
The next foundation question is the source's tube-as-fiber-bundle condition.
