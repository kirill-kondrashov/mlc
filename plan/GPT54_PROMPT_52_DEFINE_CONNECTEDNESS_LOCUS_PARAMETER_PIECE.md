Complete the active-frontier task in
`plan/GPT54_TASK_52_DEFINE_CONNECTEDNESS_LOCUS_PARAMETER_PIECE.md`.

Result 51 successfully generalized the local-connectivity consumer to
`ParameterPieceLcAtData`, independent of the frozen `ParaPuzzlePieceAt`.

Now define the first honest moving-parameter piece object using the existing
quadratic-like connectedness-locus foundation:

```lean
Molecule.BMolParameterFamily
Molecule.BMolParameterFamily.connectednessLocus
Molecule.filledJuliaSet
Molecule.FilledJuliaConnected
```

Audit the current `AnalyticQuadraticLikeFamilyCore`/`GenuineBMol` files and local
references. Implement a focused Lean-facing definition for a finite-level
connectedness-locus-backed parameter piece, with explicit parameter domain and
family data. The piece must be defined from the moving family’s connectedness
locus, not from `green_function c (c' - c)`, an exact image, or an
`IsConnected` witness.

At minimum, land:

1. a definition of the connectedness-locus piece for a supplied
   `BMolParameterFamily` (or a depth-indexed family of them);
2. membership/unfolding lemmas;
3. an adapter statement identifying the hypotheses still needed to feed
   `ParameterPieceLcAtData`.

Do not assert the deep sourced theorem that the locus is connected/full unless
the repository already contains a checked provider. Do not fabricate a proper
unfolded equipped family from the incomplete analytic core. If no concrete
family instance can be constructed honestly, leave sources unchanged and report
the exact missing family-level foundation and the smallest next task.

Write the worker report to:

`plan/GPT54_RESULT_52_DEFINE_CONNECTEDNESS_LOCUS_PARAMETER_PIECE.md`

Do not resume the Böttcher mesh/monodromy sequence. Do not add `sorry`, `admit`,
or new axioms, do not edit unrelated files, and do not commit.
