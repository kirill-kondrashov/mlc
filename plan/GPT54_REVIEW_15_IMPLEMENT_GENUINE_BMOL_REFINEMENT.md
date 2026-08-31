# Supervisor Review 15: Genuine BMol refinement implementation

**Verdict:** focused compilation passes, but the implementation is not accepted;
one required semantic correction is necessary.

The import cleanup is correct: `Mlc/BMolFilledJulia.lean` now depends directly on
`Molecule.BMol`, and its declarations are unchanged. The new module also compiles
successfully under an independent focused check.

However, the central declaration does not implement Task 15's required public
compact-containment predicate. The worker wrote:

```lean
abbrev HasCompactClosureInV (g : BMol) : Prop :=
  IsCompact (closure g.U)
```

The name `...InV` and its docstring claim compact containment in `V`, but the
definition never mentions `g.V` and does not state `closure g.U ⊆ g.V`. Task 15
explicitly required the public predicate to expand to both compactness and closure
inclusion, even though the latter proof is already stored on every `BMol`.

This must be corrected to an explicit conjunction, preferably through a reusable
set-level predicate such as:

```lean
def IsCompactlyContained (U V : Set ℂ) : Prop :=
  IsCompact (closure U) ∧ closure U ⊆ V
```

with `GenuineBMol` storing that predicate for `toBMol.U` and `toBMol.V`.
Collision checks may require a project-specific name.

The three current simp lemmas are definitional restatements. They are harmless but
do not demonstrate the missing compact-containment API. The corrected module
should instead expose useful projection lemmas for compactness and closure
inclusion; filled-Julia reuse already follows from the coercion and does not need
multiple tautological lemmas.

No analytic-family machinery should be added during the correction.
