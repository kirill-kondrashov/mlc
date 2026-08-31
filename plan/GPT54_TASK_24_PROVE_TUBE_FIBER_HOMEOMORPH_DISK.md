# GPT-5.4 Worker Task 24: Prove a tube chart fiber is homeomorphic to its disk model

**Repository:** `/home/kir/pers/mlc`
**Mode:** read-only focused Lean proof audit
**Result file:** `plan/GPT54_RESULT_24_PROVE_TUBE_FIBER_HOMEOMORPH_DISK.md`

## Safety

Write only the result report, via atomic rename. Do not edit repository sources,
dependencies, plans, or prior artifacts; do not commit. Use `/tmp` for Lean tests.

Read Result 23 and Supervisor Review 23.

## Goal

Complete and compile the missing topology proof that a corrected concrete tube
chart identifies each fiber over a point in its base set with the fixed disk model.
This proof will unblock implementation of the full concrete tube module.

## A. Product slice homeomorphism

For `baseSet : Set Λ`, `c : Λ`, `hc : c ∈ baseSet`, and a topological type `F`,
construct and compile:

```lean
{y : baseSet × F // ((y.1 : baseSet) : Λ) = c} ≃ₜ F
```

Give explicit forward/inverse maps, inverse proofs, and continuity proofs, or reuse
an exact Mathlib combinator after reporting its signature. The inverse sends
`x : F` to `⟨(⟨c, hc⟩, x), rfl⟩` up to subtype equality.

Make the lemma generic in `F` if that reduces duplication and compiles cleanly.

## B. Restrict the chart homeomorphism

Given:

```lean
chart.homeomorph : TubeSource hscope chart.baseSet ≃ₜ
  (chart.baseSet × DiskType model)
```

and `chart.proj_fst`, construct a homeomorphism between:

```lean
{p : total // tubeProj hscope p = c}
```

and the corresponding product slice. Carefully bridge the fact that the chart
homeomorphism's source additionally contains the proof that the projection lies in
`chart.baseSet`, using `hc`.

Compile the complete composition:

```lean
noncomputable def fiberHomeomorphDisk
    (chart : ConcreteTubeChart hscope model)
    (c : Λ) (hc : c ∈ chart.baseSet) :
    {p : total // tubeProj hscope p = c} ≃ₜ DiskType model
```

Do not replace continuity with a bare equivalence.

## C. Atlas-facing theorem

Using `chartAt c` and `mem_baseSet_chartAt c`, compile a convenient atlas-level
definition/theorem giving:

```lean
{p : total // tubeProj hscope p = c} ≃ₜ DiskType model
```

for every `c : Λ`.

## D. Integration rehearsal

Compile all accepted Result 23 declarations plus these new homeomorphisms together
in one temporary file. Check disk topology instances for ambiguity. Run the Lean
file twice if necessary after removing redundant imports/instances to identify the
smallest stable form.

## E. Decision

Choose exactly one:

1. the complete concrete tube module is ready for implementation;
2. the product slice works but restricting the chart needs one named Mathlib lemma;
3. the chart representation must change;
4. defer tube formalization.

Give the exact next worker task but do not create its file.

## Report contract

Include complete compiled code, imports, commands, outcomes, full
`git status --short`, and confirmation that only the result artifact was written
and no commit was made.
