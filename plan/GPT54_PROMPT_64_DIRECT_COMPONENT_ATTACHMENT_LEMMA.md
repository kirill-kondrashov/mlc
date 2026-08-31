Continue Stage 2 of the direct frozen-straddling sequence:

`plan/GPT54_TASK_64_DIRECT_COMPONENT_ATTACHMENT_LEMMA.md`

Use only facts proved in Stage 1 and existing checked mathematics. Do not use
the frontier axiom or any theorem whose conclusion is the target under another
name.

Study connected components of:

```lean
S c n ∩ MandelbrotSet
```

where:

```lean
S c n := {c' | green_function c (c' - c) < (1 / 2 : ℝ)^n}.
```

Attempt to prove a substantive specialized lemma showing that every component
of the intersection attaches to a common connected subset, or that a
separation of the intersection contradicts a proved boundary/continuum
property of the frozen Green translate and `MandelbrotSet`.

Possible outputs include:

- a component-attachment theorem;
- a no-separation theorem;
- a precise proof that the proposed attachment principle is false or
  unprovable from the available hypotheses.

Do not invoke generic intersection-connectedness, path connectedness of
Mandelbrot, or fullness unless these are actually proved in the repository and
apply to the exact sets.

Make only focused source edits for genuine lemmas. Otherwise write a hard-stop
report. Do not add axioms, `sorry`, `admit`, or speculative geometry.

Write:

`plan/GPT54_RESULT_64_DIRECT_COMPONENT_ATTACHMENT_LEMMA.md`
