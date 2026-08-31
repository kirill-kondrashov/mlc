Begin the parameter-exterior foundation sequence:

`plan/GPT54_TASK_77_DEFINE_FULLNESS_AND_EXTERIOR_TARGETS.md`

Prompt 76 found that the repository lacks formal targets for fullness/simple
connectedness of `MandelbrotSetᶜ` and lacks a usable Riemann-map theorem.

First audit the existing topology APIs and fix the exact Lean formulations for:

- fullness of a compact plane set;
- compact connected continuum structure;
- connectedness of the complement;
- simple connectedness of an open plane domain;
- the unbounded-domain normalization needed for an exterior coordinate.

Determine whether the project already has definitions/lemmas that should be
reused. Do not introduce competing definitions unnecessarily.

Then select precise classical source statements for:

1. fullness of the Mandelbrot set;
2. full compact continuum ⇒ simply connected complement;
3. the unbounded uniformization theorem.

This is a specification/source task. Do not add opaque target-shaped axioms or
claim any theorem from the existing `mandelbrot_set_connected` axiom alone.
Do not edit source unless a small, non-duplicative definition/lemma is clearly
justified. No new axiom, `sorry`, or `admit`; do not commit.

Write:

`plan/GPT54_RESULT_77_DEFINE_FULLNESS_AND_EXTERIOR_TARGETS.md`
