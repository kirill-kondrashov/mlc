# Direct-proof sequence for the frozen straddling theorem

Target:

```lean
green_sublevel_translate_inter_mandelbrot_connected_straddling
```

The sequence is deliberately gated. Each stage must either prove a substantive
lemma or identify the exact obstruction; later stages must not assume an
unproved geometric principle.

1. `GPT54_PROMPT_63_DIRECT_STRADDLING_GEOMETRY_GATE.md`
   Normalize the frozen translated Green sublevel and prove all elementary
   geometric facts available without the frontier axiom.

2. `GPT54_PROMPT_64_DIRECT_COMPONENT_ATTACHMENT_LEMMA.md`
   Analyze components of the intersection and prove a genuine attachment or
   no-separation lemma; reject invalid generic “intersection of connected sets”
   arguments.

3. `GPT54_PROMPT_65_DIRECT_FROZEN_BOUNDARY_CROSSING_THEOREM.md`
   Prove the missing frozen boundary-crossing/no-separation statement from
   quadratic Green-function and Mandelbrot geometry, or give a precise
   impossibility/blocker report.

4. `GPT54_PROMPT_66_ASSEMBLE_DIRECT_STRADDLING_AND_DELETE_AXIOM.md`
   Assemble the exact theorem and remove the frontier axiom only if all prior
   lemmas are proved without equivalent assumptions.

This route may terminate before Stage 4 if the frozen statement has no valid
direct reduction.
