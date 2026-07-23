Run the final Stage 4 gate of the direct frozen-straddling sequence:

`plan/GPT54_TASK_66_ASSEMBLE_DIRECT_STRADDLING_AND_DELETE_AXIOM.md`

Only proceed if Stages 1–3 produced a complete proof with no equivalent
assumptions. Assemble the exact theorem:

```lean
green_sublevel_translate_inter_mandelbrot_connected_straddling
```

Then:

1. replace the axiom by the proved theorem;
2. rebuild `ParaPuzzleConnectivity`;
3. run the project axiom check;
4. verify that the straddling frontier axiom is absent and that no hidden
   replacement axiom or `sorryAx` was introduced.

If any prior stage ended in a hard stop, do not fake assembly. Report that the
direct sequence terminates at the first missing theorem and leave the axiom
unchanged.

Write:

`plan/GPT54_RESULT_66_ASSEMBLE_DIRECT_STRADDLING_AND_DELETE_AXIOM.md`
