# TASK 66 — Assemble direct straddling proof and delete the axiom

## Gate

This task is executable only if the preceding stages proved all required
geometric lemmas without axioms or equivalent target assumptions.

## Work

Replace:

```lean
axiom green_sublevel_translate_inter_mandelbrot_connected_straddling
```

with the assembled theorem proof. Rebuild the para-puzzle connectivity route
and check the actual root dependency graph.

Run:

```bash
lake build
lake env lean check_axioms.lean
```

Confirm:

- no `sorryAx`;
- no new project axiom;
- the straddling axiom is absent from the root dependency graph;
- only the residual molecule axiom remains if that is still expected.

If the direct proof is incomplete, make no source edits and report the exact
stage and theorem where the sequence terminates.

Do not commit.

Write:

`plan/GPT54_RESULT_66_ASSEMBLE_DIRECT_STRADDLING_AND_DELETE_AXIOM.md`
