# TASK 71 — Assemble the provider and reroute the root

## Gate

Run this task only after a complete genuine quadratic moving-window provider has
been proved.

## Work

Instantiate `FiniteMovingWindowProviderData`, route the actual root theorem
through the moving-window strategy, and remove:

```lean
green_sublevel_translate_inter_mandelbrot_connected_straddling
```

from the source and dependency graph only if it is genuinely unused.

Run:

```bash
lake build
lake env lean check_axioms.lean
```

Verify no hidden equivalent axiom or `sorryAx` replaced the frontier.

If the provider is incomplete, make no source edits and report the exact
blocking theorem.

## Result

Write:

`plan/GPT54_RESULT_71_ASSEMBLE_PROVIDER_AND_REROUTE_ROOT.md`
