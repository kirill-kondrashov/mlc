# TASK 79 — Prove Mandelbrot fullness

## Goal

Supply the Mandelbrot-specific fullness theorem needed for the generic
full-compact complement bridge.

## Work

Use existing definitions and proved escape estimates to determine whether the
parameter exterior is connected/full. If a classical theorem is required,
state it exactly and assess whether the current formalization contains its
prerequisites.

Do not invoke external-coordinate or ray-map axioms to prove fullness; that
would be circular with the next uniformization stage.

## Constraints

- no frozen straddling axiom;
- no `external_ray_map_exists`;
- no new axiom, `sorry`, or `admit`;
- no speculative path-connectedness claim;
- do not commit.

## Result

Write:

`plan/GPT54_RESULT_79_PROVE_MANDELBROT_FULLNESS.md`
