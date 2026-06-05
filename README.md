# Mandelbrot Local Connectivity (MLC) in Lean 4

[![build](https://github.com/kirill-kondrashov/mlc/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/kirill-kondrashov/mlc/actions/workflows/lean_action_ci.yml)

[Live dependency graph](https://kirill-kondrashov.github.io/mlc/mlc_conjecture/) *(GitHub Pages deploys from `main`; the checked-in `site/` directory reflects the current branch state.)*

A Lean 4 formalization of the Mandelbrot local connectivity statement
`MLC.mlc_conjecture`.

## Quick Start

```bash
make build
make check
```

Expected `make check` output:

```text
✅ The proof of 'MLC.mlc_conjecture' is free of 'sorry'.
All axioms used:
- Quot.sound
- propext
- Classical.choice
- MLC.basinExternalRayKernelTwo
```

## Current Frontier

```text
Axioms(MLC.mlc_conjecture)
= {Quot.sound, propext, Classical.choice,
   MLC.basinExternalRayKernelTwo}

project_frontier(MLC.mlc_conjecture)
= {MLC.basinExternalRayKernelTwo}
```

## Current Status

The checked root is now routed through a **single honest basin-valued kernel**:
a theorem-shaped minimal-counterexample wrapper for the specialized statement
`Quadratic.BasinExternalRayMapDataTwo`. This package asks for a right inverse to
the fixed `bottcher_map (2)` on the full exterior `Ω = {w : |w| > 1}` and a
left inverse on the outside-open source region `V = {z : |z| > 4}`.

The former full-exterior degree route is no longer root-facing. The monodromy
Problem A package remains formalized as an auxiliary route in
`Mlc.Bottcher.DegreeOne`, but the old Problem B package has now been formally
refuted in Lean.

The expert-facing documentation has been cleaned up accordingly:

1. `draft/genuine_bottcher_coordinate_problem.md` states the first honest
   remaining positive target: replace the current proxy by a genuine holomorphic
   Böttcher coordinate at `c = 2`.
2. `draft/genuine_bottcher_inverse_problem.md` states the matching exterior
   inverse package for that genuine coordinate.
3. `proof_sketches/` now mirrors `draft/`: it contains one rigorous
   human-readable proof for each current remaining positive target.

So the earlier explicit frontier

1. para-puzzle connectedness,
2. residual virtual near-Molecule data,
3. chosen-true primitive bridge data,
4. bounded-type primitive Feigenbaum inputs,

has been pushed off the checked root. Those routes still exist in the repo, but
they are no longer part of `Axioms(MLC.mlc_conjecture)`.

## Remaining Blocker

One non-core project axiom remains:

1. `MLC.basinExternalRayKernelTwo`

It is the theorem-shaped scope interface
`BasinExternalRayMapDataTwoMinimalCounterexample`, whose positive content is the
specialized basin-valued inverse package `Quadratic.BasinExternalRayMapDataTwo`.

So there is only **one** root-facing missing theorem in the checked proof.
However, the current constructive coordinate

$$
\phi(z)=
\begin{cases}
\dfrac{z}{|z|}\,e^{G(z)}, & z\neq 0,\\
e^{G(0)}, & z=0
\end{cases}
$$

does **not** satisfy the old expert-facing inverse targets. The current `draft/`
folder therefore records the corrected positive targets that remain after those
proxy-based routes were formally ruled out.

## Non-solutions

The repository still rejects reroutes that revive older project axioms, notably
through:

1. `ir_locally_connected_seam`
2. `InconsistencyRoute` / `lyubich_conformal_bridge`
3. renormalization-tower existence bridge axioms

## Remaining Mathematical Targets

The old proxy-based routes are now formally eliminated. The exact remaining
positive targets are:

1. `draft/genuine_bottcher_coordinate_problem.md`
2. `draft/genuine_bottcher_inverse_problem.md`

In particular, the last axiom can no longer be eliminated by proving the
already-refuted basin-valued inverse theorem for the current proxy

$$
\phi(z)=\frac{z}{|z|}e^{G(z)}
$$

away from $$z=0$$. The positive human-readable proofs of the corrected
replacement package are now written in `proof_sketches/`; the remaining checked
work is to internalize that package in Lean.

This basin-valued target is the codomain-correct replacement for the false
statement that the restricted map `φ|_V : V → Ω` should already have positive
constant fiber degree over all of `Ω`.

The false degree package is now explicitly ruled out by
`Mlc.Bottcher.DegreeOne.not_restrictedLocalHomeomorphPositiveConstantDegreeTwo`
and by
`MLC.not_restrictedLocalHomeomorphPositiveConstantDegreeTwoMinimalCounterexample`.
The earlier closed-preimage, compact-preimage, and direct proper/local witness
routes remain formally refuted as well.

## Repository Snapshot

1. `make build`, `make check`, and `./scripts/verify_output.sh` pass.
2. `plan/` now records the live theorem-facing Bottcher plan in
   `PLAN_06_global_bottcher_package.md`, alongside completed or auxiliary
   historical plans.
3. `draft/` now records the exact remaining positive mathematical targets after
   factoring out the proxy-based obstructions.
4. `proof_sketches/` records the rigorous human-readable proofs of the current
   `draft/` targets.
5. The current root-facing story is therefore honest: one residual
   theorem-facing assumption remains, and its elimination now clearly requires a
   genuine Böttcher coordinate package rather than the current proxy.

## Dependencies

- [mathlib4](https://github.com/leanprover-community/mathlib4)
- [yoccoz-theorem](https://github.com/kirill-kondrashov/yoccoz-theorem)
- [molecule-conjecture](https://github.com/kirill-kondrashov/molecule-conjecture)

Lean toolchain: `leanprover/lean4:v4.27.0-rc1`
