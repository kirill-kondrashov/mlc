# Machine-Generated Proof Skeleton of the MLC Conjecture

[![build](https://github.com/kirill-kondrashov/mlc/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/kirill-kondrashov/mlc/actions/workflows/lean_action_ci.yml)

## 🚧 WORK IN PROGRESS 🚧

## Current Status

This repository is a proof skeleton. It compiles and isolates the main logical
dependencies, but several deep inputs remain axiomatic.

Active research-debt tracking for the Böttcher inverse-branch route:
`plan/PLAN_global_research_debt_bottcher_inverse.md`.

For the Molecule Conjecture track, the project re-exports the refined conjecture
statement from an external `Molecule` package located at
`./.lake/packages/molecule-conjecture`. The file
`Mlc/MoleculeConjectureBridge.lean` then assumes a bridge axiom that turns this
refined conjecture into MLC for satellite infinitely renormalizable parameters
(as referenced in the literature).

The external package is `molecule-conjecture` (vendored via Lake). It is a
substantial formal scaffold, but it is not yet a complete proof. In particular:

- The top-level statement `Molecule.molecule_conjecture_refined` is conditional,
  with large analytic/dynamical hypotheses left as explicit parameters.
- The Banach slice model is still stubbed (e.g. `SliceSpace` is instantiated as `ℂ`,
  and `slice_chart` / `slice_operator` are placeholder constant maps).
- The renormalization operator `Rfast` is totalized with `Classical.choose`, so
  existence is assumed rather than constructed.
- Key analytic ingredients (a priori bounds, spectral gap, orbit control, etc.)
  are not yet derived inside Lean; they remain hypotheses.

So while the package provides a rigorous dependency graph, it should be read as
“formalized assumptions + logical pipeline” rather than a finished proof.

For the finitely renormalizable case, the current proof skeleton assumes
parameter-piece shrinkage as an explicit hypothesis and also takes a holomorphic
motion hypothesis derived from two inputs: a parameter-disk inclusion in `M`
(`BottcherOnMHyp`) and connectedness of Green sublevels on `M`
(`GreenSublevelConnectedHyp`). For the infinitely renormalizable case,
the current route assumes existence of a satellite-style renormalization tower
as an explicit bridge axiom and derives the Primitive/Satellite wrapper from
that route.
The primitive case is derived from modulus divergence in the principal nest, 
using a conformal proxy definition to satisfy Lyubich's a priori bounds.

## Formalization Origins

The core definitions and the top-level statement of the MLC conjecture in this project are based on the [Google DeepMind formal-conjectures](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Wikipedia/Mandelbrot.lean) repository. These definitions have been manually aligned and integrated into our framework because direct dependency integration was not possible. This is due to version incompatibilities: the DeepMind repository relies on an older version of Lean 4 and Mathlib (v4.22.0), whereas this project is built on more recent releases.

## Formalization Structure

The proof is structured around the dichotomy of renormalizability:

1.  **Finitely Renormalizable (Yoccoz's Theorem):**
    *   Parameters where the Yoccoz puzzle moduli diverge.
    *   We assume the parameter-piece shrinkage needed to apply the local-connectivity criterion.
    *   Key files: `Mlc/MainConjecture.lean`, `Mlc/Quadratic/Complex/Puzzle.lean`.

2.  **Infinitely Renormalizable:**
    *   Parameters where the moduli sum converges.
    *   This case is further split into:
        *   **Primitive:** Derived from modulus divergence in the principal nest (Lyubich).
        *   **Satellite:** Uses the **Molecule Conjecture** (re-exported) plus a bridge axiom;
            the current formalization is conditional and still assumes major analytic inputs,
            with the intended proof path going via Pacman renormalization.
    *   Key files: `Mlc/InfinitelyRenormalizable.lean`, `Mlc/PrimitiveModulusDivergence.lean`,
        `Mlc/FastTowerExistence.lean`, `Mlc/MoleculeConjectureBridge.lean`.
    *   Reference for the primitive MLC axiom: Lyubich, "Conformal Geometry and Dynamics of
        Quadratic Polynomials", §42.6 "MLC on the main cardioid".

## Verification

To verify the build and check the axioms used in the current proof skeleton:

```bash
make check
```

This will compile the main conjecture file and output the list of axioms relied upon.

## Dependencies

*   [Lean 4](https://leanprover.github.io/)
*   [Mathlib 4](https://github.com/leanprover-community/mathlib4)

## Disclaimer

> **This is an AI-assisted attempt to formalize modern mathematics.**
>
> The code in this repository was produced by a combination of AI assistance and manual formalization. While definitions and logic are checked by the Lean 4 kernel, the choice of axioms and the fidelity to the mathematical literature (especially regarding deep theorems like the Molecule Conjecture) requires expert human verification.

## Axioms Used

Run `make check` to see the authoritative list. As of the latest check, the
axioms used are listed below.

Output:
```
✅ The proof of 'MLC.mlc_conjecture' is free of 'sorry'.
All axioms used:
- Quot.sound
- propext
- Classical.choice
- MLC.Quadratic.bottcher_seq_converges
- MLC.Quadratic.external_ray_map_exists
- MLC.Quadratic.para_puzzle_piece_inter_mandelbrot_connected
- MLC.Quadratic.filled_julia_set_connected
- MLC.Quadratic.extended_ray_map_continuous
```
