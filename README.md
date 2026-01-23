# Machine-Generated Proof Skeleton of the MLC Conjecture

## 🚧 WORK IN PROGRESS 🚧

## Current Status

This repository is a proof skeleton. It compiles and isolates the main logical
dependencies, but several deep inputs remain axiomatic.

For the Molecule Conjecture track, `Mlc/MoleculeConjecture.lean` currently
re-exports the refined conjecture statement from an external `Molecule` package
located at `./.lake/packages/molecule-conjecture`. The file
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
parameter-piece shrinkage as an explicit hypothesis.

## Formalization Structure

The proof is structured around the dichotomy of renormalizability:

1.  **Finitely Renormalizable (Yoccoz's Theorem):**
    *   Parameters where the Yoccoz puzzle moduli diverge.
    *   We assume the parameter-piece shrinkage needed to apply the local-connectivity criterion.
    *   Key files: `Mlc/Yoccoz.lean`, `Mlc/Quadratic/Complex/Puzzle.lean`.

2.  **Infinitely Renormalizable:**
    *   Parameters where the moduli sum converges.
    *   This case is further split into:
        *   **Primitive:** Handled by Lyubich's Theorem (axiom).
        *   **Satellite:** Uses the **Molecule Conjecture** (re-exported) plus a bridge axiom;
            the current formalization is conditional and still assumes major analytic inputs,
            with the intended proof path going via Pacman renormalization.
    *   Key files: `Mlc/InfinitelyRenormalizable.lean`, `Mlc/MoleculeConjecture.lean`,
        `Mlc/MoleculeConjectureBridge.lean`.
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

Run `make check` to see the authoritative list. Key axioms include:

*   `MLC.mlc_primitive_renormalizable_ax`
*   `MLC.infinitely_renormalizable_classification`
*   `MLC.Quadratic.slodkowski_theorem`

Reference note:
*   `MLC.mlc_primitive_renormalizable_ax`: Lyubich, "Conformal Geometry and Dynamics of
    Quadratic Polynomials", §42.6 "MLC on the main cardioid".

Status note:
*   The Molecule Conjecture currently appears as an imported statement and a bridge
    hypothesis; it is not listed as an axiom by `make check`.

Output:
```
✅ The proof of 'MLC.MLC_Conjecture' is free of 'sorry'.
All axioms used:
- propext
- Quot.sound
- Classical.choice
- MLC.Quadratic.filled_julia_set_connected
- MLC.Quadratic.puzzle_boundary_motion_exists
- MLC.Quadratic.slodkowski_theorem
- MLC.Quadratic.mandelbrot_set_connected
- MLC.infinitely_renormalizable_classification
- MLC.mlc_primitive_renormalizable_ax
```
