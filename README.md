# Machine-Generated Proof Skeleton of the MLC Conjecture

## 🚧 WORK IN PROGRESS 🚧

**Current Status:** This repository is in active development.

The original direction of this formalization focused heavily on the classical Yoccoz theorem for non-renormalizable parameters. While that remains a valid component, the project has pivoted to address the most challenging open cases of the MLC conjecture.

**The main target is now the formalization of the [Molecule Conjecture](https://arxiv.org/abs/1703.01206) (Dudko, Lyubich, Selinger).**

This conjecture is key to resolving the local connectivity for "satellite" infinitely renormalizable parameters, particularly those with unbounded combinatorics, which are not covered by Lyubich's prior theorems for primitive renormalization.

## Formalization Structure

The proof is structured around the dichotomy of renormalizability:

1.  **Finitely Renormalizable (Yoccoz's Theorem):**
    *   Parameters where the Yoccoz puzzle moduli diverge.
    *   We prove that the intersection of puzzle pieces is a point, implying local connectivity.
    *   Key files: `Mlc/Yoccoz.lean`, `Mlc/Quadratic/Complex/Puzzle.lean`.

2.  **Infinitely Renormalizable:**
    *   Parameters where the moduli sum converges.
    *   This case is further split into:
        *   **Primitive:** Handled by Lyubich's Theorem (axiom).
        *   **Satellite:** Handled by the **Molecule Conjecture** (axiom) and Pacman Renormalization.
    *   Key files: `Mlc/InfinitelyRenormalizable.lean`.

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

*   `MLC.molecule_conjecture_implies_mlc_satellite`
*   `MLC.mlc_primitive_renormalizable_ax`
*   `MLC.infinitely_renormalizable_classification`
*   `MLC.Quadratic.parameter_shrink_ax`
*   `MLC.Quadratic.slodkowski_theorem`

Output:
```
✅ The proof of 'MLC.MLC_Conjecture' is free of 'sorry'.
All axioms used:
- Quot.sound
- propext
- Classical.choice
- MLC.Quadratic.parameter_shrink_ax
- MLC.Quadratic.filled_julia_set_connected
- MLC.Quadratic.puzzle_boundary_motion_exists
- MLC.Quadratic.slodkowski_theorem
- MLC.Quadratic.mandelbrot_set_connected
- MLC.infinitely_renormalizable_classification
- MLC.mlc_primitive_renormalizable_ax
- MLC.molecule_conjecture_implies_mlc_satellite
```

## Documentation

*   [Read the Proof Overview (PDF)](docs/proof.pdf): *Note: This PDF is a work in progress and may lag behind the Lean code.*
