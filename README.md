# Machine-Generated Proof Skeleton of the MLC Conjecture

This repository contains a **machine-generated formal proof skeleton** of the Mandelbrot Local Connectivity (MLC) Conjecture in Lean 4.

Essentially, this is software that can help with moving forward with an exact proof **together** with human verification (if it allows formalizing with Lean).

This is a work in progress; there will be an update when (or if ☺ ) the proof is fully verified. This repository is shared at an early stage to simplify collaboration (not everyone has a github account).

The benefit of using Lean is that it is verified by the Lean kernel, even when it is generated. Some essential parts, such as definitions, useful lemmas, and theorems from the references, are included here. To have a closed loop, a few theorems (see below) are stated as axioms.

## Disclaimer

> **This is an AI-assisted attempt to formalize modern mathematics.**
>
> The code and documentation in this repository were produced by a combination of actions of AI assistant and manual fixes. While the definitions and logical structure are checked by the Lean 4 kernel, the choice of axioms and the mathematical fidelity of the formalization to the standard literature should be verified by human experts. This project is inspired by [recent work on AI for math](https://arxiv.org/abs/2511.02864).

## Axioms

Some of the statements used in the proof are stated as `axiom`s (keyword in Lean). They include:

### 1. Yoccoz Puzzles & Geometry
*   [`groetzsch_inequality_axiom`](Mlc/Quadratic/Complex/Basic.lean#L81): Grötzsch's Inequality (Superadditivity of modulus).
    *   Source: [Milnor, Dynamics in One Complex Variable, Corollary B.5] (Local: `refs/9201272v1.pdf`)
    *   Note: This axiom is used to prove `modulus_summable_of_nontrivial_intersection`, which states that if the intersection of nested pieces is non-trivial, the sum of moduli converges.
*   **Basic Properties**:
    *   [`modulus_nonneg`](Mlc/Quadratic/Complex/Basic.lean#L77): Modulus is non-negative.
        *   Source: [Milnor, Dynamics in One Complex Variable] (Local: `refs/9201272v1.pdf`, Appendix B)
    *   [`modulus_empty`](Mlc/Quadratic/Complex/Basic.lean#L74): Modulus of empty set is 0.
*   **Connectivity**: [`mandelbrot_set_connected`](Mlc/Quadratic/Complex/Basic.lean#L59) (Mandelbrot set is connected) and [`filled_julia_set_connected`](Mlc/Quadratic/Complex/Basic.lean#L63) (Filled Julia set is connected for $c \in M$).
    *   Source: [Douady and Hubbard, Etude dynamique des polynômes complexes, 1984]

### 2. Deep Theorems
*   [`infinitely_renormalizable_classification`](Mlc/InfinitelyRenormalizable.lean): Classification of infinitely renormalizable parameters into Primitive and Satellite types.
    *   Source: [Dudko, Lyubich, Selinger, arXiv:1703.01206v3]
*   [`mlc_primitive_renormalizable_ax`](Mlc/InfinitelyRenormalizable.lean): Lyubich's Theorem stating that MLC holds for Primitive infinitely renormalizable parameters.
    *   Source: [Lyubich, The Dynamics of Quadratic Polynomials I-II, Acta Math. 178 (1997)]
*   [`molecule_conjecture_implies_mlc_satellite`](Mlc/InfinitelyRenormalizable.lean): The Molecule Conjecture implies MLC for Satellite infinitely renormalizable parameters.
    *   Source: [Dudko, Lyubich, Selinger, arXiv:1703.01206v3, Appendix C]
*   [`slodkowski_theorem`](Mlc/Quadratic/Complex/PuzzleLemmas2.lean#L145) (Slodkowski's Theorem).
    *   Source: [Slodkowski, Holomorphic motions and polynomial hulls] <https://www.ams.org/journals/proc/1991-111-02/S0002-9939-1991-1037218-8/>
    *   Local: `refs/S0002-9939-1991-1037218-8.pdf`
    *   Note: This theorem implies that parameter puzzle pieces are open ([`para_puzzle_piece_open`](Mlc/Quadratic/Complex/PuzzleLemmas2.lean#L188)).
*   [`puzzle_boundary_motion_exists`](Mlc/Quadratic/Complex/PuzzleLemmas2.lean#L164): Axiom stating that the boundary of puzzle pieces moves holomorphically.
    *   Note: This bridges the geometric properties of quadratic polynomials with the Slodkowski theorem.

## Future Directions

The following axioms are identified as targets for future formalization. Replacing these with formal proofs would make the result fully self-contained:

*   `MLC.Quadratic.groetzsch_inequality_axiom`
*   `MLC.Quadratic.modulus_nonneg`
*   `MLC.Quadratic.puzzle_boundary_motion_exists`
*   `MLC.Quadratic.slodkowski_theorem`
*   `MLC.mlc_primitive_renormalizable_ax`
*   `MLC.molecule_conjecture_implies_mlc_satellite`

## Verification

To verify the proof and check for axioms (`sorry` keyword in Lean), run:

```bash
make check
```

This will output any axioms used in the proof. The goal is to reduce the axioms to only standard mathematical ones (and the ones explicitly stated for deep theorems).

Output:
```
✅ The proof of 'MLC.MLC_Conjecture' is free of 'sorry'.
All axioms used:
- Quot.sound
- propext
- Classical.choice
- MLC.Quadratic.modulus_mono_axiom
- MLC.Quadratic.modulus_empty
- MLC.essential_induction_step_A
- MLC.essential_induction_step_B
- MLC.Quadratic.groetzsch_inequality_axiom
- MLC.Quadratic.modulus_nonneg
- MLC.puzzle_diff_is_annulus
- MLC.Quadratic.filled_julia_set_connected
- MLC.Quadratic.puzzle_boundary_motion_exists
- MLC.Quadratic.slodkowski_theorem
- MLC.Quadratic.mandelbrot_set_connected
- MLC.infinitely_renormalizable_classification
- MLC.mlc_primitive_renormalizable_ax
- MLC.molecule_conjecture_implies_mlc_satellite
```

## Paper

[Read the Paper (PDF)](docs/proof.pdf). It includes Lean listings next to comments, and attempts to make the proofs human-readable.
*Note: The paper might be updated with a lag. The Lean code in this repository is the higher priority source of truth.*
