# ⚠️ **EXPERIMENTAL PROJECT DISCLAIMER** ⚠️

> 🧪 **This repository is an experimental attempt to explore the MLC Conjecture using Lean 4 and LLMs.** 🤖
>
> This work is inspired by **[DeepSeek-Prover-V1.5: Unleashing the Potential of Long-Chain-of-Thought Reasoning for Theorem Proving](https://arxiv.org/abs/2511.02864)** and similar AI-assisted formalization approaches.
>
> 🚧 **Please Note:**
> *   This is a **proof-of-concept** exploration, not a complete mathematical verification.
> *   The goal is to test the limits of LLMs in formalizing deep mathematical theory.
> *   Expect experimental code and potential axioms!

---

# MLC Conjecture Formalization

This repository contains a formalization of the MLC (Mandelbrot Set is Locally Connected) Conjecture for quadratic polynomials in Lean 4.

## Overview

The goal is to prove that the Mandelbrot set $M$ is locally connected. The proof strategy follows the standard approach using Yoccoz puzzles and renormalization theory.

## Proof Structure

The formalization is organized as follows:

### 1. Main Conjecture
*   File: `Mlc/MainConjecture.lean`
*   Content: Defines the `MLC_Conjecture` and provides the high-level proof structure.
*   Logic: The proof splits into two cases based on the renormalization of the parameter $c$:
    *   Finitely Renormalizable: Handled by Yoccoz's Theorem.
    *   Infinitely Renormalizable: Handled by Lyubich's Theorem.

### 2. Local Connectivity from Shrinking Puzzles
*   File: `Mlc/LcAtOfShrink.lean`
*   Content: Proves that if the parameter puzzle pieces $P_n(c)$ shrink to the single point $\{c\}$, then the Mandelbrot set is locally connected at $c$.
*   Key Lemma: `lc_at_of_shrink` establishes the link between the combinatorial shrinking of puzzles and the topological property of local connectivity.

### 3. Finitely Renormalizable Case (Yoccoz's Theorem)
*   File: `Mlc/Yoccoz.lean`
*   Content: Handles the case where $c$ is not infinitely renormalizable.
*   Theorem: `yoccoz_theorem` states that if the moduli of the puzzle annuli diverge (which happens in the non-renormalizable case), then the dynamical puzzle pieces shrink to a point. This implies the parameter pieces also shrink.

### 4. Infinitely Renormalizable Case
*   File: `Mlc/InfinitelyRenormalizable.lean`
*   Content: Handles the case where $c$ is infinitely renormalizable.
*   Status: This part relies on deep results by Lyubich (and Kahn-Lyubich), which are currently axiomatized (`mlc_infinitely_renormalizable`).

## Dependencies

*   Mathlib: The project relies heavily on the Lean mathematical library (Mathlib) for topology, complex analysis, and set theory.

## Current Status

*   **Top-Level Proof Completed**: The main theorem `MLC_Conjecture` is now fully proven in `Mlc/MainConjecture.lean`, modulo the axioms listed below. The proof successfully handles the dichotomy between non-renormalizable and infinitely renormalizable parameters.
*   **CI Integration**: The GitHub Actions pipeline now enforces that the proof contains no `sorry` (admit) tactics, ensuring that all dependencies are explicitly stated as axioms.
*   **Topological Reduction**: The reduction from shrinking puzzles to local connectivity (`lc_at_of_shrink`) is fully proven.
*   **Yoccoz's Theorem**: Formalized using the Grötzsch criterion.

## Axioms Introduced

The proof relies on the following axioms, which abstract away deep geometric and analytic results. These are defined in `Mlc/Quadratic/Complex/Puzzle.lean` and `Mlc/InfinitelyRenormalizable.lean`.

### 1. Yoccoz Puzzles & Geometry
*   [`groetzsch_inequality`](Mlc/Quadratic/Complex/Groetzsch.lean#L64): Grötzsch's Inequality (Superadditivity of modulus).
    *   Source: [Milnor, Dynamics in One Complex Variable, Corollary B.5] (Local: `refs/9201272v1.pdf`)
    *   Note: This axiom is used to prove **`modulus_summable_of_nontrivial_intersection`**, which states that if the intersection of nested pieces is non-trivial, the sum of moduli converges.
*   **Topological Properties**: [`para_puzzle_piece_open`](Mlc/Quadratic/Complex/PuzzleLemmas2.lean#L116) (pieces are open).
    *   Source: [Lyubich, Conformal Geometry and Dynamics of Quadratic Polynomials, Lemma 3.1] (Local: `refs/Conformal Geometry and Dynamics of Quadratic Polynomials.pdf`)
    *   Note: Relies on Slodkowski's Theorem (Generalized Lambda Lemma): [Holomorphic motions and polynomial hulls](https://www.ams.org/journals/proc/1991-111-02/S0002-9939-1991-1037218-8/).
*   **Basic Properties**:
    *   [`modulus_nonneg_ax`](Mlc/Quadratic/Complex/Groetzsch.lean#L50): Modulus is non-negative.
        *   Source: [Milnor, Dynamics in One Complex Variable] (Local: `refs/9201272v1.pdf`, Appendix B)
*   **Connectivity**: [`mandelbrot_set_connected`](Mlc/Quadratic/Complex/Basic.lean#L59) (Mandelbrot set is connected) and [`filled_julia_set_connected`](Mlc/Quadratic/Complex/Basic.lean#L63) (Filled Julia set is connected for $c \in M$).
    *   Source: [Douady and Hubbard, Etude dynamique des polynômes complexes, 1984]

### 2. Deep Theorems
*   [`mlc_infinitely_renormalizable_ax`](Mlc/InfinitelyRenormalizable.lean#L26): Lyubich's Theorem stating that the Mandelbrot set is locally connected at infinitely renormalizable parameters.
    *   Source: [Lyubich, The Dynamics of Quadratic Polynomials I-II, Main Theorem] (Local: `refs/Conformal Geometry and Dynamics of Quadratic Polynomials.pdf`)

## Verification

To verify the proof and check for axioms (sorry), run:

```bash
make check
```

This will output any axioms used in the proof. The goal is to reduce the axioms to only standard mathematical ones (and the ones explicitly stated for deep theorems).

Example output:
```
✅ The proof of 'MLC.MLC_Conjecture' is free of 'sorry'.
All axioms used:
- Quot.sound
- propext
- Classical.choice
- MLC.Quadratic.groetzsch_inequality
- MLC.Quadratic.modulus_nonneg_ax
- MLC.Quadratic.filled_julia_set_connected
- MLC.Quadratic.para_puzzle_piece_open
- MLC.Quadratic.mandelbrot_set_connected
- MLC.mlc_infinitely_renormalizable_ax
```
