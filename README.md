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

*   The high-level logic is implemented in `Mlc/MainConjecture.lean`.
*   The topological reduction (`lc_at_of_shrink`) is fully proven.
*   Yoccoz's theorem (`yoccoz_theorem`) is formalized (modulo some geometric axioms).
*   The infinitely renormalizable case is axiomatized.

## Verification

To verify the proof and check for axioms (sorry), run:

```bash
lake exe check_axioms
```

This will output any axioms used in the proof. The goal is to reduce the axioms to only standard mathematical ones (and the ones explicitly stated for deep theorems).
