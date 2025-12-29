# Mandelbrot Local Connectivity (MLC) Hypothesis

This is a collection of materials on MLC hypothesis.

## Set up

```bash
$ lake exe cache get
$ lake build
```

## Main Conjecture

The formal statement of the Mandelbrot Local Connectivity conjecture can be found in `Mlc/MainConjecture.lean`.

## Proof Scheme for MLC

Based on "Conformal Geometry and Dynamics of Quadratic Polynomials", the strategy to prove that the Mandelbrot set $M$ is locally connected (MLC) relies on the theory of Yoccoz Puzzles.

### 1. Dynamical Plane Construction (Yoccoz Puzzles)
For a quadratic polynomial $f_c(z) = z^2 + c$ with connected Julia set $J_c$, we construct a sequence of partitions of the dynamical plane.
*   Rays: Use external rays landing at repelling or parabolic periodic points (specifically the $\alpha$-fixed point and its preimages).
*   Equipotentials: Use equipotential curves coming from the Böttcher coordinate at infinity.
*   Puzzle Pieces: The intersection of regions bounded by these rays and equipotentials forms a "puzzle".
*   Depth: Increasing the depth $n$ (taking more preimages) refines the partition, creating a sequence of puzzle pieces $P_n(z)$ containing a point $z$.

### 2. Parameter Plane Transfer (Para-puzzles)
The combinatorial structure of the dynamical plane is transferred to the parameter plane $M$.
*   Para-rays: External rays in the parameter plane landing at specific parameters.
*   Para-puzzle Pieces: Regions in the parameter plane $\mathcal{P}_n(c)$ defined similarly to the dynamical plane.
*   Correspondence: For $c \in \mathcal{P}_n(c)$, the critical value $c = f_c(0)$ lies in a specific dynamical puzzle piece $P_n(0)$.

### 3. Yoccoz's Theorem
The core geometric argument is based on the moduli of annuli.
*   Annuli: Consider the annulus $A_n = P_n(0) \setminus P_{n+1}(0)$ (or similar nested pieces).
*   Modulus Condition: If $\sum \text{mod}(A_n) = \infty$, then the intersection $\cap P_n(0)$ is a single point.
*   Implication: This implies that the Julia set is locally connected at the critical point, and by transfer, the Mandelbrot set is locally connected at $c$.

### 4. Combinatorics and Tableau
To prove the modulus condition, one analyzes the combinatorics of the recurrence of the critical orbit.
*   Yoccoz Tableau: A 2D grid representing the puzzle pieces $P_d(f^k(0))$.
*   Recurrence: How often the critical orbit returns to the central puzzle pieces.
*   Non-renormalizable case: For non-renormalizable parameters, Yoccoz proved MLC by showing the moduli sum diverges.

### 5. Renormalization
If the map is infinitely renormalizable, the puzzle pieces might not shrink to a point in the standard construction.
*   Small Mandelbrot Sets: These correspond to renormalization windows.
*   PL-Homeomorphisms: The dynamics can be rescaled to look like a polynomial of the same degree.
*   Full Proof: Requires handling these infinitely renormalizable cases (e.g., using Lyubich's work on renormalization).

### Summary of Steps
1.  Define the Yoccoz puzzle partition in the dynamical plane.
2.  Define the corresponding para-puzzle in the parameter plane.
3.  Establish the correspondence between dynamical and parameter pieces.
4.  Prove that for "most" parameters (at least non-renormalizable ones), the moduli of nested annuli diverge.
5.  Conclude local connectivity from the shrinking of puzzle pieces.