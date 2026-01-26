import Mlc.Quadratic.Complex.BottcherMotion
import Mlc.Quadratic.Complex.PuzzleBoundaryMotion

namespace MLC.Quadratic

open Complex Topology Set Filter

/-!
# Detailed Sketch Proof of `motion_preserves_para_piece_of_green_sublevel`

Axiom Statement:
For a sequence of parameters `c_t = c₀ + r * t` in a disk, if:
  (h0)   0 is in the dynamical Green sublevel set `G_n(c_t)`
  (hmem) c_t is in the dynamical Green sublevel set `G_n(c_t)`
  (hconn) G_n(c_t) is connected
then the parameter `c_t` remains in the parameter puzzle piece `P_n(c₀)`.

## Proof Steps:

1. **Dynamical Piece Identification**:
   - `DynamicalPuzzlePiece c_t n 0` is defined as the connected component of `GreenSublevel c_t n` containing `0`.
   - By hypothesis `hconn`, `GreenSublevel c_t n` is its own connected component.
   - Thus, `DynamicalPuzzlePiece c_t n 0 = GreenSublevel c_t n`.
   - By hypothesis `hmem`, we have `c_t ∈ DynamicalPuzzlePiece c_t n 0`.

2. **Boundary Stability via Böttcher Coordinates**:
   - The boundary `E = PuzzleBoundary c₀ n` moves according to the Böttcher motion `h.f t z`.
   - This motion satisfies `phi_{c_t}(h.f t z) = phi_{c₀}(z)`.
   - Since `PuzzleBoundary c n` is defined by `|phi_c(z)| = (1/2)^n`, the motion `h` preserves the boundary of the dynamical puzzle piece.

3. **Invariance of the Piece under Motion**:
   - By Slodkowski's Theorem, the motion `h` extends to `H : ℂ → ℂ → ℂ`.
   - Holomorphic motions are homeomorphisms at each time `t`, and they preserve the topology of components.
   - The interior of the boundary `E` at `t=0` (which is `DynamicalPuzzlePiece c₀ n 0`) is mapped to the interior of the boundary `h.f t E` at time `t`.
   - This image is exactly `DynamicalPuzzlePiece c_t n 0` (or a related component).

4. **Parameter-Dynamics Correspondence (Stability)**:
   - The condition `c_t ∈ ParaPuzzlePieceAt c₀ n` in this project is defined as `c_t - c₀ ∈ DynamicalPuzzlePiece c₀ n 0`.
   - This definition models the parameter piece as a translate of the dynamical piece at the base parameter.
   - The stability lemma asserts that if the dynamical configuration (0 and c relative to the puzzle) 
     is preserved, then the parameter is "trapped" within the corresponding region of the parameter plane.
   - Specifically, if `c_t` is in the dynamical piece `D_n(c_t)` and this piece moves holomorphically 
     without any topological changes (like the boundary hitting 0), the parameter `c_t` is restricted 
     to the para-puzzle piece `P_n`.

5. **Parameter Rescaling and the Unit Disk**:
   - `rescale_param c₀ r t = c₀ + r * t` maps the unit disk `t ∈ Metric.ball 0 1` to a parameter disk `D(c₀, r)`.
   - The holomorphic motion extension `H` is defined over this unit disk.
   - For every `t`, `H.f t` is a homeomorphism of `ℂ` such that `H.f t (D_n(c₀)) = D_n(c_t)`.
   - Since `c_t ∈ D_n(c_t)` (by `hmem` and `hconn`), its Böttcher preimage `H.f t⁻¹(c_t)` must be in `D_n(c₀)`.
   - The project's definition of `ParaPuzzlePieceAt c₀ n` essentially uses the base dynamical piece as a template for the parameter piece.
   - The stability lemma concludes that `c_t` is in the para-puzzle piece because the dynamical puzzle containing the critical value `c_t` (which is `f_{c_t}(0)`) has not crossed any rays or equipotentials.
   - (Note: The critical value `c_t` is the image of `0`, and its position in the puzzle determines the para-piece.)
-/

end MLC.Quadratic
