import Yoccoz.Quadratic.Complex.Basic
import Yoccoz.Quadratic.Complex.Green
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Constructions
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.GCongr
import Yoccoz.Quadratic.Complex.Puzzle
import Yoccoz.Quadratic.Complex.PuzzleLemmas
import Mlc.Quadratic.Complex.ParaPuzzle
import Mlc.Quadratic.Complex.Axioms
import Mlc.Quadratic.Complex.ParaPuzzleBasis

namespace MLC.Quadratic

open Complex Topology Filter Set

noncomputable section

variable (c : ℂ)

set_option maxHeartbeats 1600000

/-- Parameter puzzle pieces are open sets. -/
theorem para_puzzle_piece_open (c : ℂ) (n : ℕ) :
    IsOpen (ParaPuzzlePieceAt c n) := by
  -- `DynamicalPuzzlePiece` is a connected component of an open set.
  have h_open : IsOpen (DynamicalPuzzlePiece c n 0) := by
    have h_base : IsOpen {w | green_function c w < (1 / 2) ^ n} :=
      IsOpen.preimage (continuous_green_function c) isOpen_Iio
    simpa [DynamicalPuzzlePiece] using IsOpen.connectedComponentIn h_base
  have h_cont : Continuous (fun z : ℂ => z - c) := continuous_id.sub continuous_const
  have h_eq :
      ParaPuzzlePieceAt c n = (fun z : ℂ => z - c) ⁻¹' DynamicalPuzzlePiece c n 0 := by
    ext z
    rfl
  simpa [h_eq] using h_open.preimage h_cont


/-- Parameter puzzle pieces form a basis of neighborhoods if they shrink to a point. -/
theorem para_puzzle_piece_basis (c : ℂ) (h : (⋂ n, ParaPuzzlePieceAt c n) = {c}) :
    ∀ U ∈ 𝓝 c, ∃ n, ParaPuzzlePieceAt c n ⊆ U := 
  para_puzzle_piece_basis_sketch c h

/-- If parameter pieces shrink to a point, they form a neighborhood basis at `c`. -/
theorem parameter_shrink (c : ℂ) :
    (⋂ n, ParaPuzzlePieceAt c n) = {c} →
      ∀ U ∈ 𝓝 c, ∃ n, ParaPuzzlePieceAt c n ⊆ U := by
  intro h
  exact para_puzzle_piece_basis c h

/-- Parameter puzzle pieces intersected with the Mandelbrot set are connected
    for Mandelbrot base parameters.
    Proof idea:
    The set `P_n ∩ M` corresponds to parameters `c ∈ M` such that `c` (or `0`? via correspondence)
    is in the dynamical piece `D_n(c)`.
    Since `c ∈ M`, the filled Julia set `K(c)` is connected (Douady-Hubbard).
    The dynamical piece `D_n(c)` is defined by level sets of Green's function, which surrounds `K(c)`.
    Since `0 ∈ K(c) ⊆ D_n(c)`, the condition is satisfied for all `c ∈ M`.
    So `P_n ∩ M` is effectively just `M`?
    (The proof shows `M ⊆ P_n` implies `P_n ∩ M = M`, and `M` is connected). -/
axiom para_puzzle_piece_inter_mandelbrot_connected (c : ℂ)
    (hc : c ∈ MandelbrotSet) (n : ℕ) :
    IsConnected (ParaPuzzlePieceAt c n ∩ MandelbrotSet)

/-- Replacement hook for `para_puzzle_piece_inter_mandelbrot_connected`. -/
def ParaPuzzlePieceInterMandelbrotConnectedData : Prop :=
  ∀ c, c ∈ MandelbrotSet → ∀ n, IsConnected (ParaPuzzlePieceAt c n ∩ MandelbrotSet)

/-- Stronger candidate bridge target: every Mandelbrot parameter belongs to each
    para-puzzle piece centered at a Mandelbrot parameter. -/
def ParaPuzzleMandelbrotSubsetData : Prop :=
  ∀ c, c ∈ MandelbrotSet → ∀ n, MandelbrotSet ⊆ ParaPuzzlePieceAt c n

theorem para_puzzle_piece_inter_mandelbrot_connected_of_data
    (h_conn : ParaPuzzlePieceInterMandelbrotConnectedData)
    (c : ℂ) (hc : c ∈ MandelbrotSet) (n : ℕ) :
    IsConnected (ParaPuzzlePieceAt c n ∩ MandelbrotSet) :=
  h_conn c hc n

theorem para_puzzle_piece_inter_mandelbrot_connected_of_mandelbrot_subset
    (c : ℂ) (n : ℕ) (hsub : MandelbrotSet ⊆ ParaPuzzlePieceAt c n) :
    IsConnected (ParaPuzzlePieceAt c n ∩ MandelbrotSet) := by
  have h_eq : ParaPuzzlePieceAt c n ∩ MandelbrotSet = MandelbrotSet := by
    ext z
    constructor
    · intro hz
      exact hz.2
    · intro hz
      exact ⟨hsub hz, hz⟩
  simpa [h_eq] using (mandelbrot_set_connected : IsConnected MandelbrotSet)

theorem para_puzzle_piece_inter_mandelbrot_connected_data_of_mandelbrot_subset_data
    (hsub : ParaPuzzleMandelbrotSubsetData) :
    ParaPuzzlePieceInterMandelbrotConnectedData := by
  intro c hc n
  exact para_puzzle_piece_inter_mandelbrot_connected_of_mandelbrot_subset c n (hsub c hc n)

lemma para_puzzle_piece_inter_mandelbrot_connected_data_of_axiom :
    ParaPuzzlePieceInterMandelbrotConnectedData := by
  intro c hc n
  exact para_puzzle_piece_inter_mandelbrot_connected c hc n

end

end MLC.Quadratic
