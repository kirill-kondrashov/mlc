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
    IsOpen (ParaPuzzlePieceAt c n) :=
  para_puzzle_piece_at_isOpen c n


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

/-- Current axiom-backed provider for para-puzzle connectedness on `M`.
    This isolates the single FR replacement target in one payload. -/
theorem para_puzzle_piece_inter_mandelbrot_connected_data_of_axiom :
    ParaPuzzlePieceInterMandelbrotConnectedData := by
  intro c hc n
  exact para_puzzle_piece_inter_mandelbrot_connected c hc n

/-- Stronger candidate bridge target: every Mandelbrot parameter belongs to each
    para-puzzle piece centered at a Mandelbrot parameter. -/
def ParaPuzzleMandelbrotSubsetData : Prop :=
  ∀ c, c ∈ MandelbrotSet → ∀ n, MandelbrotSet ⊆ ParaPuzzlePieceAt c n

/-- Transport-witness bridge target: each para-puzzle intersection on `M` is
    identified with an explicitly connected set. -/
structure ParaPuzzleInterMandelbrotTransportData where
  transportSet : ℂ → ℕ → Set ℂ
  connected :
    ∀ c, c ∈ MandelbrotSet → ∀ n, IsConnected (transportSet c n)
  eq_inter :
    ∀ c, c ∈ MandelbrotSet → ∀ n,
      transportSet c n = ParaPuzzlePieceAt c n ∩ MandelbrotSet

/-- Existential transport-witness target: for each Mandelbrot base parameter
    and depth, there exists a connected witness set for the para-puzzle
    intersection. -/
structure ParaPuzzleInterMandelbrotTransportExistsData : Prop where
  witness :
    ∀ c, c ∈ MandelbrotSet → ∀ n,
      ∃ S : Set ℂ, IsConnected S ∧ S = ParaPuzzlePieceAt c n ∩ MandelbrotSet

/-- Build existential transport data directly from a witness function. -/
def para_puzzle_transport_exists_data_of_witness
    (h :
      ∀ c, c ∈ MandelbrotSet → ∀ n,
        ∃ S : Set ℂ, IsConnected S ∧ S = ParaPuzzlePieceAt c n ∩ MandelbrotSet) :
    ParaPuzzleInterMandelbrotTransportExistsData where
  witness := h

/-- Build concrete transport data from the existential witness target. -/
noncomputable def para_puzzle_transport_data_of_exists_data
    (hex : ParaPuzzleInterMandelbrotTransportExistsData) :
    ParaPuzzleInterMandelbrotTransportData := by
  classical
  refine
    { transportSet := fun c n =>
        if hc : c ∈ MandelbrotSet then
          Classical.choose (hex.witness c hc n)
        else
          ∅
      connected := ?_
      eq_inter := ?_ }
  · intro c hc n
    simp [hc]
    exact (Classical.choose_spec (hex.witness c hc n)).1
  · intro c hc n
    simp [hc]
    exact (Classical.choose_spec (hex.witness c hc n)).2

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

theorem para_puzzle_piece_inter_mandelbrot_connected_data_of_transport_data
    (htr : ParaPuzzleInterMandelbrotTransportData) :
    ParaPuzzlePieceInterMandelbrotConnectedData := by
  intro c hc n
  have h_conn : IsConnected (htr.transportSet c n) := htr.connected c hc n
  have h_eq : htr.transportSet c n = ParaPuzzlePieceAt c n ∩ MandelbrotSet :=
    htr.eq_inter c hc n
  simpa [h_eq] using h_conn

theorem para_puzzle_piece_inter_mandelbrot_connected_data_of_transport_exists_data
    (hex : ParaPuzzleInterMandelbrotTransportExistsData) :
    ParaPuzzlePieceInterMandelbrotConnectedData :=
  para_puzzle_piece_inter_mandelbrot_connected_data_of_transport_data
    (para_puzzle_transport_data_of_exists_data hex)

def para_puzzle_transport_exists_data_of_connected_data
    (h_conn : ParaPuzzlePieceInterMandelbrotConnectedData) :
    ParaPuzzleInterMandelbrotTransportExistsData where
  witness c hc n := ⟨ParaPuzzlePieceAt c n ∩ MandelbrotSet, h_conn c hc n, rfl⟩

def para_puzzle_transport_exists_data_of_transport_data
    (htr : ParaPuzzleInterMandelbrotTransportData) :
    ParaPuzzleInterMandelbrotTransportExistsData where
  witness c hc n := ⟨htr.transportSet c n, htr.connected c hc n, htr.eq_inter c hc n⟩

def para_puzzle_transport_exists_data_of_mandelbrot_subset_data
    (hsub : ParaPuzzleMandelbrotSubsetData) :
    ParaPuzzleInterMandelbrotTransportExistsData :=
  para_puzzle_transport_exists_data_of_connected_data
    (para_puzzle_piece_inter_mandelbrot_connected_data_of_mandelbrot_subset_data hsub)

def para_puzzle_transport_data_of_connected_data
    (h_conn : ParaPuzzlePieceInterMandelbrotConnectedData) :
    ParaPuzzleInterMandelbrotTransportData where
  transportSet c n := ParaPuzzlePieceAt c n ∩ MandelbrotSet
  connected c hc n := h_conn c hc n
  eq_inter _c _hc _n := rfl

def para_puzzle_transport_data_of_mandelbrot_subset_data
    (hsub : ParaPuzzleMandelbrotSubsetData) :
    ParaPuzzleInterMandelbrotTransportData :=
  para_puzzle_transport_data_of_connected_data
    (para_puzzle_piece_inter_mandelbrot_connected_data_of_mandelbrot_subset_data hsub)

end

end MLC.Quadratic
