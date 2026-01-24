import Yoccoz.Quadratic.Complex.Green
import Mlc.Quadratic.Complex.PuzzleBoundaryMotion
import Mathlib.Topology.Basic
import Mathlib.Topology.Order.OrderClosed

namespace MLC.Quadratic

open Complex Topology Set

noncomputable section

/-- The equipotential of level `n` for the Green function. -/
def Equipotential (c : ℂ) (n : ℕ) : Set ℂ :=
  {z | green_function c z = (1 / 2 : ℝ) ^ n}

/-- The closed Green sublevel of depth `n`. -/
def GreenSublevelClosed (c : ℂ) (n : ℕ) : Set ℂ :=
  {z | green_function c z ≤ (1 / 2 : ℝ) ^ n}

/-- Equipotentials are closed sets (by continuity of the Green function). -/
lemma equipotential_closed (c : ℂ) (n : ℕ) :
    IsClosed (Equipotential c n) := by
  have hcont : Continuous (green_function c) := continuous_green_function c
  simpa [Equipotential] using (IsClosed.preimage hcont isClosed_singleton)

/-- Closed Green sublevels are closed (by continuity of the Green function). -/
lemma green_sublevel_closed (c : ℂ) (n : ℕ) :
    IsClosed (GreenSublevelClosed c n) := by
  have hcont : Continuous (green_function c) := continuous_green_function c
  simpa [GreenSublevelClosed] using (IsClosed.preimage hcont isClosed_Iic)

/-- Open sublevels are contained in closed sublevels. -/
lemma green_sublevel_subset_closed (c : ℂ) (n : ℕ) :
    GreenSublevel c n ⊆ GreenSublevelClosed c n := by
  intro z hz
  have hz' : green_function c z < (1 / 2 : ℝ) ^ n := by
    simpa [GreenSublevel] using hz
  have hle : green_function c z ≤ (1 / 2 : ℝ) ^ n := le_of_lt hz'
  simpa [GreenSublevelClosed] using hle

/-- The closure of an open sublevel is contained in the closed sublevel. -/
lemma closure_green_sublevel_subset_closed (c : ℂ) (n : ℕ) :
    closure (GreenSublevel c n) ⊆ GreenSublevelClosed c n := by
  intro z hz
  have hclosed : IsClosed (GreenSublevelClosed c n) := green_sublevel_closed c n
  have hsubset : GreenSublevel c n ⊆ GreenSublevelClosed c n :=
    green_sublevel_subset_closed c n
  exact hclosed.closure_subset_iff.2 hsubset hz

/-- Equipotentials are contained in the closed sublevel. -/
lemma equipotential_subset_closed (c : ℂ) (n : ℕ) :
    Equipotential c n ⊆ GreenSublevelClosed c n := by
  intro z hz
  have hz' : green_function c z = (1 / 2 : ℝ) ^ n := by
    simpa [Equipotential] using hz
  have hle : green_function c z ≤ (1 / 2 : ℝ) ^ n := by
    simp [hz']
  simpa [GreenSublevelClosed] using hle

/-- The boundary of an open Green sublevel lies in the equipotential. -/
lemma frontier_green_sublevel_subset_equipotential (c : ℂ) (n : ℕ) :
    frontier (GreenSublevel c n) ⊆ Equipotential c n := by
  have hcont : Continuous (green_function c) := continuous_green_function c
  have hconst : Continuous (fun _ : ℂ => (1 / 2 : ℝ) ^ n) := continuous_const
  have hfront :
      frontier {z : ℂ | green_function c z < (1 / 2 : ℝ) ^ n} ⊆
        {z : ℂ | green_function c z = (1 / 2 : ℝ) ^ n} :=
    frontier_lt_subset_eq hcont hconst
  simpa [GreenSublevel, Equipotential] using hfront

end

end MLC.Quadratic
