import Mlc.Quadratic.Complex.PuzzleBoundaryMotion
import Mathlib.Topology.Connected.PathConnected

namespace MLC

open Quadratic Complex Topology Set Filter

/-- For c ∈ M, the filled Julia set K_c is connected. -/
lemma Kc_connected (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet) : IsConnected (MLC.Quadratic.K c) := by
  exact MLC.Quadratic.filled_julia_set_connected hc

/-- The Green function is continuous on ℂ. -/
lemma green_continuous (c : ℂ) : Continuous (MLC.Quadratic.green_function c) := by
  exact MLC.Quadratic.continuous_green_function c

/--
Every point in the Green sublevel set `S` is path-connected to `K_c` within `S`.
This essentially means that equipotential lines (or rather gradient lines) connect points to K.
For now, we assume this as a lemma, relying on the dynamical properties of the Green function
(foliation by external rays).
-/
lemma green_sublevel_joined_to_Kc (c : ℂ) (n : ℕ) :
    let S := MLC.Quadratic.GreenSublevel c n
    let K := MLC.Quadratic.K c
    ∀ z ∈ S, ∃ w ∈ K, JoinedIn S z w := by
  intro S K z hz
  -- Sketch of proof:
  -- 1. If z ∈ K, then w = z and we are done.
  -- 2. If z ∉ K, then G_c(z) > 0.
  -- 3. There exists an external ray passing through z.
  -- 4. Following the ray downwards reduces the Green function.
  -- 5. The ray lands on K (or accumulates on it) because K is connected (c ∈ M).
  -- 6. The segment of the ray from z to K lies in the sublevel set because G decreases.
  sorry

/--
If K_c is connected and the Green function is continuous and proper (implied by properties),
then the sublevel sets {z | G_c(z) < ε} are connected.
-/
lemma green_sublevel_connected_of_connected_Kc (c : ℂ) (n : ℕ) (hK : IsConnected (MLC.Quadratic.K c)) :
    IsConnected (MLC.Quadratic.GreenSublevel c n) := by
  let S := MLC.Quadratic.GreenSublevel c n
  let K := MLC.Quadratic.K c
  have h_S_def : S = MLC.Quadratic.GreenSublevel c n := rfl
  
  -- 1. The filled Julia set K_c is contained in the Green sublevel set.
  have hK_sub : K ⊆ S := by
    intro z hz
    dsimp [S, K, MLC.Quadratic.GreenSublevel]
    have hGz : MLC.Quadratic.green_function c z = 0 :=
      (MLC.Quadratic.green_function_eq_zero_iff_mem_K c z).2 hz
    rw [hGz]
    positivity
  
  -- 2. Every point in the Green sublevel set is in the same component as K_c.
  have h_same_comp : ∀ z ∈ S, ∃ w ∈ K, JoinedIn S z w :=
    green_sublevel_joined_to_Kc c n

  -- 3. Show S is connected.
  -- We construct S as the union of connected sets (path components) that all intersect K (which is connected).
  let family := {C | ∃ z ∈ S, ∃ w ∈ K, ∃ p : JoinedIn S z w, C = range p.somePath ∪ K}
  
  -- S is the union of this family
  have h_union : S = ⋃₀ family := by
    ext z
    constructor
    · intro hz
      obtain ⟨w, hw, h_joined⟩ := h_same_comp z hz
      let C := range h_joined.somePath ∪ K
      have hC : C ∈ family := ⟨z, hz, w, hw, h_joined, rfl⟩
      refine mem_sUnion_of_mem ?_ hC
      left
      exact h_joined.somePath.source_mem_range
    · intro hz
      obtain ⟨C, ⟨u, hu, v, hv, h_joined, rfl⟩, h_in_C⟩ := hz
      rcases h_in_C with h_path | h_K
      · obtain ⟨t, ht⟩ := h_path
        rw [← ht]
        exact JoinedIn.somePath_mem h_joined t
      · exact hK_sub h_K

  rw [← h_S_def, h_union]
  obtain ⟨x0, hx0⟩ := hK.nonempty
  have h_pre : IsPreconnected (⋃₀ family) := by
    apply isPreconnected_sUnion x0
    · intro C hC
      obtain ⟨z, hz, w, hw, h_joined, rfl⟩ := hC
      right
      exact hx0
    · intro C hC
      obtain ⟨z, hz, w, hw, h_joined, rfl⟩ := hC
      apply IsPreconnected.union w
      · exact h_joined.somePath.target_mem_range
      · exact hw
      · exact (isConnected_range h_joined.somePath.continuous).isPreconnected
      · exact hK.isPreconnected

  constructor
  · -- Show nonempty
    use x0
    rw [mem_sUnion]
    have hx0_S : x0 ∈ S := hK_sub hx0
    use range (JoinedIn.refl hx0_S).somePath ∪ K
    constructor
    · refine ⟨x0, hx0_S, x0, hx0, JoinedIn.refl hx0_S, rfl⟩
    · right; exact hx0
  · exact h_pre

/--
Theorem: Green sublevel sets are connected on the Mandelbrot set.
(Formerly an axiom).
-/
theorem green_sublevel_connected : MLC.Quadratic.GreenSublevelConnectedHyp := {
  connected := by
    intro c n hc
    apply green_sublevel_connected_of_connected_Kc
    exact Kc_connected c hc
}

end MLC