import Mlc.Quadratic.Complex.PuzzleBoundaryMotion
import Mathlib.Topology.Connected.PathConnected

namespace MLC

open Quadratic Complex Topology Set Filter

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
  by_cases h_in_K : z ∈ K
  · use z
    exact ⟨h_in_K, JoinedIn.refl hz⟩

  -- 2. If z ∉ K, then G_c(z) > 0.
  have h_G_pos : 0 < MLC.Quadratic.green_function c z := by
    rw [← MLC.Quadratic.green_function_eq_zero_iff_mem_K c z] at h_in_K
    apply lt_of_le_of_ne (MLC.Quadratic.green_function_nonneg c z) (Ne.symm h_in_K)

  -- 3. There exists an external ray passing through z.
  -- We need to introduce the concept of external rays or dynamic rays here.
  -- Since we don't have Böttcher coordinates fully formalized for the dynamical plane in the imports seen so far,
  -- we might need to assume their existence or use the property that z lies on some dynamic ray R_t.
  
  -- 4. Following the ray downwards reduces the Green function.
  -- The ray R_t is parameterized by potential level. 
  -- Let R_t(s) be the point on ray t at potential s.
  -- z = R_t(G(z)).
  -- Consider the path γ(u) = R_t((1-u)*G(z)) for u ∈ [0, 1].
  -- This path starts at z and approaches K as u -> 1.
  
  -- 5. The ray lands on K (or accumulates on it) because K is connected (c ∈ M).
  -- Since c ∈ M, K_c is connected. Dynamic rays accumulate on K_c.
  -- In fact, since G_c is proper on ℂ \ K_c, any gradient flow line accumulates on K_c (or infinity, but we are going down).

  -- 6. The segment of the ray from z to K lies in the sublevel set because G decreases.
  -- For u ∈ [0, 1), G(γ(u)) = (1-u)*G(z) < G(z) < 1/2^n.
  -- So the entire path stays in S.
  
  sorry

end MLC
