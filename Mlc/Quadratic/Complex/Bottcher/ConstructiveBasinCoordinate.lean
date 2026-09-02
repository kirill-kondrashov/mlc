import Mlc.Quadratic.Complex.Bottcher.LogSeries
import Yoccoz.Quadratic.Complex.Green

namespace MLC

open Quadratic Complex Topology Set Filter

noncomputable section

lemma boundedOrbit_iff_not_tendsto_infty (c z : ℂ) :
    Quadratic.boundedOrbit c z ↔
      ¬ Tendsto (fun n => ‖(quadratic_map c)^[n] z‖) atTop atTop := by
  constructor
  · rintro ⟨M, hM⟩ ht
    have h := (tendsto_atTop.1 ht) (M + 1)
    rcases eventually_atTop.1 h with ⟨N, hN⟩
    have hN' : M + 1 ≤ ‖(quadratic_map c)^[N] z‖ := hN N le_rfl
    have hbound : ‖(quadratic_map c)^[N] z‖ ≤ M := by
      simpa [Quadratic.orbit, quadratic_map, Quadratic.fc] using hM N
    linarith
  · intro hnt
    by_contra hunbounded
    have hunbounded' : ∀ M : ℝ, ∃ n : ℕ, ‖Quadratic.orbit c z n‖ > M := by
      intro M
      by_contra hM
      push_neg at hM
      exact hunbounded ⟨M, hM⟩
    rcases hunbounded' (Quadratic.R c) with ⟨n₀, hn₀⟩
    have horbit :
        Tendsto (fun n => ‖Quadratic.orbit c z n‖) atTop atTop := by
      rw [tendsto_atTop]
      intro M
      rcases escape_lemma n₀ hn₀ M with ⟨N, hN⟩
      exact eventually_atTop.2 ⟨N, fun n hn => le_of_lt (hN n hn)⟩
    apply hnt
    simpa [Quadratic.orbit, quadratic_map, Quadratic.fc] using horbit

theorem basin_eq_compl_K (c : ℂ) :
    basin_of_infinity c = (Quadratic.K c)ᶜ := by
  ext z
  constructor
  · intro hz
    have hz' : Tendsto (fun n => ‖(quadratic_map c)^[n] z‖) atTop atTop := by
      simpa [basin_of_infinity] using hz
    have hnot : ¬ Quadratic.boundedOrbit c z := by
      intro hbounded
      exact (boundedOrbit_iff_not_tendsto_infty c z).1 hbounded hz'
    simpa [Set.mem_compl_iff, Quadratic.K, Set.mem_setOf_eq] using hnot
  · intro hz
    have hnot : ¬ Quadratic.boundedOrbit c z := by
      simpa [Set.mem_compl_iff, Quadratic.K, Set.mem_setOf_eq] using hz
    have hz' : Tendsto (fun n => ‖(quadratic_map c)^[n] z‖) atTop atTop := by
      by_contra hnt
      exact hnot ((boundedOrbit_iff_not_tendsto_infty c z).2 hnt)
    simpa [basin_of_infinity] using hz'

/-- Every basin point eventually enters the canonical outside-open region. -/
lemma exists_iterate_mem_outside_open_of_mem_basin
    (c z : ℂ) (hz : z ∈ basin_of_infinity c) :
    ∃ n : ℕ, ‖(quadratic_map c)^[n] z‖ > ‖c‖ + 2 := by
  have htend :
      Tendsto (fun n : ℕ => ‖(quadratic_map c)^[n] z‖) atTop atTop := by
    simpa [basin_of_infinity] using hz
  rcases (Filter.eventually_atTop.1
    ((Filter.tendsto_atTop.1 htend) (‖c‖ + 3))) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  have hN' : ‖c‖ + 3 ≤ ‖(quadratic_map c)^[N] z‖ := hN N le_rfl
  linarith

/-- A concrete escape time for basin points. -/
noncomputable def basinEscapeTime (c z : ℂ) (hz : z ∈ basin_of_infinity c) : ℕ :=
  Nat.find (exists_iterate_mem_outside_open_of_mem_basin c z hz)

lemma basinEscapeTime_spec (c z : ℂ) (hz : z ∈ basin_of_infinity c) :
    ‖(quadratic_map c)^[basinEscapeTime c z hz] z‖ > ‖c‖ + 2 :=
  Nat.find_spec (exists_iterate_mem_outside_open_of_mem_basin c z hz)

lemma green_function_orbit_eq_local (c z : ℂ) (n : ℕ) :
    green_function c ((quadratic_map c)^[n] z) =
      2 ^ n * green_function c z := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        green_function c ((quadratic_map c)^[n + 1] z)
            = green_function c (quadratic_map c ((quadratic_map c)^[n] z)) := by
                rw [Function.iterate_succ_apply']
        _ = green_function c (fc c ((quadratic_map c)^[n] z)) := by
              simp [quadratic_map, fc, add_comm]
        _ = 2 * green_function c ((quadratic_map c)^[n] z) := by
              rw [green_function_functional_eq]
        _ = 2 * (2 ^ n * green_function c z) := by rw [ih]
        _ = 2 ^ (n + 1) * green_function c z := by ring

end

end MLC
