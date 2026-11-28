import Mlc.Research.Collar

/-!
# The rate at which a nest shrinks

`NestModulus.lean` shows that a nest whose moduli add up to infinity shrinks to its point, and
`Collar.lean` that a nest with uniform collars is such a nest. This module makes the shrinking
quantitative, in the form of a Teichmüller-type estimate: the size of a piece of a nest is controlled
by the total modulus of the annuli that precede it. The constants are those of the metric
`1 / |z − c|` of `NestModulus.lean` and are far from the optimal ones of Teichmüller's modulus
theorem.

* **Theorem `ConnectedNest.closure_piece_subset_closedBall_of_sum`**: if the first piece lies in the
  disk of radius `R` around `c` and the first `n` annuli have total modulus at least `s`, with
  `κ s ≥ log 8` and `κ = (log 2)² / 2π`, the closure of the piece `n` lies in the disk of radius
  `8 R e^{−κ s}`.
* `ConnectedNest.closure_piece_subset_closedBall_of_uniform`: moduli bounded below by `w` give the
  exponential decay `8 R e^{−κ w n}` for every `n` with `κ n w ≥ log 8`.
* **Theorem `ConnectedNest.closure_piece_subset_closedBall_of_collars`**: a nest whose annuli all
  have collars of dilatation at most `K₀` and modulus at least `μ₀ / 2π` shrinks at the rate
  `exp (−κ μ₀ n / (2π K₀))`: bounded geometry gives the geometric decay of the diameters.

The constants are those of the metric `1 / |z − c|` of `NestModulus.lean` and are far from optimal.
The rate is geometric in the number of levels. Whether it gives a Hölder estimate for the landing
map of the rays depends on the angular sizes of the pieces, and, given Shishikura's theorem, the
exponent of any such estimate is at most `1/2` (`Dimension.lean`).
-/

namespace MLC.Research

open MeasureTheory ENNReal Set Real Topology Metric

noncomputable section

namespace ConnectedNest

variable {S : Set ℂ} {c : ℂ} (D : ConnectedNest S c)

/-- **A Teichmüller-type estimate for a nest: the size of a piece is controlled by the total
modulus.**
If the first piece lies in the disk of radius `R` around `c` and the first `n` annuli have total
modulus at least `s`, with `κ s ≥ log 8` for `κ = (log 2)² / 2π`, the closure of the piece `n` lies
in the disk of radius `8 R e^{−κ s}`. -/
theorem closure_piece_subset_closedBall_of_sum {R s : ℝ} (hR : 0 < R)
    (hR' : closure (D.piece 0) ⊆ closedBall c R) {n : ℕ}
    (hs : ENNReal.ofReal s ≤ ∑ j ∈ Finset.range n, extWidth volume (D.loops j))
    (hlog : Real.log 8 ≤ (Real.log 2) ^ 2 / (2 * π) * s) :
    closure (D.piece n) ⊆
      closedBall c (8 * R * Real.exp (-((Real.log 2) ^ 2 / (2 * π) * s))) := by
  intro z hz
  by_contra hzc
  rw [mem_closedBall, not_le] at hzc
  set κ : ℝ := (Real.log 2) ^ 2 / (2 * π) with hκ
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hκpos : 0 < κ := by positivity
  have hε : 0 < 8 * R * Real.exp (-(κ * s)) := by positivity
  have hδ : 0 < dist z c := hε.trans hzc
  have hzR : dist z c ≤ R :=
    mem_closedBall.1 (hR' (closure_mono (D.antitone_piece (Nat.zero_le n)) hz))
  have h1 := hs.trans (D.sum_extWidth_loops_le hδ hR' hz le_rfl)
  have hpos : 0 < 4 * (R + dist z c) / dist z c := by positivity
  have hlogpos : 0 ≤ Real.log (4 * (R + dist z c) / dist z c) := by
    refine Real.log_nonneg ?_
    rw [le_div_iff₀ hδ]
    nlinarith
  have h2 : s ≤ 2 * π * Real.log (4 * (R + dist z c) / dist z c) / (Real.log 2) ^ 2 := by
    have h3 : ENNReal.ofReal s ≤ ENNReal.ofReal
        (2 * π * Real.log (4 * (R + dist z c) / dist z c) / (Real.log 2) ^ 2) := by
      refine h1.trans (le_of_eq ?_)
      rw [ENNReal.ofReal_div_of_pos (by positivity),
        ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * π), ENNReal.ofReal_pow hlog2.le]
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h3
  have h4 : κ * s ≤ Real.log (4 * (R + dist z c) / dist z c) := by
    rw [hκ]
    have : (Real.log 2) ^ 2 / (2 * π) * s ≤ (Real.log 2) ^ 2 / (2 * π) *
        (2 * π * Real.log (4 * (R + dist z c) / dist z c) / (Real.log 2) ^ 2) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    calc (Real.log 2) ^ 2 / (2 * π) * s ≤ _ := this
      _ = Real.log (4 * (R + dist z c) / dist z c) := by field_simp
  have h8 : 8 ≤ Real.exp (κ * s) := by
    calc (8 : ℝ) = Real.exp (Real.log 8) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp (κ * s) := Real.exp_le_exp.2 hlog
  have h5 : 4 * (R + dist z c) / dist z c < Real.exp (κ * s) := by
    have h6 : R / dist z c < Real.exp (κ * s) / 8 := by
      rw [div_lt_iff₀ hδ]
      have h9 : 8 * R * Real.exp (-(κ * s)) < dist z c := hzc
      have h10 : Real.exp (κ * s) * Real.exp (-(κ * s)) = 1 := by
        rw [← Real.exp_add]; simp
      nlinarith [Real.exp_pos (κ * s), Real.exp_pos (-(κ * s))]
    have h7 : 4 * (R + dist z c) / dist z c = 4 * (R / dist z c) + 4 := by
      field_simp
    rw [h7]
    linarith
  have h11 := Real.log_lt_log hpos h5
  rw [Real.log_exp] at h11
  linarith

/-- **Uniform moduli give exponential shrinking.** If every annulus of the nest has modulus at least
`w`, the closure of the piece `n` lies in the disk of radius `8 R e^{-κ w n}` around `c`, where
`κ = (log 2)² / 2π` and `κ n w ≥ log 8`. -/
theorem closure_piece_subset_closedBall_of_uniform {R w : ℝ} (hR : 0 < R)
    (hR' : closure (D.piece 0) ⊆ closedBall c R)
    (hmod : ∀ j, ENNReal.ofReal w ≤ extWidth volume (D.loops j)) {n : ℕ}
    (hn : Real.log 8 ≤ (Real.log 2) ^ 2 / (2 * π) * (n * w)) :
    closure (D.piece n) ⊆
      closedBall c (8 * R * Real.exp (-((Real.log 2) ^ 2 / (2 * π) * (n * w)))) := by
  refine D.closure_piece_subset_closedBall_of_sum hR hR' ?_ hn
  have hsum : ∑ _j ∈ Finset.range n, ENNReal.ofReal w = ENNReal.ofReal (n * w) := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast]
  rw [← hsum]
  exact Finset.sum_le_sum fun j _ => hmod j

/-- **Nests with uniform collars shrink exponentially.** If every annulus `Pⱼ ∖ cl P_{j+1}` has a
collar of dilatation at most `K₀` and modulus at least `μ₀ / 2π`, the pieces shrink at the rate
`exp (−κ μ₀ n / (2π K₀))`, `κ = (log 2)² / 2π`: bounded geometry gives a geometric decay of the
diameters. -/
theorem closure_piece_subset_closedBall_of_collars {R K₀ μ₀ : ℝ} (hR : 0 < R)
    (hR' : closure (D.piece 0) ⊆ closedBall c R) (hK₀ : 0 < K₀) (hμ₀ : 0 < μ₀)
    (h : ∀ j, ∃ Kd r R' : ℝ, Kd ≤ K₀ ∧ μ₀ ≤ Real.log (R' / r) ∧
      IsCollar (closure (D.piece (j + 1))) (D.piece j) Kd r R') {n : ℕ}
    (hn : Real.log 8 ≤ (Real.log 2) ^ 2 / (2 * π) * (n * (μ₀ / (2 * π) / K₀))) :
    closure (D.piece n) ⊆ closedBall c
      (8 * R * Real.exp (-((Real.log 2) ^ 2 / (2 * π) * (n * (μ₀ / (2 * π) / K₀))))) := by
  exact D.closure_piece_subset_closedBall_of_uniform hR hR' (w := μ₀ / (2 * π) / K₀)
    (D.ofReal_le_extWidth_loops_of_collars hK₀ hμ₀ h) hn

end ConnectedNest

end

end MLC.Research
