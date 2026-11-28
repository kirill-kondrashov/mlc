import Mlc.Research.Collar
import Mlc.Research.Dimension
import Mlc.Research.LevelTower
import Mlc.Research.NestRate

/-!
# The Yoccoz criterion in modulus form, with a logarithmic scale

The modules `NestModulus.lean`, `Collar.lean`, `NestRate.lean` and `LevelTower.lean` prove the
steps from a geometric hypothesis on the annuli of a nest to the shrinking of its pieces. This
module closes the chain at a point: the shrinking gives the local connectivity at the center of the
nest, with a scale that is logarithmic in the size of the neighbourhood.

* **Theorem `ConnectedNest.exists_closure_piece_subset_ball_of_uniform`**: if every annulus of a nest
  has modulus at least `w`, and the closure of the first piece lies in the disk of radius `R`
  around `c`, then for every `ε > 0` the closure of the piece `n` lies in the disk of radius `ε`,
  for some `n ≤ max (log 8, log (8R/ε)) / (κ w) + 1`, `κ = (log 2)² / 2π`. The depth grows like
  `log (1/ε)` (`NestRate.lean`).
* **Theorems `ConnectedNest.locallyConnectedAt_of_divergent`,
  `ConnectedNest.locallyConnectedAt_of_uniform`**: the set is locally connected at the center of
  a nest whose moduli add up to infinity (the Yoccoz criterion), in particular when the moduli of
  the annuli have a uniform lower bound, and
  `ConnectedNest.exists_relativePiece_of_uniform` gives, in that case, the connected
  neighbourhoods at depth `O (log (1/ε))` (the *logarithmic modulus of local connectivity*).
* **Theorems `ConnectedNest.locallyConnectedAt_of_collars`,
  `ConnectedNest.exists_relativePiece_of_collars`**: the same when every annulus has a collar of
  dilatation at most `K₀` and modulus at least `μ₀ / 2π`, with `w = μ₀ / (2π K₀)`
  (`Collar.lean`).
* **Theorems `Geometry.locallyConnectedAt_of_comparison`,
  `Geometry.exists_relativePiece_of_comparison`**: Lemma T in its pointwise and quantitative
  form: given the phase–parameter comparison of moduli (`LevelTower.lean`), a degeneration bound
  `B` at a parameter `c` of `M` gives the local connectivity of `M` at `c`, with connected
  neighbourhoods at depth `B Kd · O (log (1/ε))`.
* **Theorem `Geometry.locallyConnectedAt_of_collars_and_comparison`**: the whole chain in one
  statement. Collars of bounded dilatation and definite modulus at the jumps of a level tower of
  `c`, the linear dichotomy for that tower, and the phase–parameter comparison give the local
  connectivity of `M` at `c`; `Geometry.locallyConnectedAt_of_tails_collars_and_comparison` is the
  form that follows the three lemmas of Problem 4.3: the Teichmüller contraction for the tower
  (TC′), collars at the jumps at the levels of large relative period (G), the linear dichotomy
  (D), and the comparison. These hypotheses are explicit geometric statements: the
  collars are the content proposed for the pseudo-Siegel disks (sub-step PS4), the linear
  dichotomy is Lemma D, and the comparison is the phase–parameter relation in moduli form. None of
  them is proved here.
* **`IsCollar.round`, `concentricNest_collars`**: a round annulus is its own collar, and the
  concentric nest has uniform collars of dilatation `1` and modulus `log (3/2) / 2π`, so the
  hypotheses of the criterion are satisfiable.

The criterion is the Yoccoz scheme with the divergence of the moduli replaced by a uniform
lower bound: a nest whose moduli add up to infinity shrinks (`DivergentModuli.shrinking`), and
the local connectivity follows from the shrinking of connected neighbourhoods
(`ConnectedNest.locallyConnectedAt_of_singleton`). The uniform bound adds the rate.
-/

namespace MLC.Research

open MeasureTheory ENNReal Set Real Topology Metric

noncomputable section

namespace ConnectedNest

variable {S : Set ℂ} {c : ℂ} (D : ConnectedNest S c)

/-- The closure of the first piece of a nest lies in a disk around its point. -/
lemma exists_radius : ∃ R : ℝ, 0 < R ∧ closure (D.piece 0) ⊆ closedBall c R := by
  obtain ⟨R, hR⟩ := (D.compact_closure 0).isBounded.subset_closedBall c
  exact ⟨max R 1, lt_of_lt_of_le one_pos (le_max_right _ _),
    hR.trans (closedBall_subset_closedBall (le_max_left _ _))⟩

/-- **A uniform lower bound for the moduli gives a logarithmic scale.** If every annulus of the nest
has modulus at least `w`, and the closure of the first piece lies in the disk of radius `R` around
`c`, then for every `ε > 0` the closure of the piece `n` lies in the disk of radius `ε` around `c`,
for some `n` that is at most `max (log 8) (log (8R/ε)) / (κ w) + 1`, `κ = (log 2)² / 2π`. -/
theorem exists_closure_piece_subset_ball_of_uniform {R w ε : ℝ} (hR : 0 < R)
    (hR' : closure (D.piece 0) ⊆ closedBall c R) (hw : 0 < w)
    (hmod : ∀ j, ENNReal.ofReal w ≤ extWidth volume (D.loops j)) (hε : 0 < ε) :
    ∃ n : ℕ, (n : ℝ) ≤
        max (Real.log 8) (Real.log (8 * R / ε)) / ((Real.log 2) ^ 2 / (2 * π) * w) + 1 ∧
      closure (D.piece n) ⊆ ball c ε := by
  set κ : ℝ := (Real.log 2) ^ 2 / (2 * π) with hκ
  have hκpos : 0 < κ := div_pos (pow_pos (Real.log_pos one_lt_two) 2) (by positivity)
  have hκw : 0 < κ * w := mul_pos hκpos hw
  set T : ℝ := max (Real.log 8) (Real.log (8 * R / ε)) with hT
  have hT8 : Real.log 8 ≤ T := le_max_left _ _
  have hTε : Real.log (8 * R / ε) ≤ T := le_max_right _ _
  have h8 : 0 < Real.log 8 := Real.log_pos (by norm_num)
  have hq : 0 ≤ T / (κ * w) := div_nonneg (h8.le.trans hT8) hκw.le
  refine ⟨⌊T / (κ * w)⌋₊ + 1, ?_, ?_⟩
  · push_cast
    linarith [Nat.floor_le hq]
  · set N : ℕ := ⌊T / (κ * w)⌋₊ + 1 with hN
    have hNgt : T / (κ * w) < N := by
      rw [hN]
      push_cast
      exact Nat.lt_floor_add_one _
    have hNT : T < κ * (N * w) := by
      have := (div_lt_iff₀ hκw).1 hNgt
      linarith
    have hn : Real.log 8 ≤ κ * (N * w) := hT8.trans hNT.le
    refine (D.closure_piece_subset_closedBall_of_uniform hR hR' hmod hn).trans
      (closedBall_subset_ball ?_)
    have h1 : 8 * R / ε < Real.exp (κ * (N * w)) :=
      (Real.log_lt_iff_lt_exp (by positivity)).1 (hTε.trans_lt hNT)
    rw [div_lt_iff₀ hε] at h1
    rw [Real.exp_neg, ← div_eq_mul_inv, div_lt_iff₀ (Real.exp_pos _)]
    linarith

/-- **The Yoccoz criterion.** A set is locally connected at the center of a connected nest whose
moduli add up to infinity: the nest shrinks to its center
(`ConnectedNest.kernel_eq_singleton_of_divergent`), and the connected neighbourhoods then form a
basis. -/
theorem locallyConnectedAt_of_divergent (hc : c ∈ S) (h : D.DivergentModuli) :
    LocallyConnectedAtSet S ⟨c, hc⟩ :=
  D.locallyConnectedAt_of_singleton hc (kernel_eq_singleton_of_divergent h)

/-- **The Yoccoz criterion with a uniform modulus.** A set is locally connected at the center of a
connected nest whose annuli have moduli bounded below by a positive number. -/
theorem locallyConnectedAt_of_uniform (hc : c ∈ S) {w : ℝ} (hw : 0 < w)
    (hmod : ∀ j, ENNReal.ofReal w ≤ extWidth volume (D.loops j)) :
    LocallyConnectedAtSet S ⟨c, hc⟩ :=
  D.locallyConnectedAt_of_divergent hc
    (D.divergentModuli_of_uniform (ENNReal.ofReal_pos.2 hw).ne' hmod)

/-- **The logarithmic modulus of local connectivity.** If every annulus of the nest has modulus at
least `w` and the closure of the first piece lies in the disk of radius `R` around `c`, then for
every `ε > 0` the relative piece `n` is a connected neighbourhood of `c` in `S` inside the disk of
radius `ε`, for some depth `n` that is at most `max (log 8) (log (8R/ε)) / (κ w) + 1`. -/
theorem exists_relativePiece_of_uniform (hc : c ∈ S) {R w ε : ℝ} (hR : 0 < R)
    (hR' : closure (D.piece 0) ⊆ closedBall c R) (hw : 0 < w)
    (hmod : ∀ j, ENNReal.ofReal w ≤ extWidth volume (D.loops j)) (hε : 0 < ε) :
    ∃ n : ℕ, (n : ℝ) ≤
        max (Real.log 8) (Real.log (8 * R / ε)) / ((Real.log 2) ^ 2 / (2 * π) * w) + 1 ∧
      IsPreconnected (D.relativePiece n) ∧ D.relativePiece n ∈ 𝓝 (⟨c, hc⟩ : S) ∧
      D.relativePiece n ⊆ Subtype.val ⁻¹' ball c ε := by
  obtain ⟨n, hn, hball⟩ := D.exists_closure_piece_subset_ball_of_uniform hR hR' hw hmod hε
  exact ⟨n, hn, D.relativePiece_preconnected n, D.relativePiece_mem_nhds hc n,
    fun z hz => hball (subset_closure (show (z : ℂ) ∈ D.piece n from hz))⟩

/-- **The Yoccoz criterion with uniform collars.** A set is locally connected at the center of a
connected nest whose annuli `Pⱼ ∖ cl P_{j+1}` all have collars of dilatation at most `K₀` and
modulus at least `μ₀ / 2π`. -/
theorem locallyConnectedAt_of_collars (hc : c ∈ S) {K₀ μ₀ : ℝ} (hK₀ : 0 < K₀) (hμ₀ : 0 < μ₀)
    (h : ∀ j, ∃ Kd r R : ℝ, Kd ≤ K₀ ∧ μ₀ ≤ Real.log (R / r) ∧
      IsCollar (closure (D.piece (j + 1))) (D.piece j) Kd r R) :
    LocallyConnectedAtSet S ⟨c, hc⟩ :=
  D.locallyConnectedAt_of_uniform hc (w := μ₀ / (2 * π) / K₀) (by positivity)
    (D.ofReal_le_extWidth_loops_of_collars hK₀ hμ₀ h)

/-- **Uniform collars give the logarithmic modulus of local connectivity.** With the collars of
`locallyConnectedAt_of_collars` and the closure of the first piece in the disk of radius `R`
around `c`, for every `ε > 0` the relative piece `n` is a connected neighbourhood of `c` in `S`
inside the disk of radius `ε`, for some `n` at most
`max (log 8) (log (8R/ε)) / (κ μ₀ / (2π K₀)) + 1`. -/
theorem exists_relativePiece_of_collars (hc : c ∈ S) {K₀ μ₀ R ε : ℝ} (hK₀ : 0 < K₀)
    (hμ₀ : 0 < μ₀) (hR : 0 < R) (hR' : closure (D.piece 0) ⊆ closedBall c R)
    (h : ∀ j, ∃ Kd r R : ℝ, Kd ≤ K₀ ∧ μ₀ ≤ Real.log (R / r) ∧
      IsCollar (closure (D.piece (j + 1))) (D.piece j) Kd r R) (hε : 0 < ε) :
    ∃ n : ℕ, (n : ℝ) ≤ max (Real.log 8) (Real.log (8 * R / ε)) /
        ((Real.log 2) ^ 2 / (2 * π) * (μ₀ / (2 * π) / K₀)) + 1 ∧
      IsPreconnected (D.relativePiece n) ∧ D.relativePiece n ∈ 𝓝 (⟨c, hc⟩ : S) ∧
      D.relativePiece n ⊆ Subtype.val ⁻¹' ball c ε :=
  D.exists_relativePiece_of_uniform hc hR hR' (by positivity)
    (D.ofReal_le_extWidth_loops_of_collars hK₀ hμ₀ h) hε

end ConnectedNest

namespace Geometry

variable (G : Geometry)

/-- **Lemma T, pointwise.** Given the phase–parameter comparison of moduli, a degeneration bound at
a parameter `c` of `M` gives the local connectivity of `M` at `c`. -/
theorem locallyConnectedAt_of_comparison (h : G.PhaseParameterComparison) {c : ℂ}
    (hc : c ∈ MLC.Quadratic.MandelbrotSet) {B : ℝ} (hB : 0 < B) (hbound : G.HasBound c B) :
    LocallyConnectedAtSet MLC.Quadratic.MandelbrotSet ⟨c, hc⟩ := by
  obtain ⟨D, Kd, hKd, hmod⟩ := G.uniformNest_of_comparison h hc hB hbound
  exact D.locallyConnectedAt_of_uniform hc (by positivity) hmod

/-- **Lemma T with a logarithmic scale.** Given the phase–parameter comparison of moduli with the
constant `Kd`, a degeneration bound `B` at a parameter `c` of `M` gives a nest around `c`, with the
closure of its first piece in the disk of radius `R`, such that for every `ε > 0` some relative
piece at depth at most `max (log 8) (log (8R/ε)) / (κ / (B Kd)) + 1` is a connected neighbourhood
of `c` in `M` inside the disk of radius `ε`. -/
theorem exists_relativePiece_of_comparison (h : G.PhaseParameterComparison) {c : ℂ}
    (hc : c ∈ MLC.Quadratic.MandelbrotSet) {B : ℝ} (hB : 0 < B) (hbound : G.HasBound c B) :
    ∃ (D : ConnectedNest MLC.Quadratic.MandelbrotSet c) (Kd R : ℝ), 0 < Kd ∧ 0 < R ∧
      ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, (n : ℝ) ≤ max (Real.log 8) (Real.log (8 * R / ε)) /
          ((Real.log 2) ^ 2 / (2 * π) * (B⁻¹ / Kd)) + 1 ∧
        IsPreconnected (D.relativePiece n) ∧
        D.relativePiece n ∈ 𝓝 (⟨c, hc⟩ : MLC.Quadratic.MandelbrotSet) ∧
        D.relativePiece n ⊆ Subtype.val ⁻¹' ball c ε := by
  obtain ⟨D, Kd, hKd, hmod⟩ := G.uniformNest_of_comparison h hc hB hbound
  obtain ⟨R, hR, hR'⟩ := D.exists_radius
  exact ⟨D, Kd, R, hKd, hR, fun ε hε =>
    D.exists_relativePiece_of_uniform hc hR hR' (by positivity) hmod hε⟩

/-- **A priori bounds and the comparison give local connectivity.** If the level tower of `c` has
a priori bounds, the phase–parameter comparison of moduli gives the local connectivity of `M`
at `c`. -/
theorem locallyConnectedAt_of_aPrioriBounds (h : G.PhaseParameterComparison) {c : ℂ}
    (hc : c ∈ MLC.Quadratic.MandelbrotSet) (L : LevelTower)
    (hL : G.tower c = some L.toWidthTower) (hB : L.APrioriBounds) :
    LocallyConnectedAtSet MLC.Quadratic.MandelbrotSet ⟨c, hc⟩ := by
  obtain ⟨B, hB⟩ := hB
  have hB' : 0 < max B 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  exact G.locallyConnectedAt_of_comparison h hc hB'
    ⟨hB', _, hL, fun k => (hB k).trans (le_max_left _ _)⟩

/-- **The chain from collars to local connectivity.** Collars of dilatation at most `K₀` and modulus
at least `μ₀ / 2π` at the levels that follow a jump of the degeneration by the factor `C₀` of a
level tower of `c`, the linear dichotomy for that tower, and the phase–parameter comparison of
moduli give the local connectivity of `M` at `c`. The hypotheses are the content proposed for the
sub-step PS4 (collars), Lemma D, and the phase–parameter relation; none of them is proved. -/
theorem locallyConnectedAt_of_collars_and_comparison (h : G.PhaseParameterComparison) {c : ℂ}
    (hc : c ∈ MLC.Quadratic.MandelbrotSet) (L : LevelTower)
    (hL : G.tower c = some L.toWidthTower) {C₀ K₀ μ₀ : ℝ} (hC₀ : 0 < C₀) (hK₀ : 0 < K₀)
    (hμ₀ : 0 < μ₀)
    (hcol : ∀ m, L.Jumps C₀ m → ∃ Kd r R : ℝ, Kd ≤ K₀ ∧ μ₀ ≤ Real.log (R / r) ∧
      IsCollar (L.filled (m + 1)) (L.target (m + 1)) Kd r R)
    (hD : L.LinearDichotomy) :
    LocallyConnectedAtSet MLC.Quadratic.MandelbrotSet ⟨c, hc⟩ :=
  G.locallyConnectedAt_of_aPrioriBounds h hc L hL
    (L.aPrioriBounds_of_collars hC₀ hK₀ hμ₀ hcol hD)

/-- **The three lemmas of Problem 4.3 and the comparison give local connectivity.** The
Teichmüller contraction for the tower of `c` (Lemma TC′), collars of dilatation at most `K₀` and
modulus at least `μ₀ / 2π` at the jumps at the levels of large relative period (Lemma G, in the
reading of PS4), the dichotomy with a linear error (Lemma D), and the phase–parameter comparison of
moduli give the local connectivity of `M` at `c`. None of the hypotheses is proved here. -/
theorem locallyConnectedAt_of_tails_collars_and_comparison (h : G.PhaseParameterComparison)
    {c : ℂ} (hc : c ∈ MLC.Quadratic.MandelbrotSet) (L : LevelTower)
    (hL : G.tower c = some L.toWidthTower) {P₀ : ℕ} {C₀ K₀ μ₀ : ℝ} (hC₀ : 0 < C₀)
    (hK₀ : 0 < K₀) (hμ₀ : 0 < μ₀) (hT : L.Teichmuller)
    (hcol : ∀ m, P₀ < L.rel m → L.Jumps C₀ m → ∃ Kd r R : ℝ, Kd ≤ K₀ ∧
      μ₀ ≤ Real.log (R / r) ∧ IsCollar (L.filled (m + 1)) (L.target (m + 1)) Kd r R)
    (hD : L.LinearDichotomy) :
    LocallyConnectedAtSet MLC.Quadratic.MandelbrotSet ⟨c, hc⟩ :=
  G.locallyConnectedAt_of_aPrioriBounds h hc L hL
    (L.aPrioriBounds_of_tails_collars hC₀ hK₀ hμ₀ hT hcol hD)

end Geometry

/-! ### The hypotheses of the criterion are satisfiable -/

/-- **A round annulus is its own collar.** For `r < R' < R` the identity chart is a collar of the
annulus `B(c, R) ∖ B̄(c, r)` of dilatation `1` and modulus `log (R'/r) / 2π`. -/
lemma IsCollar.round {c : ℂ} {r R R' : ℝ} (hr : 0 < r) (hrR' : r < R') (hR'R : R' < R) :
    IsCollar (closedBall c r) (ball c R) 1 r R' :=
  ⟨one_pos, hr, hrR', univ, id, c,
    QcEmbedding.of_holomorphic isOpen_univ differentiableOn_id (injOn_id _) fun z _ => by simp,
    measurable_id, subset_univ _, by simp, by simpa using closedBall_subset_ball hR'R⟩

/-- **The concentric nest has uniform collars.** Every annulus `B(0, 2⁻ʲ) ∖ B̄(0, 2^{-(j+1)})` has a
collar of dilatation `1` and modulus `log (3/2) / 2π`, so the hypotheses of
`ConnectedNest.locallyConnectedAt_of_collars` are satisfiable. -/
theorem concentricNest_collars (j : ℕ) :
    ∃ Kd r R : ℝ, Kd ≤ 1 ∧ Real.log (3 / 2) ≤ Real.log (R / r) ∧
      IsCollar (closure (concentricNest.piece (j + 1))) (concentricNest.piece j) Kd r R := by
  have hr : 0 < (1 / 2 : ℝ) ^ (j + 1) := by positivity
  have hpow : (1 / 2 : ℝ) ^ j = 2 * (1 / 2 : ℝ) ^ (j + 1) := by
    rw [pow_succ]
    ring
  refine ⟨1, (1 / 2 : ℝ) ^ (j + 1), 3 / 2 * (1 / 2 : ℝ) ^ (j + 1), le_rfl, ?_, ?_⟩
  · rw [mul_div_cancel_right₀ _ hr.ne']
  · have hcl : closure (concentricNest.piece (j + 1)) = closedBall 0 ((1 / 2 : ℝ) ^ (j + 1)) :=
      closure_ball _ hr.ne'
    rw [hcl]
    exact IsCollar.round (R := (1 / 2 : ℝ) ^ j) hr (by linarith) (by rw [hpow]; linarith)

end

end MLC.Research
