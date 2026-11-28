import Mlc.Research.Collar
import Mlc.Research.PhaseParameter
import Mlc.Research.RoundAnnulus

/-!
# The levels of a tower as annuli

The abstract degeneration `W_k` of a `WidthTower` (`Mlc/Research/Degeneration.lean`) is, in the
survey (3.2), (4.1), the reciprocal `W(f) = 1 / mod⁺(f)` of the modulus `mod⁺(f) = mod(V ∖ K_f)` of
the annulus between the filled Julia set and the range domain of a quadratic-like level
`f : U → V`. This module records that dictionary in the language of extremal widths, with the
modulus of an annulus taken as the extremal width of the `C¹` loops in it that separate the inner
set from the complement of the outer one. That width is at most the classical modulus and equals it
for round annuli (`RoundAnnulus.lean`); its equality with the classical modulus in general belongs to
the dictionary and is not proved. The module proves what follows from the quasi-monotonicity of the
modulus (`Mlc/Research/Collar.lean`).

* **Structure `LevelTower`**: a `WidthTower` with sets `filled k` (the filled Julia set of the level
  `k`) and `target k` (its range domain `V_k`) such that `W_k = 1 / mod(V_k ∖ K_k)`, where the
  modulus of an annulus is the extremal width of the `C¹` loops in it that separate the inner set
  from the complement of the outer one. The sets are data of the dictionary: nothing in the
  structure ties them to the dynamics of `f_c`, and every width tower is realized by round levels
  (`RoundTower.lean`), so the structure has no dynamical content by itself. The circles of a round
  annulus lie in that family, so its
  modulus is at least `log (R/r) / 2π` (`extWidth_loopFamily_ge_radii`), and it is at most the
  classical modulus in general, since the family consists of separating curves. For a round level
  `filled = B̄(c, r)`, `target = B(c, R)` it is exactly `log (R/r) / 2π`
  (`LevelTower.width_eq_of_round`, from `RoundAnnulus.lean`), so the degeneration of a round level
  is `2π / log (R/r)`.
* **Theorem `LevelTower.width_le_of_collar`**: a collar of dilatation `Kd` and modulus
  `log (R/r) / 2π` in the annulus of a level bounds its degeneration by `2π Kd / log (R/r)`.
* **Theorem `LevelTower.jumpCap_of_collars`** (Lemma G from uniform collars): if at every level that
  follows a jump of the degeneration by the factor `C₀` the annulus has a collar of dilatation at
  most `K₀` and modulus at least `μ₀ / 2π`, the jumps are capped by `2π K₀ / μ₀`. This is the
  reading of the sub-step PS4 of the programme (the invariant degeneration, absorbed by the
  pseudo-Siegel disks, "is bounded by their uniform quasi-conformal geometry") as a precise
  geometric hypothesis with a proved consequence. That the pseudo-Siegel disks give collars at the
  jumps is the proposed content; the same theorem applies to the virtual levels of Lemma VG2.
  `LevelTower.aPrioriBounds_of_collars` adds the linear dichotomy and gives a priori bounds.
* **Theorem `Geometry.transfer_of_comparison`** (Lemma T from the phase–parameter comparison): the
  statement `Geometry.PhaseParameterComparison` asks, from a degeneration bound on the tower of `c`,
  for a realization of the tower by the annuli of its levels and for a connected nest in `M` around
  `c` such that the modulus of the annulus of each level is at most a fixed multiple `Kd` of the
  modulus of the corresponding annulus of the nest. It is the form in which Lyubich's
  phase–parameter relation is used at the renormalization levels, and a quasi-conformal chart from
  the dynamical annulus to the parameter annulus gives it (for a `C¹` chart this is
  `extWidth_loopFamily_le_map`). Given it, the moduli of the nest are bounded below by `1 / (B Kd)`,
  so they add up to infinity and the pieces shrink (`ConnectedNest.nonempty_parameterRealization`).

Nothing here constructs the levels of a tower from a parameter, the collars, or the nest and the
chart of the comparison; these are the open parts, and `Geometry.PhaseParameterComparison` is not a
field of the root input (the root keeps `Geometry.Transfer`). The comparison is a statement about
the dictionary: it is vacuous for a dictionary whose towers are all absent, and, for a dictionary
whose level sets are not the dynamical ones, it is a numerical comparison of widths with no
dynamical meaning.
-/

namespace MLC.Research

open MeasureTheory ENNReal Set Real

noncomputable section

/-- **A tower whose degeneration is the reciprocal modulus of an annulus.** The level `k` is a
quadratic-like map `f_k : U_k → V_k`; `filled k` is its filled Julia set `K_{f_k}` and `target k`
is `V_k`. The degeneration of the level is `W(f_k) = 1 / mod⁺(f_k)` with
`mod⁺(f_k) = mod(V_k ∖ K_{f_k})` (the survey (3.2), (4.1)), where the modulus of an annulus is the
extremal width of the `C¹` loops in it that separate the inner set from the complement of the
outer one. -/
structure LevelTower extends WidthTower where
  filled : ℕ → Set ℂ
  target : ℕ → Set ℂ
  width_eq : ∀ k, ENNReal.ofReal (width k) =
    (extWidth volume (loopFamily (target k \ filled k) (filled k) (target k)))⁻¹

namespace LevelTower

variable (T : LevelTower)

/-- The modulus `mod⁺(f_k)` of the level `k`. -/
def modulus (k : ℕ) : ℝ≥0∞ :=
  extWidth volume (loopFamily (T.target k \ T.filled k) (T.filled k) (T.target k))

lemma modulus_eq (k : ℕ) : T.modulus k = (ENNReal.ofReal (T.width k))⁻¹ := by
  rw [T.width_eq k, inv_inv]
  rfl

/-- **The degeneration of a round level is the reciprocal of the classical modulus.** If the filled
set of the level `k` is the closed disk `B̄(c, r)` and its range domain is the disk `B(c, R)`, the
degeneration of the level is `2π / log (R/r)`: the dictionary is exact on the round annuli. -/
theorem width_eq_of_round {k : ℕ} {c : ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hf : T.filled k = Metric.closedBall c r) (ht : T.target k = Metric.ball c R) :
    T.width k = 2 * π / Real.log (R / r) := by
  have hlog : 0 < Real.log (R / r) := Real.log_pos ((one_lt_div hr).2 hrR)
  have h := T.width_eq k
  rw [hf, ht, extWidth_loopFamily_round_open hr hrR,
    ← ENNReal.ofReal_inv_of_pos (div_pos hlog (by positivity)), inv_div] at h
  exact (ENNReal.ofReal_eq_ofReal_iff (T.width_pos k).le (by positivity)).1 h

/-- **A collar bounds the degeneration of a level.** If the annulus of the level `k` has a collar of
dilatation `Kd` and modulus `log (R/r) / 2π`, its degeneration is at most `2π Kd / log (R/r)`. -/
theorem width_le_of_collar {k : ℕ} {Kd r R : ℝ}
    (h : IsCollar (T.filled k) (T.target k) Kd r R) :
    T.width k ≤ 2 * π * Kd / Real.log (R / r) := by
  have hKd : 0 < Kd := h.1
  have hlog : 0 < Real.log (R / r) := Real.log_pos ((one_lt_div h.2.1).2 h.2.2.1)
  have ha : 0 < Real.log (R / r) / (2 * π) / Kd := by positivity
  have hcol : ENNReal.ofReal (Real.log (R / r) / (2 * π) / Kd) ≤ T.modulus k :=
    h.ofReal_le_extWidth
  have h1 : ENNReal.ofReal (T.width k) ≤ ENNReal.ofReal (2 * π * Kd / Real.log (R / r)) := by
    calc ENNReal.ofReal (T.width k) = (T.modulus k)⁻¹ := by rw [T.modulus_eq k, inv_inv]
      _ ≤ (ENNReal.ofReal (Real.log (R / r) / (2 * π) / Kd))⁻¹ := ENNReal.inv_le_inv.2 hcol
      _ = ENNReal.ofReal ((Real.log (R / r) / (2 * π) / Kd)⁻¹) :=
          (ENNReal.ofReal_inv_of_pos ha).symm
      _ = ENNReal.ofReal (2 * π * Kd / Real.log (R / r)) := by
          congr 1
          field_simp
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h1

/-- **Lemma G from uniform collars.** If at every level `m + 1` that follows a jump of the
degeneration by the factor `C₀` the annulus has a collar of dilatation at most `K₀` and modulus at
least `μ₀ / 2π`, the jumps are capped by the ceiling `2π K₀ / μ₀`. The ceiling is the degeneration
of a round annulus of modulus `μ₀ / 2π` times the dilatation `K₀` of the chart: the invariant
degeneration is bounded by the uniform quasi-conformal geometry of the collars. -/
theorem jumpCap_of_collars {C₀ K₀ μ₀ : ℝ} (hK₀ : 0 < K₀) (hμ₀ : 0 < μ₀)
    (h : ∀ m, T.Jumps C₀ m → ∃ Kd r R : ℝ, Kd ≤ K₀ ∧ μ₀ ≤ Real.log (R / r) ∧
      IsCollar (T.filled (m + 1)) (T.target (m + 1)) Kd r R) :
    T.JumpCap C₀ (2 * π * K₀ / μ₀) := by
  intro m hm
  obtain ⟨Kd, r, R, hKd, hμ, hcol⟩ := h m hm
  refine (T.width_le_of_collar hcol).trans ?_
  have hKd0 : 0 < Kd := hcol.1
  have hlog : 0 < Real.log (R / r) := hμ₀.trans_le hμ
  calc 2 * π * Kd / Real.log (R / r) ≤ 2 * π * K₀ / Real.log (R / r) := by gcongr
    _ ≤ 2 * π * K₀ / μ₀ := by gcongr

/-- **A priori bounds from collars at the jumps.** Collars of bounded dilatation and definite
modulus at the levels that follow a jump, and the dichotomy with an additive error at most linear in
the period, give a priori bounds for the tower. -/
theorem aPrioriBounds_of_collars {C₀ K₀ μ₀ : ℝ} (hC₀ : 0 < C₀) (hK₀ : 0 < K₀) (hμ₀ : 0 < μ₀)
    (h : ∀ m, T.Jumps C₀ m → ∃ Kd r R : ℝ, Kd ≤ K₀ ∧ μ₀ ≤ Real.log (R / r) ∧
      IsCollar (T.filled (m + 1)) (T.target (m + 1)) Kd r R)
    (hD : T.LinearDichotomy) : T.APrioriBounds :=
  T.aPrioriBounds_of_jumpCap hC₀ (T.jumpCap_of_collars hK₀ hμ₀ h) hD

/-- **Lemma G at the levels of large relative period from collars.** If at every level `m + 1` that
follows a jump by the factor `C₀` at a level `m` of relative period above `P₀` the annulus has a
collar of dilatation at most `K₀` and modulus at least `μ₀ / 2π`, the jumps at the levels of large
relative period are capped by the ceiling `2π K₀ / μ₀`. -/
theorem largePeriodJumpCap_of_collars {P₀ : ℕ} {C₀ K₀ μ₀ : ℝ} (hK₀ : 0 < K₀) (hμ₀ : 0 < μ₀)
    (h : ∀ m, P₀ < T.rel m → T.Jumps C₀ m → ∃ Kd r R : ℝ, Kd ≤ K₀ ∧
      μ₀ ≤ Real.log (R / r) ∧ IsCollar (T.filled (m + 1)) (T.target (m + 1)) Kd r R) :
    T.LargePeriodJumpCap P₀ C₀ (2 * π * K₀ / μ₀) := by
  intro m hm hj
  obtain ⟨Kd, r, R, hKd, hμ, hcol⟩ := h m hm hj
  refine (T.width_le_of_collar hcol).trans ?_
  have hKd0 : 0 < Kd := hcol.1
  have hlog : 0 < Real.log (R / r) := hμ₀.trans_le hμ
  calc 2 * π * Kd / Real.log (R / r) ≤ 2 * π * K₀ / Real.log (R / r) := by gcongr
    _ ≤ 2 * π * K₀ / μ₀ := by gcongr

/-- **A priori bounds from the three lemmas of Problem 4.3, with Lemma G as collars.** The
Teichmüller contraction (Lemma TC′), collars of bounded dilatation and definite modulus at the
jumps at the levels of large relative period (Lemma G, in the reading of PS4), and the dichotomy
with an additive error at most linear in the period (Lemma D) give a priori bounds. -/
theorem aPrioriBounds_of_tails_collars {P₀ : ℕ} {C₀ K₀ μ₀ : ℝ} (hC₀ : 0 < C₀) (hK₀ : 0 < K₀)
    (hμ₀ : 0 < μ₀) (hT : T.Teichmuller)
    (h : ∀ m, P₀ < T.rel m → T.Jumps C₀ m → ∃ Kd r R : ℝ, Kd ≤ K₀ ∧
      μ₀ ≤ Real.log (R / r) ∧ IsCollar (T.filled (m + 1)) (T.target (m + 1)) Kd r R)
    (hD : T.LinearDichotomy) : T.APrioriBounds :=
  T.aPrioriBounds_of_tails hC₀ hT (T.largePeriodJumpCap_of_collars hK₀ hμ₀ h) hD

end LevelTower

/-! ### The phase–parameter comparison -/

namespace Geometry

variable (G : Geometry)

/-- **The phase–parameter comparison of moduli.** An a priori bound on the degeneration of the tower
of `c` gives a realization of the tower by the annuli `V_k ∖ K_{f_k}` of its levels, and a connected
nest in `M` around `c`, such that the modulus of the annulus of each level is at most a fixed
multiple `Kd` of the modulus of the corresponding annulus of the nest. This is the form in which
the phase–parameter relation of Lyubich is used for the renormalization levels (a quasi-conformal
chart from the dynamical annulus to the parameter annulus gives it, for a `C¹` chart by
`extWidth_loopFamily_le_map`); its construction is what is open. -/
def PhaseParameterComparison : Prop :=
  ∀ c ∈ MLC.Quadratic.MandelbrotSet, ∀ (B : ℝ) (_ : 0 < B), G.HasBound c B →
    ∃ (L : LevelTower) (D : ConnectedNest MLC.Quadratic.MandelbrotSet c) (Kd : ℝ), 0 < Kd ∧
      G.tower c = some L.toWidthTower ∧
      ∀ k, L.modulus k ≤ ENNReal.ofReal Kd * extWidth volume (D.loops k)

/-- **The comparison gives a nest whose annuli have a definite modulus.** The levels of a tower with
a degeneration bound `B` have moduli at least `1/B`, and the comparison gives a connected nest in
`M` around `c` whose annuli have moduli at least `1 / (B Kd)`, for the constant `Kd` of the
comparison. -/
theorem uniformNest_of_comparison (h : G.PhaseParameterComparison) {c : ℂ}
    (hc : c ∈ MLC.Quadratic.MandelbrotSet) {B : ℝ} (hB : 0 < B) (hbound : G.HasBound c B) :
    ∃ (D : ConnectedNest MLC.Quadratic.MandelbrotSet c) (Kd : ℝ), 0 < Kd ∧
      ∀ k, ENNReal.ofReal (B⁻¹ / Kd) ≤ extWidth volume (D.loops k) := by
  obtain ⟨L, D, Kd, hKd, hL, hcmp⟩ := h c hc B hB hbound
  obtain ⟨-, T, hT, hle⟩ := hbound
  have hTL : T = L.toWidthTower := Option.some.inj (hT.symm.trans hL)
  subst hTL
  refine ⟨D, Kd, hKd, fun k => ?_⟩
  have h1 : ENNReal.ofReal B⁻¹ ≤ L.modulus k := by
    rw [L.modulus_eq k]
    calc ENNReal.ofReal B⁻¹ = (ENNReal.ofReal B)⁻¹ := ENNReal.ofReal_inv_of_pos hB
      _ ≤ (ENNReal.ofReal (L.width k))⁻¹ := ENNReal.inv_le_inv.2 (ENNReal.ofReal_le_ofReal (hle k))
  rw [ENNReal.ofReal_div_of_pos hKd]
  exact ENNReal.div_le_of_le_mul' (h1.trans (hcmp k))

/-- **Lemma T from the phase–parameter comparison.** The levels of a tower with a degeneration
bound `B` have moduli at least `1/B`, the comparison gives moduli of the annuli of the nest at
least `1 / (B Kd)`, so they add up to infinity and the pieces shrink to `c`
(`ConnectedNest.nonempty_parameterRealization`). -/
theorem transfer_of_comparison (h : G.PhaseParameterComparison) : G.Transfer := by
  intro c hc B hB hbound
  obtain ⟨D, Kd, hKd, hmod⟩ := G.uniformNest_of_comparison h hc hB hbound
  exact D.nonempty_parameterRealization (D.divergentModuli_of_uniform
    (w := ENNReal.ofReal (B⁻¹ / Kd)) (ENNReal.ofReal_pos.2 (by positivity)).ne' hmod) _

end Geometry

end

end MLC.Research
