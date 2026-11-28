import Mlc.Research.LevelTower
import Mlc.Research.NestModulus

/-!
# Lemma D from stacked annuli

The linear dichotomy (`WidthTower.LinearDichotomy`, Lemma D) says that for every threshold `C` there
are constants `c > 0` and `A ≥ 0` such that for every pair of levels `k`, `k + n`, with `p` the
period of the level `k + n` relative to the level `k`, either the amplification
`c p W_{k+n} − A p ≤ W_k` holds, or the degeneration jumps, `C W_{k+n} ≤ W_{k+n+1}`. This module
gives a geometric form of the amplification, the one of the quasi-additivity mechanism of the survey
(§4.2, (4.5)): the annulus of the level `k + n` contains `p` pairwise disjoint essential annuli,
each of which has a definite modulus in terms of the degeneration of the level `k`.

* **Theorem `sum_extWidth_loopFamily_le`** (Grötzsch's inequality for disjoint sub-annuli): the
  moduli of pairwise disjoint measurable sub-annuli add up to at most the modulus of the annulus
  that contains them. The loops of a sub-annulus separating `K` from the complement of `O` are loops
  of the annulus, and the sub-annuli are disjoint regions (the parallel law). For the annuli of a
  nest this is `ConnectedNest.sum_extWidth_loops_le_coarse`.
* **Definition `LevelTower.StackedAnnuli L C c' A'`**: for every pair of levels `k`, `k + n`, either
  the degeneration jumps by the factor `C` at the level `k + n`, or the annulus of the level `k + n`
  contains `p = period k n` pairwise disjoint measurable sub-annuli, each of which has modulus at
  least `c' / (W_k + A')`.
* **Theorem `LevelTower.linearDichotomy_of_stacked`**: if the stacked annuli exist for every
  threshold `C`, with constants `c' > 0` and `A' ≥ 0`, the linear dichotomy holds: the moduli of the
  `p` sub-annuli add up, so `c' p W_{k+n} ≤ W_k + A'`, and `A' ≤ A' p`.

The additive loss `A'` of each sub-annulus, against the degeneration of the shallower level, is
the place where the thin–thick decomposition of the survey enters; a loss that grows with `p` is
absorbed by the linear error of the dichotomy. That the annulus of a level of a quadratic-like tower
contains such stacked annuli, pullbacks of the annulus of the shallower level along the critical
orbit, is the dynamical statement and is not proved here. In the round model of `RoundTower.lean`
the sub-annuli can be taken concentric, so the hypothesis demands there no more than the
amplification inequality itself (this converse is not formalized): the geometry enters only when
the sets of the levels are the dynamical ones.
-/

namespace MLC.Research

open MeasureTheory ENNReal Set Real

noncomputable section

/-- **Grötzsch's inequality for disjoint sub-annuli.** If the measurable sets `B i`, `i ∈ s`, are
pairwise disjoint and lie in `A`, the extremal widths of the loops in them that separate `K` from
the complement of `O` add up to at most the extremal width of the loops in `A` that separate `K`
from the complement of `O`. -/
theorem sum_extWidth_loopFamily_le {ι : Type*} (s : Finset ι) {B : ι → Set ℂ} {A K O : Set ℂ}
    (hmeas : ∀ i ∈ s, MeasurableSet (B i)) (hdisj : (s : Set ι).PairwiseDisjoint B)
    (hsub : ∀ i ∈ s, B i ⊆ A) :
    ∑ i ∈ s, extWidth volume (loopFamily (B i) K O) ≤ extWidth volume (loopFamily A K O) := by
  refine (extWidth_parallel_finset (m := volume) s (Γ := fun i => loopFamily (B i) K O)
    (Ω := B) hmeas hdisj ?_).trans (extWidth_mono ?_)
  · intro i hi μ hμ
    obtain ⟨γ, hγ, hA, -, rfl⟩ := hμ
    exact loopMeasure_compl_eq_zero hγ (hmeas i hi) hA
  · intro μ hμ
    obtain ⟨i, hi, hμi⟩ := Set.mem_iUnion₂.1 hμ
    exact loopFamily_mono (hsub i hi) subset_rfl subset_rfl hμi

namespace LevelTower

variable (L : LevelTower)

/-- **Stacked annuli.** For every pair of levels `k`, `k + n`, either the degeneration jumps by the
factor `C` at the level `k + n`, or the annulus of the level `k + n` contains `p = period k n`
pairwise disjoint measurable sub-annuli, each of which has modulus at least `c' / (W_k + A')`: the
quasi-additivity mechanism of the survey (§4.2), in which the deeper annulus collects the moduli of
the pullbacks of the shallower one, each with an additive loss `A'` in the degeneration. -/
def StackedAnnuli (C c' A' : ℝ) : Prop :=
  ∀ k n, L.Jumps C (k + n) ∨ ∃ B : Fin (L.period k n) → Set ℂ, (∀ i, MeasurableSet (B i)) ∧
    Pairwise (Function.onFun Disjoint B) ∧
    (∀ i, B i ⊆ L.target (k + n) \ L.filled (k + n)) ∧
    ∀ i, ENNReal.ofReal (c' / (L.width k + A')) ≤
      extWidth volume (loopFamily (B i) (L.filled (k + n)) (L.target (k + n)))

/-- **Stacked annuli give the amplification or a jump.** The moduli of the `p` sub-annuli add up
(Grötzsch), so the modulus of the annulus of the level `k + n` is at least `p c' / (W_k + A')`;
that is `c' p W_{k+n} ≤ W_k + A'`, hence `c' p W_{k+n} − A' p ≤ W_k`. -/
theorem amplifies_or_jumps_of_stacked {C c' A' : ℝ} (hc' : 0 < c') (hA' : 0 ≤ A')
    (h : L.StackedAnnuli C c' A') (k n : ℕ) :
    L.Amplifies c' (fun p => A' * p) k n ∨ L.Jumps C (k + n) := by
  rcases h k n with hj | ⟨B, hmeas, hdisj, hsub, hmod⟩
  · exact Or.inr hj
  · left
    have hp1 : 1 ≤ L.period k n := (Nat.one_le_two_pow).trans (L.two_pow_le_period k n)
    have hWk := L.width_pos k
    have hWn := L.width_pos (k + n)
    have hden : 0 < L.width k + A' := by linarith
    have hx : 0 < c' / (L.width k + A') := div_pos hc' hden
    have hsum : ((L.period k n : ℕ) : ℝ≥0∞) * ENNReal.ofReal (c' / (L.width k + A')) ≤
        L.modulus (k + n) := by
      have h1 := sum_extWidth_loopFamily_le (Finset.univ : Finset (Fin (L.period k n))) (B := B)
        (A := L.target (k + n) \ L.filled (k + n)) (K := L.filled (k + n))
        (O := L.target (k + n)) (fun i _ => hmeas i) (fun i _ j _ hij => hdisj hij)
        (fun i _ => hsub i)
      calc ((L.period k n : ℕ) : ℝ≥0∞) * ENNReal.ofReal (c' / (L.width k + A'))
          = ∑ _i : Fin (L.period k n), ENNReal.ofReal (c' / (L.width k + A')) := by
            simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        _ ≤ ∑ i, extWidth volume (loopFamily (B i) (L.filled (k + n)) (L.target (k + n))) :=
            Finset.sum_le_sum fun i _ => hmod i
        _ ≤ L.modulus (k + n) := h1
    rw [L.modulus_eq (k + n)] at hsum
    have h2 := ENNReal.le_inv_iff_mul_le.1 hsum
    have h3 : ENNReal.ofReal ((L.period k n : ℝ) * (c' / (L.width k + A')) * L.width (k + n)) ≤
        1 := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_natCast]
      exact h2
    have h4 := ENNReal.ofReal_le_one.1 h3
    have h5 : c' * (L.period k n : ℝ) * L.width (k + n) / (L.width k + A') ≤ 1 := by
      calc c' * (L.period k n : ℝ) * L.width (k + n) / (L.width k + A')
          = (L.period k n : ℝ) * (c' / (L.width k + A')) * L.width (k + n) := by ring
        _ ≤ 1 := h4
    rw [div_le_one hden] at h5
    have hpR : (1 : ℝ) ≤ L.period k n := by exact_mod_cast hp1
    have hAp : A' ≤ A' * (L.period k n : ℝ) := by nlinarith
    show c' * (L.period k n : ℝ) * L.width (k + n) - A' * (L.period k n : ℝ) ≤ L.width k
    linarith

/-- **Lemma D from stacked annuli.** If for every threshold `C` there are constants `c' > 0` and
`A' ≥ 0` with stacked annuli, the linear dichotomy holds. -/
theorem linearDichotomy_of_stacked
    (h : ∀ C : ℝ, 0 < C → ∃ c' : ℝ, 0 < c' ∧ ∃ A' : ℝ, 0 ≤ A' ∧ L.StackedAnnuli C c' A') :
    L.LinearDichotomy := fun C hC => by
  obtain ⟨c', hc', A', hA', hst⟩ := h C hC
  exact ⟨c', hc', A', hA', fun k n => L.amplifies_or_jumps_of_stacked hc' hA' hst k n⟩

end LevelTower

end

end MLC.Research
