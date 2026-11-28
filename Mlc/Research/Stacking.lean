import Mlc.Research.LevelTower
import Mlc.Research.NestModulus
import Mlc.Research.RoundTower

/-!
# Lemma D from stacked annuli

The linear dichotomy (`WidthTower.LinearDichotomy`, Lemma D) says that for every threshold `C` there
are constants `c > 0` and `A ≥ 0` such that for every pair of levels `k`, `k + n`, with `p` the
period of the level `k + n` relative to the level `k`, either the amplification
`c p W_{k+n} − A p ≤ W_k` holds, or the degeneration jumps, `C W_{k+n} ≤ W_{k+n+1}`. This module
gives a geometric sufficient form of the amplification, a proposed analogue of the quasi-additivity
mechanism of the survey (§4.2, (4.5), where the degeneration is collected along the orbit of a
puzzle piece): the annulus of the level `k + n` contains `p` pairwise disjoint essential annuli,
each of which has a definite modulus in terms of the degeneration of the level `k`. The survey does
not state this form; the code encodes measurable regions whose loops separate the same set, and
neither pullbacks nor the geometry of the orbit.

* **Theorem `sum_extWidth_loopFamily_le`** (Grötzsch's inequality for disjoint sub-annuli): the
  moduli of pairwise disjoint measurable sub-annuli add up to at most the modulus of the annulus
  that contains them. The loops of a sub-annulus separating `K` from the complement of `O` are loops
  of the annulus, and the sub-annuli are disjoint regions (the parallel law). For the annuli of a
  nest this is `ConnectedNest.sum_extWidth_loops_le_coarse`.
* **Definition `LevelTower.StackedAnnuli L C c' A'`**: for every pair of levels `k`, `k + n`, either
  the degeneration jumps by the factor `C` at the level `k + n`, or the annulus of the level `k + n`
  contains `p = period k n` pairwise disjoint measurable sub-annuli, each of which has modulus at
  least `c' / (W_k + A' p)`: the additive loss in the degeneration of the stack is linear in the
  period, as in the dichotomy.
* **Theorem `LevelTower.linearDichotomy_of_stacked`**: if the stacked annuli exist for every
  threshold `C`, with constants `c' > 0` and `A' ≥ 0`, the linear dichotomy holds: the moduli of the
  `p` sub-annuli add up, so the modulus of the annulus of the level `k + n` is at least
  `p c' / (W_k + A' p)`, that is `c' p W_{k+n} ≤ W_k + A' p`.
* **Theorem `WidthTower.linearDichotomy_iff_stacked`**: in the round model of `RoundTower.lean` the
  converse holds, the sub-annuli being concentric: Lemma D is equivalent to the stacked annuli for
  every threshold. So the geometric form is exact where the geometry is trivial, and carries
  information about the dynamics only when the sets of the levels are the dynamical ones. The form
  with a loss `A'` that does not grow with `p`, that is `c' / (W_k + A')`, is strictly stronger, and
  fails for a tower of constant degeneration without jumps.

That the annulus of a level of a tower contains such stacked annuli is the dynamical statement and
is not proved here.
-/

namespace MLC.Research

open MeasureTheory ENNReal Set Real Metric

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
pairwise disjoint measurable sub-annuli, each of which has modulus at least `c' / (W_k + A' p)`: a
proposed sufficient form of the amplification, in which the deeper annulus collects the moduli of
`p` sub-annuli with an additive loss in the degeneration that is linear in the period. -/
def StackedAnnuli (C c' A' : ℝ) : Prop :=
  ∀ k n, L.Jumps C (k + n) ∨ ∃ B : Fin (L.period k n) → Set ℂ, (∀ i, MeasurableSet (B i)) ∧
    Pairwise (Function.onFun Disjoint B) ∧
    (∀ i, B i ⊆ L.target (k + n) \ L.filled (k + n)) ∧
    ∀ i, ENNReal.ofReal (c' / (L.width k + A' * L.period k n)) ≤
      extWidth volume (loopFamily (B i) (L.filled (k + n)) (L.target (k + n)))

/-- **Stacked annuli give the amplification or a jump.** The moduli of the `p` sub-annuli add up
(Grötzsch), so the modulus of the annulus of the level `k + n` is at least `p c' / (W_k + A' p)`;
that is `c' p W_{k+n} ≤ W_k + A' p`, the amplification. -/
theorem amplifies_or_jumps_of_stacked {C c' A' : ℝ} (hc' : 0 < c') (hA' : 0 ≤ A')
    (h : L.StackedAnnuli C c' A') (k n : ℕ) :
    L.Amplifies c' (fun p => A' * p) k n ∨ L.Jumps C (k + n) := by
  rcases h k n with hj | ⟨B, hmeas, hdisj, hsub, hmod⟩
  · exact Or.inr hj
  · left
    have hWk := L.width_pos k
    have hWn := L.width_pos (k + n)
    have hAp : 0 ≤ A' * (L.period k n : ℝ) := mul_nonneg hA' (Nat.cast_nonneg _)
    have hden : 0 < L.width k + A' * L.period k n := by linarith
    have hx : 0 < c' / (L.width k + A' * L.period k n) := div_pos hc' hden
    have hsum : ((L.period k n : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal (c' / (L.width k + A' * L.period k n)) ≤ L.modulus (k + n) := by
      have h1 := sum_extWidth_loopFamily_le (Finset.univ : Finset (Fin (L.period k n))) (B := B)
        (A := L.target (k + n) \ L.filled (k + n)) (K := L.filled (k + n))
        (O := L.target (k + n)) (fun i _ => hmeas i) (fun i _ j _ hij => hdisj hij)
        (fun i _ => hsub i)
      calc ((L.period k n : ℕ) : ℝ≥0∞) *
            ENNReal.ofReal (c' / (L.width k + A' * L.period k n))
          = ∑ _i : Fin (L.period k n),
              ENNReal.ofReal (c' / (L.width k + A' * L.period k n)) := by
            simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        _ ≤ ∑ i, extWidth volume (loopFamily (B i) (L.filled (k + n)) (L.target (k + n))) :=
            Finset.sum_le_sum fun i _ => hmod i
        _ ≤ L.modulus (k + n) := h1
    rw [L.modulus_eq (k + n)] at hsum
    have h2 := ENNReal.le_inv_iff_mul_le.1 hsum
    have h3 : ENNReal.ofReal ((L.period k n : ℝ) *
        (c' / (L.width k + A' * L.period k n)) * L.width (k + n)) ≤ 1 := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_natCast]
      exact h2
    have h4 := ENNReal.ofReal_le_one.1 h3
    have h5 : c' * (L.period k n : ℝ) * L.width (k + n) /
        (L.width k + A' * L.period k n) ≤ 1 := by
      calc c' * (L.period k n : ℝ) * L.width (k + n) / (L.width k + A' * L.period k n)
          = (L.period k n : ℝ) * (c' / (L.width k + A' * L.period k n)) * L.width (k + n) := by
            ring
        _ ≤ 1 := h4
    rw [div_le_one hden] at h5
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

/-! ### The round model -/

namespace WidthTower

variable (T : WidthTower)

/-- **In the round model the amplification gives stacked annuli.** In the level tower of round
annuli `T.toLevelTower` the annulus of the level `k + n` is `B(0, e^{2π/W_{k+n}}) ∖ B̄(0, 1)`; it
splits into `p` concentric annuli of the same modulus `1 / (p W_{k+n})`, and the amplification
`c' p W_{k+n} − A' p ≤ W_k` makes each of them have modulus at least `c' / (W_k + A' p)`. -/
theorem toLevelTower_stackedAnnuli_of_amplifies {C c' A' : ℝ} (hA' : 0 ≤ A')
    (h : ∀ k n, T.Amplifies c' (fun p => A' * p) k n ∨ T.Jumps C (k + n)) :
    T.toLevelTower.StackedAnnuli C c' A' := by
  intro k n
  rcases h k n with hamp | hj
  · right
    have hwpos : 0 < T.width (k + n) := T.width_pos (k + n)
    have hp1 : 1 ≤ T.period k n := (Nat.one_le_two_pow).trans (T.two_pow_le_period k n)
    have hppos : (0 : ℝ) < T.period k n := by exact_mod_cast hp1
    have hWk := T.width_pos k
    have hAp : 0 ≤ A' * (T.period k n : ℝ) := mul_nonneg hA' (Nat.cast_nonneg _)
    have hden : 0 < T.width k + A' * T.period k n := by linarith
    set a : ℝ := 2 * π / T.width (k + n) with ha
    have hapos : 0 < a := by positivity
    set p : ℕ := T.period k n with hp
    let r : ℕ → ℝ := fun i => Real.exp (a * ((i : ℝ) / p))
    have hr_pos : ∀ i, 0 < r i := fun i => Real.exp_pos _
    have hr_lt : ∀ i j : ℕ, i < j → r i < r j := fun i j hij =>
      Real.exp_lt_exp.2 (mul_lt_mul_of_pos_left
        (div_lt_div_of_pos_right (by exact_mod_cast hij) hppos) hapos)
    have hr_le : ∀ i j : ℕ, i ≤ j → r i ≤ r j := fun i j hij => by
      rcases hij.eq_or_lt with rfl | hlt
      · exact le_rfl
      · exact (hr_lt i j hlt).le
    have hr0 : r 0 = 1 := by simp [r]
    have hrp : r p = Real.exp a := by simp [r, hppos.ne']
    have hlog : ∀ i : ℕ, Real.log (r (i + 1) / r i) = a / p := by
      intro i
      rw [Real.log_div (hr_pos _).ne' (hr_pos _).ne']
      simp only [r, Real.log_exp]
      push_cast
      ring
    have hfilled : T.toLevelTower.filled (k + n) = closedBall 0 1 := rfl
    have htarget : T.toLevelTower.target (k + n) = ball 0 (Real.exp a) := rfl
    have hdisj : ∀ i j : Fin p, i < j →
        Disjoint (ball (0 : ℂ) (r (i + 1)) \ closedBall 0 (r i))
          (ball (0 : ℂ) (r (j + 1)) \ closedBall 0 (r j)) := by
      intro i j hij
      refine Set.disjoint_left.2 fun z hz1 hz2 => ?_
      have h1 : ‖z‖ < r (i + 1) := mem_ball_zero_iff.1 hz1.1
      have h2 : r j < ‖z‖ := not_le.1 (mem_closedBall_zero_iff.not.1 hz2.2)
      exact absurd (h2.trans h1) (not_lt.2 (hr_le (i + 1) j (Nat.succ_le_of_lt hij)))
    refine ⟨fun i => ball (0 : ℂ) (r (i + 1)) \ closedBall 0 (r i),
      fun i => measurableSet_ball.diff measurableSet_closedBall, ?_, ?_, ?_⟩
    · intro i j hij
      rcases lt_or_gt_of_ne hij with hlt | hgt
      · exact hdisj i j hlt
      · exact (hdisj j i hgt).symm
    · intro i z hz
      rw [hfilled, htarget]
      refine ⟨?_, ?_⟩
      · rw [mem_ball_zero_iff]
        exact (mem_ball_zero_iff.1 hz.1).trans_le
          ((hr_le (i + 1) p (Nat.succ_le_of_lt i.isLt)).trans_eq hrp)
      · rw [mem_closedBall_zero_iff, not_le]
        have h2 : r i < ‖z‖ := not_le.1 (mem_closedBall_zero_iff.not.1 hz.2)
        exact lt_of_le_of_lt (hr0 ▸ hr_le 0 i (Nat.zero_le _)) h2
    · intro i
      have hi := extWidth_loopFamily_ge_radii_of_ioo
        (A := ball (0 : ℂ) (r (i + 1)) \ closedBall 0 (r i)) (K := closedBall (0 : ℂ) 1)
        (O := ball (0 : ℂ) (Real.exp a)) (c := 0) (r := r i) (R := r (i + 1)) (hr_pos i)
        (hr_lt i (i + 1) (Nat.lt_succ_self _))
        (fun z hz => by
          rw [sub_zero]
          exact (mem_closedBall_zero_iff.1 hz).trans (hr0 ▸ hr_le 0 i (Nat.zero_le _)))
        (fun w hw => by
          rw [sub_zero]
          have hw' : Real.exp a ≤ ‖w‖ := not_lt.1 (mem_ball_zero_iff.not.1 hw)
          exact (hr_le (i + 1) p (Nat.succ_le_of_lt i.isLt)).trans (hrp ▸ hw'))
        (fun s hs t => by
          have hn : ‖circleLoop s t‖ = s := norm_pol (hs.1.le.trans' (hr_pos i).le) _
          rw [zero_add]
          refine ⟨?_, ?_⟩
          · rw [mem_ball_zero_iff, hn]
            exact hs.2
          · rw [mem_closedBall_zero_iff, hn, not_le]
            exact hs.1)
      rw [hfilled, htarget]
      refine le_trans (ENNReal.ofReal_le_ofReal ?_) hi
      rw [hlog i]
      have hamp' : c' * (p : ℝ) * T.width (k + n) ≤ T.width k + A' * p := by
        have h0 := hamp
        unfold WidthTower.Amplifies at h0
        simp only at h0
        linarith
      have hval : a / (p : ℝ) / (2 * π) = 1 / (T.width (k + n) * p) := by
        rw [ha]
        field_simp
      rw [hval]
      show c' / (T.width k + A' * (p : ℝ)) ≤ 1 / (T.width (k + n) * p)
      rw [div_le_div_iff₀ hden (by positivity)]
      nlinarith [hamp', hwpos, hppos]
  · exact Or.inl hj

/-- **In the round model, Lemma D is equivalent to the stacked annuli.** For the level tower of
round annuli of a width tower `T`, the linear dichotomy holds exactly when, for every threshold, the
stacked annuli exist: the geometric form of Lemma D is exact where the geometry is trivial. -/
theorem linearDichotomy_iff_stacked :
    T.LinearDichotomy ↔
      ∀ C : ℝ, 0 < C → ∃ c' : ℝ, 0 < c' ∧ ∃ A' : ℝ, 0 ≤ A' ∧ T.toLevelTower.StackedAnnuli C c' A' :=
  ⟨fun h C hC => by
      obtain ⟨c, hc, A, hA, hamp⟩ := h C hC
      exact ⟨c, hc, A, hA, T.toLevelTower_stackedAnnuli_of_amplifies hA hamp⟩,
    fun h => T.toLevelTower.linearDichotomy_of_stacked h⟩

end WidthTower

end

end MLC.Research
