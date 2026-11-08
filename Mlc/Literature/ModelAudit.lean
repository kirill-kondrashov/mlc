import Mlc.Literature.Combinatorics
import Mlc.Quadratic.Complex.ConformalGroetzsch

/-!
# Audit of the frozen puzzle model

`Quadratic.modulus` in the pinned Yoccoz dependency is Gaussian weighted
area. It is not conformal modulus. Differences of any nested measurable
family therefore have summable `modulus`, independently of their
intersection. In particular, the legacy `FinitelyRenormalizable` predicate
has no instances and must not be identified with the literature class.
-/

namespace MLC.Literature.ModelAudit

open Set Filter Topology MeasureTheory BigOperators

noncomputable section

theorem weightedArea_le_total (A : Set ℂ) :
    Quadratic.modulus A ≤ Quadratic.modulus Set.univ := by
  unfold Quadratic.modulus
  apply integral_mono_measure
    (Measure.restrict_mono (subset_univ A) le_rfl)
  · exact ae_of_all _ fun z => le_of_lt (Real.exp_pos _)
  · exact Quadratic.weight_integrable.integrableOn

theorem summable_weightedArea_differences
    (P : ℕ → Set ℂ)
    (hnested : ∀ n, P (n + 1) ⊆ P n)
    (hmeasurable : ∀ n, MeasurableSet (P n)) :
    Summable (fun n => Quadratic.modulus (P n \ P (n + 1))) := by
  let A := fun n => P n \ P (n + 1)
  have hdisjoint : Pairwise (fun i j => Disjoint (A i) (A j)) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro z hzi hzj
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact hzi.2
        (Quadratic.subset_of_le_nested hnested (Nat.succ_le_of_lt hlt) hzj.1)
    · exact hzj.2
        (Quadratic.subset_of_le_nested hnested (Nat.succ_le_of_lt hgt) hzi.1)
  apply summable_of_sum_range_le
    (c := Quadratic.modulus Set.univ) (fun n => Quadratic.modulus_nonneg _)
  intro N
  have hsum :
      Quadratic.modulus (⋃ n ∈ Finset.range N, A n) =
        ∑ n ∈ Finset.range N, Quadratic.modulus (A n) :=
    Quadratic.modulus_finset_sum
      (fun i _ j _ hij => hdisjoint hij)
      (fun n _ => (hmeasurable n).diff (hmeasurable (n + 1)))
  change (∑ n ∈ Finset.range N, Quadratic.modulus (A n)) ≤ _
  rw [← hsum]
  exact weightedArea_le_total _

theorem frozen_puzzle_modulus_summable (c : ℂ) :
    MLC.PuzzleModulusSummable c := by
  exact summable_weightedArea_differences
    (fun n => Quadratic.DynamicalPuzzlePiece c n 0)
    (Quadratic.dynamical_puzzle_piece_nested c)
    (fun n => (Quadratic.isOpen_dynamicalPuzzlePiece_conformal c n).measurableSet)

theorem not_finitelyRenormalizable_in_frozenModel (c : ℂ) :
    ¬ MLC.FinitelyRenormalizable c := by
  intro h
  exact h (frozen_puzzle_modulus_summable c)

theorem no_uniform_lower_bound_frozen_puzzleAnnuli (c : ℂ) :
    ¬ ∃ μ : ℝ, 0 < μ ∧ ∀ n, μ ≤ Quadratic.modulus (Quadratic.PuzzleAnnulus c n) := by
  rintro ⟨μ, hμ, hbound⟩
  exact not_summable_of_uniform_lower_bound hμ hbound
    (frozen_puzzle_modulus_summable c)

theorem frozen_principalNest_modulus_summable
    (c : ℂ) (depths : ℕ → ℕ) (hmono : Monotone depths) :
    Summable (fun n =>
      Quadratic.modulus (Quadratic.PrincipalNest.dynAnnulus c depths n)) := by
  exact summable_weightedArea_differences
    (fun n => Quadratic.DynamicalPuzzlePiece c (depths n) 0)
    (fun n => Quadratic.subset_of_le_nested
      (P := fun k => Quadratic.DynamicalPuzzlePiece c k 0)
      (Quadratic.dynamical_puzzle_piece_nested c) (hmono (Nat.le_succ n)))
    (fun n =>
      (Quadratic.isOpen_dynamicalPuzzlePiece_conformal c (depths n)).measurableSet)

theorem not_nonempty_satelliteAPrioriCertificate (c : ℂ) :
    ¬ Nonempty (SatelliteAPrioriCertificate c) := by
  rintro ⟨certificate⟩
  obtain ⟨μ, hμ, hbound⟩ := certificate.uniformBound
  exact not_summable_of_uniform_lower_bound hμ hbound
    (frozen_principalNest_modulus_summable c
      (PrincipalNestTarget.depthsFromSatelliteTower c certificate.tower)
      (PrincipalNestTarget.depthsFromSatelliteTower_monotone c certificate.tower))

end

end MLC.Literature.ModelAudit
