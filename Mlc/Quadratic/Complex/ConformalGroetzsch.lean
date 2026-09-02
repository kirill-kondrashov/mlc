import Yoccoz.Quadratic.Complex.Groetzsch
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

namespace MLC
namespace Quadratic

open MeasureTheory

theorem modulus_finset_sum {ι : Type*} [DecidableEq ι] {s : Finset ι}
    {A : ι → Set ℂ}
    (h_disj : Set.PairwiseDisjoint s A)
    (h_meas : ∀ i ∈ s, MeasurableSet (A i)) :
    modulus (⋃ i ∈ s, A i) = ∑ i ∈ s, modulus (A i) := by
  simpa only [modulus] using
    (integral_biUnion_finset (f := weight) s h_meas h_disj
      (fun _ _ => weight_integrable.integrableOn))

end Quadratic
end MLC
