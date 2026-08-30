import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.ContinuousMap.Algebra

/-!
# A topological falsification gate for the motivic route

The frozen straddling target cannot follow from connectedness of the two
ambient sets alone.  This file records a concrete counterexample in `ℂ` and
the elementary algebraic shadow of a clopen separation.

No Mandelbrot or motive-specific hypothesis is used here.  The point is to
keep the first Plan 05 gate honest: a future incidence-category realization
must supply information beyond the connectedness of the translated
sublevel and of `M`.
-/

namespace MLC.Motivic

open Set Topology
open scoped Classical

noncomputable section

/-- The punctured plane, a connected open set. -/
def puncturedPlane : Set ℂ := ({0} : Set ℂ)ᶜ

/-- A connected real segment embedded in the complex plane. -/
def realSegment : Set ℂ :=
  Complex.ofReal '' Set.Icc (-1 : ℝ) 1

theorem puncturedPlane_isConnected : IsConnected puncturedPlane := by
  have hrank : 1 < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]
    norm_num
  simpa [puncturedPlane] using
    (isPathConnected_compl_singleton_of_one_lt_rank hrank (0 : ℂ)).isConnected

theorem puncturedPlane_isOpen : IsOpen puncturedPlane := by
  exact isClosed_singleton.isOpen_compl

theorem realSegment_isConnected : IsConnected realSegment := by
  have hinterval : IsConnected (Set.Icc (-1 : ℝ) 1) :=
    isConnected_Icc (by norm_num)
  exact hinterval.image (fun x : ℝ => (x : ℂ)) Complex.continuous_ofReal.continuousOn

theorem realSegment_endpoints_mem_inter : (-1 : ℂ) ∈ puncturedPlane ∩ realSegment := by
  refine ⟨?_, ?_⟩
  · simp [puncturedPlane]
  · refine ⟨-1, ?_, ?_⟩
    · norm_num
    · norm_num

theorem realSegment_right_endpoint_mem_inter : (1 : ℂ) ∈ puncturedPlane ∩ realSegment := by
  refine ⟨?_, ?_⟩
  · simp [puncturedPlane]
  · refine ⟨1, ?_, ?_⟩
    · norm_num
    · norm_num

/-- The puncture separates the embedded segment after intersection. -/
theorem puncturedPlane_inter_realSegment_not_isConnected :
    ¬ IsConnected (puncturedPlane ∩ realSegment) := by
  intro hconn
  have hzero_mem :
      (0 : ℝ) ∈ Set.Icc ((-1 : ℂ).re) ((1 : ℂ).re) := by
    norm_num
  have himage :
      (0 : ℝ) ∈ Complex.re '' (puncturedPlane ∩ realSegment) :=
    hconn.isPreconnected.intermediate_value
      (realSegment_endpoints_mem_inter : (-1 : ℂ) ∈ puncturedPlane ∩ realSegment)
      (realSegment_right_endpoint_mem_inter :
        (1 : ℂ) ∈ puncturedPlane ∩ realSegment)
      Complex.continuous_re.continuousOn
      hzero_mem
  rcases himage with ⟨z, hz, hzre⟩
  rcases hz.2 with ⟨x, hx, rfl⟩
  have hxzero : x = 0 := by
    simpa using hzre
  subst x
  exact hz.1 (by simp)

/-- Connectedness, openness, and a common point do not force a connected
intersection in the straddling case. -/
theorem no_generic_straddling_intersection_rule :
    ¬ (∀ (S K : Set ℂ) (c : ℂ),
      IsConnected S →
      IsConnected K →
      IsOpen S →
      c ∈ S ∩ K →
      ¬ S ⊆ K →
      IsConnected (S ∩ K)) := by
  intro h
  have hnot_sub : ¬ puncturedPlane ⊆ realSegment := by
    intro hsub
    have htwo : (2 : ℂ) ∈ puncturedPlane := by
      simp [puncturedPlane]
    rcases hsub htwo with ⟨x, hx, hxeq⟩
    have hx_eq : x = 2 := by
      have hreal := congrArg Complex.re hxeq
      simpa using hreal
    linarith [hx.2]
  exact puncturedPlane_inter_realSegment_not_isConnected
    (h puncturedPlane realSegment (-1 : ℂ)
      puncturedPlane_isConnected realSegment_isConnected puncturedPlane_isOpen
      realSegment_endpoints_mem_inter hnot_sub)

/-- The continuous integer-valued functions are an elementary topological
realization in which a clopen split becomes an idempotent. -/
abbrev integerValuedRealization (X : Type*) [TopologicalSpace X] :=
  C(X, ℤ)

/-- A clopen subset gives a continuous integer-valued characteristic map. -/
def boolToInt : Bool → ℤ :=
  fun b => if b then 1 else 0

def clopenCharacteristic {X : Type*} [TopologicalSpace X]
    (U : Set X) (hU : IsClopen U) : integerValuedRealization X :=
  (⟨boolToInt, continuous_of_discreteTopology⟩ : C(Bool, ℤ)).comp
    ⟨U.boolIndicator, (continuous_boolIndicator_iff_isClopen U).2 hU⟩

theorem clopenCharacteristic_apply {X : Type*} [TopologicalSpace X]
    (U : Set X) (hU : IsClopen U) (x : X) :
    clopenCharacteristic U hU x = if x ∈ U then 1 else 0 := by
  classical
  simp [clopenCharacteristic, boolToInt, Set.boolIndicator]

theorem clopenCharacteristic_idempotent {X : Type*} [TopologicalSpace X]
    (U : Set X) (hU : IsClopen U) :
    clopenCharacteristic U hU * clopenCharacteristic U hU =
      clopenCharacteristic U hU := by
  ext x
  classical
  by_cases hx : x ∈ U <;>
    simp [clopenCharacteristic, boolToInt, Set.boolIndicator, hx]

theorem clopenCharacteristic_nontrivial
    {X : Type*} [TopologicalSpace X] (U : Set X) (hU : IsClopen U)
    (hU_nonempty : U.Nonempty) (hUc_nonempty : Uᶜ.Nonempty) :
    clopenCharacteristic U hU ≠ 0 ∧
      clopenCharacteristic U hU ≠ 1 := by
  constructor
  · intro hzero
    rcases hU_nonempty with ⟨x, hx⟩
    have : (1 : ℤ) = 0 := by
      simpa [clopenCharacteristic, boolToInt, Set.boolIndicator, hx] using
        DFunLike.congr_fun hzero x
    norm_num at this
  · intro hone
    rcases hUc_nonempty with ⟨x, hx⟩
    have : (0 : ℤ) = 1 := by
      have hx' : x ∉ U := hx
      simpa [clopenCharacteristic, boolToInt, Set.boolIndicator, hx'] using
        DFunLike.congr_fun hone x
    norm_num at this

theorem clopen_split_to_nontrivial_idempotent
    {X : Type*} [TopologicalSpace X] (U : Set X) (hU : IsClopen U)
    (hU_nonempty : U.Nonempty) (hUc_nonempty : Uᶜ.Nonempty) :
    ∃ e : integerValuedRealization X,
      e * e = e ∧ e ≠ 0 ∧ e ≠ 1 := by
  refine ⟨clopenCharacteristic U hU, clopenCharacteristic_idempotent U hU, ?_⟩
  exact clopenCharacteristic_nontrivial U hU hU_nonempty hUc_nonempty

end

end MLC.Motivic
