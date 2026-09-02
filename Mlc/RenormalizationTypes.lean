import Yoccoz.Quadratic.Complex.Basic
import Yoccoz.Quadratic.Complex.Puzzle
import Yoccoz.Yoccoz
import Mlc.LocalConnectivity
import Molecule.Rfast
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Convex.Contractible
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import Mathlib.Tactic.NormNum

namespace MLC

open Molecule Complex Topology Set Filter

noncomputable section

/-- Primitive renormalizable parameters in the root-facing interface. -/
def PrimitiveRenormalizable (c : ℂ) : Prop :=
  ∀ (hc : c ∈ MLC.Quadratic.MandelbrotSet),
    MLC.LocallyConnectedAt MLC.Quadratic.MandelbrotSet ⟨c, hc⟩

private lemma isProperMap_pow2 : IsProperMap (fun z : ℂ => z^2) := by
  rw [isProperMap_iff_isCompact_preimage]
  constructor
  · exact continuous_pow 2
  · intro K hK
    refine
      Metric.isCompact_of_isClosed_isBounded
        (hK.isClosed.preimage (continuous_pow 2)) ?_
    obtain ⟨R, hR⟩ := hK.isBounded.subset_ball (0 : ℂ)
    rw [isBounded_iff_forall_norm_le]
    refine ⟨Real.sqrt R, ?_⟩
    intro z hz
    have : ‖z^2‖ < R := by
      apply mem_ball_zero_iff.mp
      apply hR
      exact hz
    rw [norm_pow] at this
    apply le_of_lt
    have hlt : Real.sqrt (‖z‖ ^ 2) < Real.sqrt R :=
      (Real.sqrt_lt_sqrt_iff (sq_nonneg _)).2 this
    simpa [Real.sqrt_sq (norm_nonneg z)] using hlt

private lemma isProperMap_quadratic (c : ℂ) :
    IsProperMap (fun z : ℂ => z^2 + c) := by
  have h_pow : IsProperMap (fun z : ℂ => z^2) := isProperMap_pow2
  have h_add : IsProperMap (fun z : ℂ => z + c) :=
    (Homeomorph.addRight c).isProperMap
  simpa [Function.comp, add_comm, add_left_comm, add_assoc] using h_add.comp h_pow

theorem parameterToBMol_spec (c : ℂ) :
    ∃ g : BMol, g.f = (fun z : ℂ => z^2 + c) ∧ criticalValue g = c := by
  let U : Set ℂ := Set.univ
  let V : Set ℂ := Set.univ
  let f : ℂ → ℂ := fun z => z^2 + c
  let g : BMol :=
    { U := U
      V := V
      f := f
      isOpen_U := isOpen_univ
      isOpen_V := isOpen_univ
      isConnected_U := isConnected_univ
      isConnected_V := isConnected_univ
      simplyConnected_U := by
        have : ContractibleSpace U :=
          (convex_univ : Convex ℝ (Set.univ : Set ℂ)).contractibleSpace Set.univ_nonempty
        infer_instance
      simplyConnected_V := by
        have : ContractibleSpace V :=
          (convex_univ : Convex ℝ (Set.univ : Set ℂ)).contractibleSpace Set.univ_nonempty
        infer_instance
      subset := by
        intro z hz
        exact mem_univ z
      closure_subset := by
        simp [U, V]
      differentiable_on := by
        simpa [U, f] using (differentiableOn_id.pow 2).const_add c
      maps_to := by
        intro z hz
        exact mem_univ (f z)
      proper := by
        rw [isProperMap_iff_isCompact_preimage]
        constructor
        · exact ((continuous_pow 2).add continuous_const).continuousOn.mapsToRestrict _
        · intro K hK
          let K' : Set ℂ := Subtype.val '' K
          have hK'_compact : IsCompact K' := hK.image continuous_subtype_val
          have hS_compact : IsCompact (f ⁻¹' K') :=
            (isProperMap_quadratic c).isCompact_preimage hK'_compact
          rw [Subtype.isCompact_iff]
          have : Subtype.val '' (MapsTo.restrict f U V (by
            intro z hz
            exact mem_univ (f z)
          ) ⁻¹' K) = f ⁻¹' K' := by
            ext z
            constructor
            · rintro ⟨x, hx, rfl⟩
              refine ⟨(MapsTo.restrict f U V (by
                intro z hz
                exact mem_univ (f z)
              ) x), hx, rfl⟩
            · intro hz
              rcases hz with ⟨y, hy, hy_eq⟩
              refine ⟨⟨z, mem_univ z⟩, ?_, rfl⟩
              have : (MapsTo.restrict f U V (by
                intro z hz
                exact mem_univ (f z)
              ) ⟨z, mem_univ z⟩) = y := by
                apply Subtype.ext
                have : (MapsTo.restrict f U V (by
                  intro z hz
                  exact mem_univ (f z)
                ) ⟨z, mem_univ z⟩).1 = y.1 := by
                  simpa [MapsTo.restrict] using hy_eq.symm
                exact this
              simpa [this] using hy
          rw [this]
          exact hS_compact
      unique_critical_point := by
        refine ⟨0, ?_, ?_⟩
        · constructor
          · simp [U]
          · simp [f]
        · intro y hy
          have h1 : deriv f y = 2 * y := by
            simp [f]
          have hzero : (2 : ℂ) * y = 0 := by
            simpa [h1] using hy.2
          rcases mul_eq_zero.mp hzero with h2 | hy0
          · cases (by norm_num : (2 : ℂ) ≠ 0) h2
          · exact hy0
      simple_critical_point := by
        intro c0 _hc0 h_deriv
        have h1 : deriv f c0 = 2 * c0 := by
          simp [f]
        have h_deriv_fun : deriv f = fun z => 2 * z := by
          ext z
          simp [f]
        rw [h1] at h_deriv
        rw [h_deriv_fun]
        rw [deriv_const_mul]
        · rw [deriv_id'']
          norm_num
        · exact differentiableAt_id }
  have h0 : 0 ∈ g.U ∧ deriv g.f 0 = 0 := by
    simp [g, f, U]
  rcases g.unique_critical_point with ⟨c0, hc0, huniq⟩
  have hcp : criticalPoint g ∈ g.U ∧ deriv g.f (criticalPoint g) = 0 :=
    (Classical.choose_spec g.unique_critical_point).1
  have hcp_eq : criticalPoint g = c0 := huniq _ hcp
  have h0_eq : 0 = c0 := huniq _ h0
  have hcp0 : criticalPoint g = 0 := by
    calc
      criticalPoint g = c0 := hcp_eq
      _ = 0 := h0_eq.symm
  refine ⟨g, rfl, ?_⟩
  simp [criticalValue, g, f, hcp0]

noncomputable def parameterToBMol (c : ℂ) : BMol :=
  Classical.choose (parameterToBMol_spec c)

abbrev FinitelyRenormalizable := NonRenormalizable

def PuzzleModulusSummable (c : ℂ) : Prop :=
  Summable (fun n => MLC.Quadratic.modulus (MLC.Quadratic.PuzzleAnnulus c n))

structure InfinitelyRenormalizable (c : ℂ) : Prop where
  puzzleModulusSummable : PuzzleModulusSummable c

@[simp] theorem puzzleModulusSummable_iff_not_finitelyRenormalizable (c : ℂ) :
    PuzzleModulusSummable c ↔ ¬ FinitelyRenormalizable c := by
  simp [PuzzleModulusSummable, FinitelyRenormalizable, NonRenormalizable]

theorem infinitelyRenormalizable_of_not_finitelyRenormalizable (c : ℂ) :
    ¬ FinitelyRenormalizable c → InfinitelyRenormalizable c := by
  intro h
  exact ⟨(puzzleModulusSummable_iff_not_finitelyRenormalizable c).2 h⟩

end

end MLC
