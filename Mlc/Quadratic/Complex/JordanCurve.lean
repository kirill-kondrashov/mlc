import Mlc.Quadratic.Complex.JordanBasics
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Path
import Mathlib.Topology.Closure

namespace MLC.Quadratic

open Complex Topology Set

noncomputable section

/-!
Jordan curve theorem development plan.

This file will host the core separation theorem for Jordan curves in `ℂ`.
It is currently a placeholder with a single consolidated statement.
-/

/-- The interior component lies in the complement of the curve image. -/
lemma jordan_interior_subset_compl (γ : ℝ → ℂ) :
    JordanInterior γ ⊆ Set.compl (JordanCurveImage γ) := by
  exact connectedComponentIn_subset _ _

/-- The exterior component lies in the complement of the curve image. -/
lemma jordan_exterior_subset_compl (γ : ℝ → ℂ) :
    JordanExterior γ ⊆ Set.compl (JordanCurveImage γ) := by
  exact connectedComponentIn_subset _ _

lemma mem_connectedComponentIn_of_path {F : Set ℂ} {x y : ℂ} (γ : Path x y)
    (hγ : ∀ t, γ t ∈ F) :
    x ∈ connectedComponentIn F y := by
  have hconn : IsConnected (Set.range γ) := by
    have hcont_on : ContinuousOn γ (Set.univ : Set unitInterval) :=
      (Path.continuous γ).continuousOn
    have hconn_univ : IsConnected (Set.univ : Set unitInterval) := isConnected_univ
    have hconn_img : IsConnected (γ '' (Set.univ : Set unitInterval)) :=
      hconn_univ.image γ hcont_on
    simpa [Set.image_univ] using hconn_img
  have hy : y ∈ Set.range γ := Path.target_mem_range γ
  have hsub : Set.range γ ⊆ F := by
    intro z hz
    rcases hz with ⟨t, rfl⟩
    exact hγ t
  have hsubset : Set.range γ ⊆ connectedComponentIn F y :=
    hconn.isPreconnected.subset_connectedComponentIn hy hsub
  exact hsubset (Path.source_mem_range γ)

lemma mem_jordanInterior_of_path (γ : ℝ → ℂ) {z : ℂ} (p : Path z 0)
    (hp : ∀ t, p t ∈ Set.compl (JordanCurveImage γ)) :
    z ∈ JordanInterior γ := by
  have hz : z ∈ connectedComponentIn (Set.compl (JordanCurveImage γ)) 0 :=
    mem_connectedComponentIn_of_path p hp
  simpa [JordanInterior] using hz

lemma mem_jordanExterior_of_path (γ : ℝ → ℂ) {z : ℂ} (p : Path z 1)
    (hp : ∀ t, p t ∈ Set.compl (JordanCurveImage γ)) :
    z ∈ JordanExterior γ := by
  have hz : z ∈ connectedComponentIn (Set.compl (JordanCurveImage γ)) 1 :=
    mem_connectedComponentIn_of_path p hp
  simpa [JordanExterior] using hz

/-- Connected components are disjoint if the basepoint is not in the other component. -/
lemma connectedComponentIn_disjoint_of_not_mem {F : Set ℂ} {x y : ℂ}
    (hy : y ∉ connectedComponentIn F x) :
    Disjoint (connectedComponentIn F x) (connectedComponentIn F y) := by
  refine Set.disjoint_left.2 ?_
  intro z hz hx
  have hxz : connectedComponentIn F x = connectedComponentIn F z :=
    connectedComponentIn_eq hz
  have hyz : connectedComponentIn F y = connectedComponentIn F z :=
    connectedComponentIn_eq hx
  have hxy : connectedComponentIn F x = connectedComponentIn F y :=
    hxz.trans hyz.symm
  have hyF : y ∈ F := by
    by_contra hyF
    have hyEmpty : connectedComponentIn F y = ∅ :=
      connectedComponentIn_eq_empty hyF
    have hxEmpty : connectedComponentIn F x = ∅ := by
      simpa [hyEmpty] using hxy
    have : False := by
      simpa [hxEmpty] using hz
    exact this
  have hy_mem : y ∈ connectedComponentIn F y := mem_connectedComponentIn hyF
  have : y ∈ connectedComponentIn F x := by
    simpa [hxy] using hy_mem
  exact hy this

lemma jordan_interior_eq_exterior_of_mem (γ : ℝ → ℂ)
    (h : (1 : ℂ) ∈ JordanInterior γ) :
    JordanExterior γ = JordanInterior γ := by
  have h' : (1 : ℂ) ∈
      connectedComponentIn (Set.compl (JordanCurveImage γ)) 0 := by
    simpa [JordanInterior] using h
  have h_eq :
      connectedComponentIn (Set.compl (JordanCurveImage γ)) 0 =
        connectedComponentIn (Set.compl (JordanCurveImage γ)) 1 :=
    connectedComponentIn_eq h'
  simpa [JordanInterior, JordanExterior] using h_eq.symm

lemma jordan_curve_interior_exterior_disjoint_of_not_mem (γ : ℝ → ℂ)
    (h : (1 : ℂ) ∉ JordanInterior γ) :
    Disjoint (JordanInterior γ) (JordanExterior γ) := by
  have h' : (1 : ℂ) ∉
      connectedComponentIn (Set.compl (JordanCurveImage γ)) 0 := by
    simpa [JordanInterior] using h
  simpa [JordanInterior, JordanExterior] using
    (connectedComponentIn_disjoint_of_not_mem (F := Set.compl (JordanCurveImage γ))
      (x := (0 : ℂ)) (y := (1 : ℂ)) h')

/-- Placeholder: any point in the complement connects to `0` or `1` in the complement. -/
lemma jordan_compl_path_to_zero_or_one (γ : ℝ → ℂ) (hγ : JordanCurve γ) {z : ℂ}
    (hz : z ∈ Set.compl (JordanCurveImage γ)) :
    (∃ p : Path z 0, ∀ t, p t ∈ Set.compl (JordanCurveImage γ)) ∨
      (∃ p : Path z 1, ∀ t, p t ∈ Set.compl (JordanCurveImage γ)) := by
  -- TODO: core Jordan curve theorem separation (existence of paths).
  sorry

/-- Placeholder: every point in the complement is in the interior or exterior component. -/
lemma jordan_curve_compl_subset_union (γ : ℝ → ℂ) (hγ : JordanCurve γ) :
    Set.compl (JordanCurveImage γ) ⊆ JordanInterior γ ∪ JordanExterior γ := by
  intro z hz
  rcases jordan_compl_path_to_zero_or_one γ hγ hz with ⟨p, hp⟩ | ⟨p, hp⟩
  · exact Or.inl (mem_jordanInterior_of_path γ p hp)
  · exact Or.inr (mem_jordanExterior_of_path γ p hp)

/-- Placeholder: the complement is exactly the union of interior/exterior. -/
lemma jordan_curve_compl_decomp (γ : ℝ → ℂ) (hγ : JordanCurve γ) :
    Set.compl (JordanCurveImage γ) =
        JordanInterior γ ∪ JordanExterior γ := by
  have h_union : JordanInterior γ ∪ JordanExterior γ ⊆ Set.compl (JordanCurveImage γ) := by
    intro z hz
    rcases hz with hz | hz
    · exact jordan_interior_subset_compl γ hz
    · exact jordan_exterior_subset_compl γ hz
  have h_compl : Set.compl (JordanCurveImage γ) ⊆ JordanInterior γ ∪ JordanExterior γ :=
    jordan_curve_compl_subset_union γ hγ
  exact subset_antisymm h_compl h_union

/-- Placeholder: interior and exterior components are disjoint. -/
lemma jordan_curve_interior_exterior_disjoint (γ : ℝ → ℂ) (hγ : JordanCurve γ) :
    Disjoint (JordanInterior γ) (JordanExterior γ) := by
  by_cases h0 : (0 : ℂ) ∈ JordanCurveImage γ
  · have h0' : (0 : ℂ) ∉ Set.compl (JordanCurveImage γ) := by
      intro h0compl
      exact h0compl h0
    have hempty : JordanInterior γ = ∅ := by
      simpa [JordanInterior] using (connectedComponentIn_eq_empty h0')
    simpa [hempty]
  by_cases h1 : (1 : ℂ) ∈ JordanCurveImage γ
  · have h1' : (1 : ℂ) ∉ Set.compl (JordanCurveImage γ) := by
      intro h1compl
      exact h1compl h1
    have hempty : JordanExterior γ = ∅ := by
      simpa [JordanExterior] using (connectedComponentIn_eq_empty h1')
    simpa [hempty]
  by_cases h : (1 : ℂ) ∈ JordanInterior γ
  · -- TODO: show the interior cannot contain `1` for a Jordan curve.
    -- This should be ruled out by Jordan separation.
    sorry
  · exact jordan_curve_interior_exterior_disjoint_of_not_mem γ h

-- TODO: local separation at curve points: every neighborhood hits the interior.
-- TODO: the curve has empty interior; any neighborhood of a curve point meets the complement.
lemma jordan_curve_image_interior_empty (γ : ℝ → ℂ) (hγ : JordanCurve γ) :
    interior (JordanCurveImage γ) = ∅ := by
  -- TODO: show the image of a Jordan curve has empty interior in ℂ.
  sorry

lemma jordan_curve_neighborhood_meets_compl (γ : ℝ → ℂ) (hγ : JordanCurve γ)
    {z : ℂ} (hz : z ∈ JordanCurveImage γ) (U : Set ℂ)
    (hU : IsOpen U) (hzU : z ∈ U) :
    (U ∩ Set.compl (JordanCurveImage γ)).Nonempty := by
  -- Core Jordan curve theorem: the curve has empty interior and is a separator.
  by_contra hne
  have hsubset : U ⊆ JordanCurveImage γ := by
    intro w hw
    by_contra hnot
    exact hne ⟨w, hw, hnot⟩
  have hU_nhds : U ∈ 𝓝 z := IsOpen.mem_nhds hU hzU
  have hnhds : JordanCurveImage γ ∈ 𝓝 z :=
    Filter.mem_of_superset hU_nhds hsubset
  have hz_int : z ∈ interior (JordanCurveImage γ) :=
    (mem_interior_iff_mem_nhds).2 hnhds
  have h_empty := jordan_curve_image_interior_empty γ hγ
  simpa [h_empty] using hz_int

-- TODO: local separation inside the complement near a curve point.
lemma jordan_curve_neighborhood_meets_interior_or_exterior (γ : ℝ → ℂ) (hγ : JordanCurve γ)
    {z : ℂ} (hz : z ∈ JordanCurveImage γ) (U : Set ℂ)
    (hU : IsOpen U) (hzU : z ∈ U) :
    (U ∩ JordanInterior γ).Nonempty ∨ (U ∩ JordanExterior γ).Nonempty := by
  -- Use a point of `U` in the complement and the path-to-zero-or-one lemma.
  sorry

lemma jordan_curve_local_separation (γ : ℝ → ℂ) (hγ : JordanCurve γ)
    {z : ℂ} (hz : z ∈ JordanCurveImage γ) (U : Set ℂ)
    (hU : IsOpen U) (hzU : z ∈ U) :
    (U ∩ JordanInterior γ).Nonempty := by
  -- Core Jordan curve theorem boundary statement.
  -- TODO: upgrade from `interior_or_exterior` using disjointness and local arguments.
  rcases jordan_curve_neighborhood_meets_interior_or_exterior γ hγ hz U hU hzU with hUin | hUout
  · exact hUin
  · -- TODO: rule out exterior-only neighborhoods.
    sorry

-- TODO: show the curve image lies in the closure of the interior component.
lemma jordan_curve_image_subset_closure_interior (γ : ℝ → ℂ) (hγ : JordanCurve γ) :
    JordanCurveImage γ ⊆ closure (JordanInterior γ) := by
  intro z hz
  refine (mem_closure_iff).2 ?_
  intro U hU hzU
  -- TODO: show any neighborhood of a curve point intersects the interior.
  -- This is a core Jordan curve theorem boundary statement.
  exact jordan_curve_local_separation γ hγ hz U hU hzU

lemma jordan_curve_image_subset_frontier_interior (γ : ℝ → ℂ) (hγ : JordanCurve γ) :
    JordanCurveImage γ ⊆ frontier (JordanInterior γ) := by
  -- TODO: show the curve lies in the closure of the interior.
  have h_closure : JordanCurveImage γ ⊆ closure (JordanInterior γ) :=
    jordan_curve_image_subset_closure_interior γ hγ
  have h_compl : JordanCurveImage γ ⊆ closure (JordanInterior γ)ᶜ := by
    intro z hz
    have hz_not : z ∉ JordanInterior γ := by
      intro hz_in
      exact (jordan_interior_subset_compl γ hz_in) hz
    have hz_mem : z ∈ (JordanInterior γ)ᶜ := hz_not
    exact subset_closure hz_mem
  intro z hz
  have hz' : z ∈ closure (JordanInterior γ) ∩ closure (JordanInterior γ)ᶜ :=
    ⟨h_closure hz, h_compl hz⟩
  simpa [frontier_eq_closure_inter_closure] using hz'

/-- Jordan curve theorem (placeholder): complement decomposition, disjointness, and boundary. -/
theorem jordan_curve_theorem (γ : ℝ → ℂ) (hγ : JordanCurve γ) :
    Set.compl (JordanCurveImage γ) =
        JordanInterior γ ∪ JordanExterior γ ∧
      Disjoint (JordanInterior γ) (JordanExterior γ) ∧
      JordanCurveImage γ ⊆ frontier (JordanInterior γ) := by
  refine ⟨jordan_curve_compl_decomp γ hγ, ?_, ?_⟩
  · exact jordan_curve_interior_exterior_disjoint γ hγ
  · exact jordan_curve_image_subset_frontier_interior γ hγ

end

end MLC.Quadratic
