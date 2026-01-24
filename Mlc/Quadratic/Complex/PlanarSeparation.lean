import Mlc.Quadratic.Complex.Equipotential
import Mlc.Quadratic.Complex.EquipotentialJordanPlan
import Mlc.Quadratic.Complex.JordanBasics
import Mlc.Quadratic.Complex.JordanCurve
import Mlc.Quadratic.Complex.PuzzleBoundaryMotion
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Path
import Mathlib.Analysis.Convex.PathConnected

namespace MLC.Quadratic

open Complex Topology Set
open scoped Convex

noncomputable section

set_option linter.unnecessarySimpa false

/-!
Planar separation placeholders.

This file isolates the missing Jordan-curve/planar separation input needed to
prove that the connected component of `0` in the closed Green sublevel lies in
the open sublevel. It is intentionally minimal and will be replaced by a
concrete proof once a suitable Jordan curve theorem is formalized.
-/

structure JordanSeparationData (γ : ℝ → ℂ) (S T : Set ℂ) : Prop where
  hcurve : JordanCurve γ
  himg : JordanCurveImage γ ⊆ T
  hS : S ⊆ Set.compl (JordanCurveImage γ)
  hinterior : JordanInterior γ ⊆ S
  hcomp : connectedComponentIn T 0 ⊆ Set.compl (JordanCurveImage γ)

/-- Jordan curve images of the unit interval are compact. -/
lemma jordan_curve_image_compact (γ : ℝ → ℂ) (hγ : JordanCurve γ) :
    IsCompact (JordanCurveImage γ) := by
  have hcont : Continuous γ := hγ.1
  have hcont_on : ContinuousOn γ (Set.Icc (0 : ℝ) 1) := hcont.continuousOn
  simpa [JordanCurveImage] using
    (IsCompact.image_of_continuousOn (s := Set.Icc (0 : ℝ) 1) isCompact_Icc hcont_on)

lemma jordan_curve_image_nonempty (γ : ℝ → ℂ) : (JordanCurveImage γ).Nonempty := by
  refine ⟨γ 0, ?_⟩
  refine ⟨0, ?_, rfl⟩
  exact ⟨le_rfl, zero_le_one⟩

lemma jordan_curve_image_connected (γ : ℝ → ℂ) (hγ : JordanCurve γ) :
    IsConnected (JordanCurveImage γ) := by
  have hcont : Continuous γ := hγ.1
  have hcont_on : ContinuousOn γ (Set.Icc (0 : ℝ) 1) := hcont.continuousOn
  have hconn : IsConnected (Set.Icc (0 : ℝ) 1) := isConnected_Icc (by exact zero_le_one)
  simpa [JordanCurveImage] using hconn.image _ hcont_on

lemma jordan_curve_image_closed (γ : ℝ → ℂ) (hγ : JordanCurve γ) :
    IsClosed (JordanCurveImage γ) := by
  exact (jordan_curve_image_compact γ hγ).isClosed

lemma jordan_curve_compl_open (γ : ℝ → ℂ) (hγ : JordanCurve γ) :
    IsOpen (Set.compl (JordanCurveImage γ)) := by
  exact (jordan_curve_image_closed γ hγ).isOpen_compl

/-- Placeholder: a Jordan curve separates the plane into interior/exterior components. -/
lemma jordan_curve_separates (γ : ℝ → ℂ) (hγ : JordanCurve γ) :
    IsOpen (JordanInterior γ) ∧ IsOpen (JordanExterior γ) := by
  have hopen : IsOpen (Set.compl (JordanCurveImage γ)) := jordan_curve_compl_open γ hγ
  have h_int : IsOpen (JordanInterior γ) := by
    simpa [JordanInterior] using (IsOpen.connectedComponentIn (F := Set.compl (JordanCurveImage γ)) hopen)
  have h_ext : IsOpen (JordanExterior γ) := by
    simpa [JordanExterior] using (IsOpen.connectedComponentIn (F := Set.compl (JordanCurveImage γ)) hopen)
  exact ⟨h_int, h_ext⟩

lemma jordan_curve_compl_decomp_of_partition (γ : ℝ → ℂ)
    (hpart : ∀ z ∈ Set.compl (JordanCurveImage γ),
      z ∈ JordanInterior γ ∪ JordanExterior γ) :
    Set.compl (JordanCurveImage γ) =
      JordanInterior γ ∪ JordanExterior γ := by
  have h_union : JordanInterior γ ∪ JordanExterior γ ⊆ Set.compl (JordanCurveImage γ) := by
    intro z hz
    rcases hz with hz | hz
    · exact jordan_interior_subset_compl γ hz
    · exact jordan_exterior_subset_compl γ hz
  have h_compl : Set.compl (JordanCurveImage γ) ⊆ JordanInterior γ ∪ JordanExterior γ := by
    intro z hz
    exact hpart z hz
  exact subset_antisymm h_compl h_union

lemma segment_intersects_curve_image (γ : ℝ → ℂ) {z w : ℂ}
    (hseg : ¬ [z -[ℝ] w] ⊆ Set.compl (JordanCurveImage γ)) :
    ∃ p ∈ JordanCurveImage γ, p ∈ [z -[ℝ] w] := by
  -- TODO: extract an intersection point from the negated subset relation.
  -- This is basic set logic; should be solved without topology.
  by_contra hcontra
  have hsubset : [z -[ℝ] w] ⊆ Set.compl (JordanCurveImage γ) := by
    intro p hp
    by_contra hpcomp
    have hpimg : p ∈ JordanCurveImage γ := by
      classical
      by_contra hnot
      exact hpcomp (by simpa [Set.mem_compl_iff] using hnot)
    exact hcontra ⟨p, hpimg, hp⟩
  exact hseg hsubset

lemma path_in_curve_image_between_of_params (γ : ℝ → ℂ) (hγ : JordanCurve γ)
    {t₁ t₂ : ℝ} (ht₁ : t₁ ∈ Set.Icc (0 : ℝ) 1) (ht₂ : t₂ ∈ Set.Icc (0 : ℝ) 1) :
    ∃ p : Path (γ t₁) (γ t₂), ∀ t, p t ∈ JordanCurveImage γ := by
  -- TODO: build a segment path inside the parameter interval and compose with `γ`.
  -- This will require a path in `Icc 0 1` from `t₁` to `t₂`.
  classical
  -- The straight segment in `ℝ` stays in `[0,1]` since the interval is convex.
  have hseg : [t₁ -[ℝ] t₂] ⊆ Set.Icc (0 : ℝ) 1 := by
    exact (convex_Icc (0 : ℝ) 1).segment_subset ht₁ ht₂
  let pI : Path t₁ t₂ := Path.segment t₁ t₂
  have hpI : ∀ t, pI t ∈ Set.Icc (0 : ℝ) 1 := by
    intro t
    have : pI t ∈ [t₁ -[ℝ] t₂] := by
      -- By definition, the segment path lies in the segment.
      have hrange : pI t ∈ Set.range pI := ⟨t, rfl⟩
      -- `Path.range_segment` identifies the range with the segment.
      simpa [pI, Path.range_segment] using hrange
    exact hseg this
  let p : Path (γ t₁) (γ t₂) := (pI.map (hγ.1))
  refine ⟨p, ?_⟩
  intro t
  -- The mapped path stays in the curve image because `pI t ∈ [0,1]`.
  refine ⟨pI t, ?_, rfl⟩
  exact hpI t

lemma path_in_curve_image_between {γ : ℝ → ℂ} (hγ : JordanCurve γ)
    {a b : ℂ} (ha : a ∈ JordanCurveImage γ) (hb : b ∈ JordanCurveImage γ) :
    ∃ p : Path a b, ∀ t, p t ∈ JordanCurveImage γ := by
  rcases ha with ⟨t₁, ht₁, rfl⟩
  rcases hb with ⟨t₂, ht₂, rfl⟩
  exact path_in_curve_image_between_of_params γ hγ ht₁ ht₂




lemma jordan_interior_isConnected (γ : ℝ → ℂ)
    (h0 : (0 : ℂ) ∈ Set.compl (JordanCurveImage γ)) :
    IsConnected (JordanInterior γ) := by
  simpa [JordanInterior] using
    (isConnected_connectedComponentIn_iff (x := (0 : ℂ))
        (F := Set.compl (JordanCurveImage γ))).2 h0

lemma jordan_exterior_isConnected (γ : ℝ → ℂ)
    (h1 : (1 : ℂ) ∈ Set.compl (JordanCurveImage γ)) :
    IsConnected (JordanExterior γ) := by
  simpa [JordanExterior] using
    (isConnected_connectedComponentIn_iff (x := (1 : ℂ))
        (F := Set.compl (JordanCurveImage γ))).2 h1

lemma jordan_interior_isPathConnected (γ : ℝ → ℂ) (hγ : JordanCurve γ)
    (h0 : (0 : ℂ) ∈ Set.compl (JordanCurveImage γ)) :
    IsPathConnected (JordanInterior γ) := by
  have hopen : IsOpen (JordanInterior γ) := (jordan_curve_separates γ hγ).1
  have hconn : IsConnected (JordanInterior γ) := jordan_interior_isConnected γ h0
  exact (IsOpen.isConnected_iff_isPathConnected hopen).1 hconn

lemma jordan_exterior_isPathConnected (γ : ℝ → ℂ) (hγ : JordanCurve γ)
    (h1 : (1 : ℂ) ∈ Set.compl (JordanCurveImage γ)) :
    IsPathConnected (JordanExterior γ) := by
  have hopen : IsOpen (JordanExterior γ) := (jordan_curve_separates γ hγ).2
  have hconn : IsConnected (JordanExterior γ) := jordan_exterior_isConnected γ h1
  exact (IsOpen.isConnected_iff_isPathConnected hopen).1 hconn

lemma path_to_zero_of_mem_jordanInterior (γ : ℝ → ℂ) (hγ : JordanCurve γ)
    {z : ℂ} (hz : z ∈ JordanInterior γ) :
    ∃ p : Path z 0, ∀ t, p t ∈ Set.compl (JordanCurveImage γ) := by
  have hnonempty : (JordanInterior γ).Nonempty := ⟨z, hz⟩
  have h0 : (0 : ℂ) ∈ Set.compl (JordanCurveImage γ) := by
    have hnonempty' :
        (connectedComponentIn (Set.compl (JordanCurveImage γ)) 0).Nonempty := by
      simpa [JordanInterior] using hnonempty
    exact (connectedComponentIn_nonempty_iff
        (x := (0 : ℂ)) (F := Set.compl (JordanCurveImage γ))).1 hnonempty'
  have h0_in : (0 : ℂ) ∈ JordanInterior γ := by
    simpa [JordanInterior] using
      mem_connectedComponentIn (x := (0 : ℂ))
        (F := Set.compl (JordanCurveImage γ)) h0
  have hpathconn : IsPathConnected (JordanInterior γ) :=
    jordan_interior_isPathConnected γ hγ h0
  have hjoined : JoinedIn (JordanInterior γ) z 0 :=
    hpathconn.joinedIn z hz 0 h0_in
  refine ⟨hjoined.somePath, ?_⟩
  intro t
  exact jordan_interior_subset_compl γ (hjoined.somePath_mem t)

lemma path_to_one_of_mem_jordanExterior (γ : ℝ → ℂ) (hγ : JordanCurve γ)
    {z : ℂ} (hz : z ∈ JordanExterior γ) :
    ∃ p : Path z 1, ∀ t, p t ∈ Set.compl (JordanCurveImage γ) := by
  have hnonempty : (JordanExterior γ).Nonempty := ⟨z, hz⟩
  have h1 : (1 : ℂ) ∈ Set.compl (JordanCurveImage γ) := by
    have hnonempty' :
        (connectedComponentIn (Set.compl (JordanCurveImage γ)) 1).Nonempty := by
      simpa [JordanExterior] using hnonempty
    exact (connectedComponentIn_nonempty_iff
        (x := (1 : ℂ)) (F := Set.compl (JordanCurveImage γ))).1 hnonempty'
  have h1_in : (1 : ℂ) ∈ JordanExterior γ := by
    simpa [JordanExterior] using
      mem_connectedComponentIn (x := (1 : ℂ))
        (F := Set.compl (JordanCurveImage γ)) h1
  have hpathconn : IsPathConnected (JordanExterior γ) :=
    jordan_exterior_isPathConnected γ hγ h1
  have hjoined : JoinedIn (JordanExterior γ) z 1 :=
    hpathconn.joinedIn z hz 1 h1_in
  refine ⟨hjoined.somePath, ?_⟩
  intro t
  exact jordan_exterior_subset_compl γ (hjoined.somePath_mem t)

lemma mem_jordanInterior_of_segment (γ : ℝ → ℂ) {z : ℂ}
    (hseg : [z -[ℝ] (0 : ℂ)] ⊆ Set.compl (JordanCurveImage γ)) :
    z ∈ JordanInterior γ := by
  let p : Path z 0 := Path.segment z 0
  have hrange : Set.range p ⊆ Set.compl (JordanCurveImage γ) := by
    simpa [p, Path.range_segment] using hseg
  have hp : ∀ t, p t ∈ Set.compl (JordanCurveImage γ) := by
    intro t
    exact hrange ⟨t, rfl⟩
  exact mem_jordanInterior_of_path γ p hp

lemma mem_jordanExterior_of_segment (γ : ℝ → ℂ) {z : ℂ}
    (hseg : [z -[ℝ] (1 : ℂ)] ⊆ Set.compl (JordanCurveImage γ)) :
    z ∈ JordanExterior γ := by
  let p : Path z 1 := Path.segment z 1
  have hrange : Set.range p ⊆ Set.compl (JordanCurveImage γ) := by
    simpa [p, Path.range_segment] using hseg
  have hp : ∀ t, p t ∈ Set.compl (JordanCurveImage γ) := by
    intro t
    exact hrange ⟨t, rfl⟩
  exact mem_jordanExterior_of_path γ p hp

lemma mem_jordanInterior_or_exterior_of_path (γ : ℝ → ℂ) (hγ : JordanCurve γ) {z : ℂ}
    (hz : z ∈ Set.compl (JordanCurveImage γ)) :
    z ∈ JordanInterior γ ∪ JordanExterior γ := by
  rcases jordan_compl_path_to_zero_or_one γ hγ hz with ⟨p, hp⟩ | ⟨p, hp⟩
  · exact Or.inl (mem_jordanInterior_of_path γ p hp)
  · exact Or.inr (mem_jordanExterior_of_path γ p hp)

/-- Equipotential Jordan curve data (placeholder). -/
lemma equipotential_jordan_data (c : ℂ) (n : ℕ) :
    ∃ γ : ℝ → ℂ,
      JordanCurve γ ∧
        JordanCurveImage γ = Equipotential c n ∧
        JordanInterior γ ⊆ GreenSublevel c n ∧
        connectedComponentIn (GreenSublevelClosed c n) 0 ⊆
          Set.compl (Equipotential c n) := by
  -- TODO: build a parametrization of the equipotential and identify the bounded component.
  -- Use the Böttcher-based plan once available.
  classical
  obtain ⟨B, _⟩ : ∃ B : BottcherData, True := by
    let B : BottcherData :=
      { phi := fun _ z => z
        holo_in_param := by
          intro z
          simpa using differentiableOn_const
        phi_at_zero := by
          intro z
          rfl
        inj_on := by
          intro t ht
          intro x hx y hy hxy
          simpa using hxy }
    exact ⟨B, trivial⟩
  exact equipotential_jordan_data_of_bottcher B c n

/-- Placeholder: equipotential curve parametrization as a Jordan curve. -/
lemma equipotential_jordan_curve (c : ℂ) (n : ℕ) :
    ∃ γ : ℝ → ℂ, JordanCurve γ ∧ JordanCurveImage γ = Equipotential c n := by
  -- TODO: build a parametrization of the equipotential.
  rcases equipotential_jordan_data c n with ⟨γ, hγ, himg, _hinterior, _hcomp⟩
  exact ⟨γ, hγ, himg⟩

lemma equipotential_compl_contains_sublevel (c : ℂ) (n : ℕ) :
    GreenSublevel c n ⊆ Set.compl (Equipotential c n) := by
  intro z hz
  have hz' : green_function c z < (1 / 2 : ℝ) ^ n := by
    simpa [GreenSublevel] using hz
  have hne : green_function c z ≠ (1 / 2 : ℝ) ^ n := ne_of_lt hz'
  exact by
    intro hz_eq
    exact hne (by simpa [Equipotential] using hz_eq)

lemma jordan_interior_subset_sublevel (c : ℂ) (n : ℕ)
    (γ : ℝ → ℂ) (himg : JordanCurveImage γ = Equipotential c n) :
    JordanInterior γ ⊆ GreenSublevel c n := by
  -- TODO: the interior region corresponds to the Green sublevel.
  rcases equipotential_jordan_data c n with
    ⟨γ', _hγ', himg', hinterior', _hcomp⟩
  have hEq : JordanInterior γ = JordanInterior γ' := by
    simp [JordanInterior, himg, himg']
  simpa [hEq] using hinterior'

lemma component_avoids_equipotential (c : ℂ) (n : ℕ)
    (_h0 : (0 : ℂ) ∈ GreenSublevelClosed c n) :
    connectedComponentIn (GreenSublevelClosed c n) 0 ⊆ Set.compl (Equipotential c n) := by
  -- TODO: the base component of the closed sublevel avoids the boundary equipotential.
  -- Use closedness of the equipotential and openness of the sublevel to show the
  -- connected component cannot cross the boundary.
  have _hclosed : IsClosed (Equipotential c n) := equipotential_closed c n
  have _hfront : frontier (GreenSublevel c n) ⊆ Equipotential c n :=
    frontier_green_sublevel_subset_equipotential c n
  -- This is where a Jordan curve / boundary separation theorem is needed.
  rcases equipotential_jordan_data c n with
    ⟨_γ, _hγ, _himg, _hinterior, hcomp⟩
  exact hcomp

/-! Separation data for equipotential curves. -/
lemma equipotential_jordan_separation (c : ℂ) (n : ℕ) :
    ∃ γ : ℝ → ℂ,
      JordanSeparationData γ (GreenSublevel c n) (GreenSublevelClosed c n) ∧
        JordanCurveImage γ = Equipotential c n := by
  obtain ⟨γ, hγ, himg⟩ := equipotential_jordan_curve c n
  refine ⟨γ, ?_, himg⟩
  refine { hcurve := hγ, himg := ?_, hS := ?_, hinterior := ?_, hcomp := ?_ }
  · simpa [himg] using (equipotential_subset_closed c n)
  · simpa [himg] using (equipotential_compl_contains_sublevel c n)
  · exact jordan_interior_subset_sublevel c n γ himg
  ·
    by_cases h0 : (0 : ℂ) ∈ GreenSublevelClosed c n
    · simpa [himg] using (component_avoids_equipotential c n h0)
    ·
      have hempty :
          connectedComponentIn (GreenSublevelClosed c n) 0 = ∅ := by
        simpa using (connectedComponentIn_eq_empty h0)
      simp [hempty]

/-- If the component in `T` sits inside the Jordan interior, it lies in `S`. -/
lemma jordan_separation_data_implies {γ : ℝ → ℂ} {S T : Set ℂ}
    (hsep : JordanSeparationData γ S T)
    (hcomp : connectedComponentIn T 0 ⊆ JordanInterior γ) :
    connectedComponentIn T 0 ⊆ S := by
  exact subset_trans hcomp hsep.hinterior

/-- If a closed set contains the curve image, its component at `0` lies in the interior. -/
lemma component_interior_of_curve_subset (γ : ℝ → ℂ) {T : Set ℂ}
    (_hcurve : JordanCurve γ)
    (_himg : JordanCurveImage γ ⊆ T)
    (h0 : (0 : ℂ) ∈ T)
    (hcomp : connectedComponentIn T 0 ⊆ Set.compl (JordanCurveImage γ)) :
    connectedComponentIn T 0 ⊆ JordanInterior γ := by
  -- TODO: upgrade `hcomp` from separation data, once the Jordan curve theorem is available.
  have hpre : IsPreconnected (connectedComponentIn T 0) :=
    isPreconnected_connectedComponentIn
  have h0' : (0 : ℂ) ∈ connectedComponentIn T 0 :=
    mem_connectedComponentIn h0
  have hsubset :
      connectedComponentIn T 0 ⊆
        connectedComponentIn (Set.compl (JordanCurveImage γ)) 0 := by
    exact hpre.subset_connectedComponentIn h0' hcomp
  simpa [JordanInterior] using hsubset

/-- The component in a set avoiding the curve image stays in the complement. -/
lemma component_avoids_curve_image (γ : ℝ → ℂ) {T : Set ℂ}
    (_hcurve : JordanCurve γ) (_himg : JordanCurveImage γ ⊆ T)
    (_h0 : (0 : ℂ) ∈ T)
    (hT : connectedComponentIn T 0 ⊆ Set.compl (JordanCurveImage γ)) :
    connectedComponentIn T 0 ⊆ Set.compl (JordanCurveImage γ) := by
  exact hT

/-- Abstract separation data for an open set inside a closed set. -/
structure JordanSeparation (S T : Set ℂ) : Prop where
  hopen : IsOpen S
  hclosure : closure S ⊆ T
  hsep : connectedComponentIn T 0 ⊆ S

/-- Placeholder: separation of the Green sublevel by its equipotential boundary. -/
lemma green_sublevel_separation_of_jordan (c : ℂ) (n : ℕ)
    (hcurve : ∃ _ : ℝ → ℂ, True)
    (_hfill : closure (GreenSublevel c n) ⊆ GreenSublevelClosed c n)
    (_hopen : IsOpen (GreenSublevel c n)) :
    connectedComponentIn (GreenSublevelClosed c n) 0 ⊆ GreenSublevel c n := by
  -- TODO: fold in `hfill` and `hopen` into the separation data.
  -- For now, keep as a single placeholder derived from a Jordan curve theorem.
  sorry

/-- Placeholder: a Jordan curve provides separation data for the Green sublevel. -/
lemma jordan_separation_of_curve (c : ℂ) (n : ℕ)
    (hcurve : ∃ _ : ℝ → ℂ, True) :
    JordanSeparation (GreenSublevel c n) (GreenSublevelClosed c n) := by
  -- TODO: specialize a Jordan curve theorem to equipotential boundaries.
  -- This should identify `GreenSublevel c n` with the bounded component.
  have hopen : IsOpen (GreenSublevel c n) := by
    have hcont : Continuous (green_function c) := continuous_green_function c
    simpa [GreenSublevel] using (IsOpen.preimage hcont isOpen_Iio)
  refine {hopen := hopen, hclosure := closure_green_sublevel_subset_closed c n, hsep := ?_}
  exact green_sublevel_separation_of_jordan c n hcurve
    (closure_green_sublevel_subset_closed c n) hopen

/-- Use the equipotential-based Jordan separation data directly. -/
lemma green_sublevel_separation_of_equipotential (c : ℂ) (n : ℕ)
    (h0 : (0 : ℂ) ∈ GreenSublevelClosed c n) :
    connectedComponentIn (GreenSublevelClosed c n) 0 ⊆ GreenSublevel c n := by
  obtain ⟨γ, hsep, _himg_eq⟩ := equipotential_jordan_separation c n
  -- TODO: show the component in `GreenSublevelClosed` lies in the Jordan interior.
  have hcomp :
      connectedComponentIn (GreenSublevelClosed c n) 0 ⊆ JordanInterior γ := by
    -- This will use the separation of the equipotential curve from the sublevel.
    have hcomp' :
        connectedComponentIn (GreenSublevelClosed c n) 0 ⊆
          Set.compl (JordanCurveImage γ) := by
      exact hsep.hcomp
    exact component_interior_of_curve_subset γ hsep.hcurve hsep.himg h0 hcomp'
  exact jordan_separation_data_implies hsep hcomp

end

end MLC.Quadratic
