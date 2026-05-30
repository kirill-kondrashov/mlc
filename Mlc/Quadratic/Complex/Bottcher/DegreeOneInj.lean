import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Algebra.OpenSubgroup
import Mlc.Quadratic.Complex.InverseBranchQuadratic
import Mlc.Quadratic.Complex.Bottcher.BottcherOutsidePlan

/-!
# Degree One Injectivity Lemma (Sketch)

This file sketches the topological argument required to close the "Local Homeomorph Branch"
of the CP5 residual seam.

The core claim is that a proper local homeomorphism between planar domains that behaves like
the identity at infinity (degree 1) must be globally injective.

Mathematically:
1. A proper local homeomorphism between connected, locally connected spaces is a covering map.
2. The degree of a covering map is the cardinality of the fiber.
3. Behavior at infinity (asymptotic to identity) fixes the degree to 1.
4. A degree 1 covering map is a homeomorphism (hence injective).
-/

open Complex Filter Metric Set Function Topology

namespace Mlc.Bottcher.DegreeOne

section ProperLocalHomeomorphFibers

variable {X Y : Type*} [PseudoMetricSpace X] [T2Space X] [TopologicalSpace Y]

omit [T2Space X] [TopologicalSpace Y] in
lemma isDiscrete_fiber_of_isLocallyInjective
    {f : X → Y} (hlocal : IsLocallyInjective f) (y : Y) :
    IsDiscrete ({x : X | f x = y} : Set X) := by
  classical
  refine (isDiscrete_iff_forall_exists_isOpen).2 ?_
  intro x hx
  rcases hlocal x with ⟨U, hUopen, hxU, hUinj⟩
  refine ⟨U, hUopen, ?_⟩
  ext z
  constructor
  · intro hz
    have hzU : z ∈ U := hz.1
    have hzf : f z = y := hz.2
    have hxf : f x = y := hx
    have : z = x := hUinj hzU hxU (by simp [hxf, hzf])
    simp [this]
  · intro hz
    rcases hz with rfl
    exact ⟨hxU, hx⟩

omit [T2Space X] in
lemma finite_fiber_of_isProperMap_isLocallyInjective
    {f : X → Y} (hproper : IsProperMap f) (hlocal : IsLocallyInjective f) (y : Y) :
    ({x : X | f x = y} : Set X).Finite := by
  have hcompact : IsCompact ((fun x : X => f x) ⁻¹' {y}) :=
    hproper.isCompact_preimage isCompact_singleton
  have hdisc : IsDiscrete ({x : X | f x = y} : Set X) :=
    isDiscrete_fiber_of_isLocallyInjective hlocal y
  have hpre : (f ⁻¹' ({y} : Set Y)) = ({x : X | f x = y} : Set X) := by
    ext x
    simp
  simpa [hpre] using hcompact.finite hdisc

lemma exists_pairwise_disjoint_ball_of_finite {s : Set X} (hs : s.Finite) :
    ∃ r : s → ℝ, (∀ x, 0 < r x) ∧
      Pairwise (fun x y => Disjoint (Metric.ball x.1 (r x)) (Metric.ball y.1 (r y))) := by
  classical
  by_cases hsubs : s.Subsingleton
  · refine ⟨fun _ => (1 : ℝ), ?_, ?_⟩
    · intro x; norm_num
    · intro x y hne
      have : x = y := by
        have hxy : x.1 = y.1 := hsubs x.property y.property
        exact Subtype.ext hxy
      exact (hne this).elim
  · let r : s → ℝ := fun x =>
      if hne : (s \ {x.1}).Nonempty then
        (Metric.infDist x.1 (s \ {x.1})) / 2
      else 1
    have hrpos : ∀ x, 0 < r x := by
      intro x
      by_cases hne : (s \ {x.1}).Nonempty
      · have hclosed : IsClosed (s \ {x.1}) :=
          (hs.subset (by intro y hy; exact hy.1)).isClosed
        have hxnot : x.1 ∉ s \ {x.1} := by
          simp
        have hpos : 0 < Metric.infDist x.1 (s \ {x.1}) := by
          have := (IsClosed.notMem_iff_infDist_pos (x := x.1) (s := s \ {x.1})
            hclosed hne).1
          exact this hxnot
        have hpos' : 0 < Metric.infDist x.1 (s \ {x.1}) / 2 := by
          nlinarith
        simpa [r, hne] using hpos'
      · simp [r, hne]
    refine ⟨r, hrpos, ?_⟩
    intro x y hne
    have hxy : x.1 ≠ y.1 := by
      intro h
      apply hne
      exact Subtype.ext h
    have hy_mem : y.1 ∈ s \ {x.1} := by
      exact ⟨y.property, by simpa [Set.mem_singleton_iff, eq_comm] using hxy⟩
    have hx_mem : x.1 ∈ s \ {y.1} := by
      exact ⟨x.property, by simpa [Set.mem_singleton_iff] using hxy⟩
    have hxne : (s \ {x.1}).Nonempty := ⟨y.1, hy_mem⟩
    have hyne : (s \ {y.1}).Nonempty := ⟨x.1, hx_mem⟩
    have hxle : r x ≤ dist x.1 y.1 / 2 := by
      have h := Metric.infDist_le_dist_of_mem (x := x.1) (s := s \ {x.1}) hy_mem
      have h' : Metric.infDist x.1 (s \ {x.1}) / 2 ≤ dist x.1 y.1 / 2 := by
        nlinarith [h]
      simpa [r, hxne] using h'
    have hyle : r y ≤ dist x.1 y.1 / 2 := by
      have h := Metric.infDist_le_dist_of_mem (x := y.1) (s := s \ {y.1}) hx_mem
      have h' : Metric.infDist y.1 (s \ {y.1}) / 2 ≤ dist y.1 x.1 / 2 := by
        nlinarith [h]
      have h'' : dist y.1 x.1 = dist x.1 y.1 := by simp [dist_comm]
      simpa [r, hyne, h''] using h'
    have hsum : r x + r y ≤ dist x.1 y.1 := by
      have : r x + r y ≤ dist x.1 y.1 / 2 + dist x.1 y.1 / 2 :=
        add_le_add hxle hyle
      have hhalf : dist x.1 y.1 / 2 + dist x.1 y.1 / 2 = dist x.1 y.1 := by ring
      simpa [hhalf] using this
    exact Metric.ball_disjoint_ball hsum

omit [T2Space X] in
lemma exists_open_preimage_subset_of_closedMap_of_fiber_subset
    {f : X → Y} (hclosed : IsClosedMap f) {y : Y} {U : Set X}
    (hUopen : IsOpen U)
    (hfiber : ({x : X | f x = y} : Set X) ⊆ U) :
    ∃ V, IsOpen V ∧ y ∈ V ∧ f ⁻¹' V ⊆ U := by
  have hy_not_in : y ∉ f '' Uᶜ := by
    intro hy
    rcases hy with ⟨x, hxU, hxy⟩
    have hxFiber : x ∈ ({x : X | f x = y} : Set X) := by
      simp [Set.mem_setOf_eq, hxy]
    exact hxU (hfiber hxFiber)
  let V : Set Y := (f '' Uᶜ)ᶜ
  have hVopen : IsOpen V := by
    change IsOpen ((f '' Uᶜ)ᶜ)
    exact (hclosed _ hUopen.isClosed_compl).isOpen_compl
  have hyV : y ∈ V := by
    simpa [V] using hy_not_in
  refine ⟨V, hVopen, hyV, ?_⟩
  intro x hx
  by_contra hxU
  have : f x ∈ f '' Uᶜ := ⟨x, hxU, rfl⟩
  exact hx this

lemma exists_open_preimage_subset_iUnion_disjoint_inj_of_finite_fiber
    {f : X → Y} (hclosed : IsClosedMap f) (hlocal : IsLocalHomeomorph f) {y : Y}
    (hfinite : ({x : X | f x = y} : Set X).Finite) :
    ∃ V, IsOpen V ∧ y ∈ V ∧
      ∃ U : ({x : X // f x = y}) → Set X,
        (∀ x, IsOpen (U x)) ∧
        (∀ x, x.1 ∈ U x) ∧
        (∀ x, Set.InjOn f (U x)) ∧
        Pairwise (fun x x' => Disjoint (U x) (U x')) ∧
        f ⁻¹' V ⊆ ⋃ x : ({x : X // f x = y}), U x := by
  classical
  have hlocinj : IsLocallyInjective f := hlocal.isLocallyInjective
  choose N hNopen hxN hNinj using (fun x : ({x : X // f x = y}) => hlocinj x.1)
  let s : Set X := {x : X | f x = y}
  have hsfinite : s.Finite := by simpa [s] using hfinite
  rcases exists_pairwise_disjoint_ball_of_finite (s := s) hsfinite with ⟨r, hrpos, hrdisj⟩
  let U : ({x : X // f x = y}) → Set X := fun x => Metric.ball x.1 (r x) ∩ N x
  let Uunion : Set X := ⋃ x : ({x : X // f x = y}), U x
  have hUopen : IsOpen Uunion := by
    unfold Uunion
    refine isOpen_iUnion ?_
    intro x
    exact (Metric.isOpen_ball.inter (hNopen x))
  have hsU : s ⊆ Uunion := by
    intro x hx
    refine mem_iUnion.2 ?_
    refine ⟨⟨x, hx⟩, ?_⟩
    exact ⟨Metric.mem_ball_self (hrpos ⟨x, hx⟩), hxN ⟨x, hx⟩⟩
  rcases exists_open_preimage_subset_of_closedMap_of_fiber_subset
    (f := f) hclosed (y := y) (U := Uunion) hUopen hsU with ⟨V, hVopen, hyV, hpre⟩
  refine ⟨V, hVopen, hyV, U, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    exact (Metric.isOpen_ball.inter (hNopen x))
  · intro x
    exact ⟨Metric.mem_ball_self (hrpos x), hxN x⟩
  · intro x
    exact (hNinj x).mono (by intro z hz; exact hz.2)
  · intro x x' hxx'
    exact (hrdisj hxx').mono (by intro z hz; exact hz.1) (by intro z hz; exact hz.1)
  · simpa [Uunion] using hpre

omit [PseudoMetricSpace X] [T2Space X] [TopologicalSpace Y] in
lemma exists_injective_fiber_map_of_mem_open_of_preimage_subset_iUnion_inj
    {f : X → Y} {y : Y} {V : Set Y}
    {U : ({x : X // f x = y}) → Set X}
    (hpre : f ⁻¹' V ⊆ ⋃ x : ({x : X // f x = y}), U x)
    (hUinj : ∀ x, Set.InjOn f (U x))
    {y' : Y} (hy' : y' ∈ V) :
    ∃ g : ({x : X // f x = y'}) → ({x : X // f x = y}),
      Function.Injective g := by
  classical
  let g : ({x : X // f x = y'}) → ({x : X // f x = y}) := fun z =>
    Classical.choose <| by
      have hzpre : z.1 ∈ f ⁻¹' V := by
        simpa [Set.preimage, z.2] using hy'
      have hzU : z.1 ∈ ⋃ x : ({x : X // f x = y}), U x := hpre hzpre
      exact Set.mem_iUnion.mp hzU
  have hgmem : ∀ z : ({x : X // f x = y'}), z.1 ∈ U (g z) := by
    intro z
    exact Classical.choose_spec <| by
      have hzpre : z.1 ∈ f ⁻¹' V := by
        simpa [Set.preimage, z.2] using hy'
      have hzU : z.1 ∈ ⋃ x : ({x : X // f x = y}), U x := hpre hzpre
      exact Set.mem_iUnion.mp hzU
  refine ⟨g, ?_⟩
  intro z₁ z₂ hz
  have hz₁U : z₁.1 ∈ U (g z₁) := hgmem z₁
  have hz₂U : z₂.1 ∈ U (g z₁) := by
    simpa [hz] using hgmem z₂
  have hf : f z₁.1 = f z₂.1 := by
    simp [z₁.2, z₂.2]
  have hz₁₂ : z₁.1 = z₂.1 := (hUinj (g z₁)) hz₁U hz₂U hf
  exact Subtype.ext hz₁₂

omit [PseudoMetricSpace X] [T2Space X] [TopologicalSpace Y] in
lemma finite_fiber_of_mem_open_of_preimage_subset_iUnion_inj
    {f : X → Y} {y : Y} {V : Set Y}
    {U : ({x : X // f x = y}) → Set X}
    (hpre : f ⁻¹' V ⊆ ⋃ x : ({x : X // f x = y}), U x)
    (hUinj : ∀ x, Set.InjOn f (U x))
    (hfinite : ({x : X | f x = y} : Set X).Finite)
    {y' : Y} (hy' : y' ∈ V) :
    ({x : X | f x = y'} : Set X).Finite := by
  classical
  rcases exists_injective_fiber_map_of_mem_open_of_preimage_subset_iUnion_inj
      (f := f) (y := y) (V := V) (U := U) hpre hUinj hy' with ⟨g, hg⟩
  haveI : Finite ({x : X // f x = y}) := hfinite.to_subtype
  haveI : Finite ({x : X // f x = y'}) := Finite.of_injective g hg
  exact (Set.finite_def).2 ⟨Fintype.ofFinite ({x : X // f x = y'})⟩

omit [PseudoMetricSpace X] [T2Space X] [TopologicalSpace Y] in
lemma natCard_fiber_le_of_mem_open_of_preimage_subset_iUnion_inj
    {f : X → Y} {y : Y} {V : Set Y}
    {U : ({x : X // f x = y}) → Set X}
    (hpre : f ⁻¹' V ⊆ ⋃ x : ({x : X // f x = y}), U x)
    (hUinj : ∀ x, Set.InjOn f (U x))
    (hfinite : ({x : X | f x = y} : Set X).Finite)
    {y' : Y} (hy' : y' ∈ V) :
    Nat.card ({x : X // f x = y'}) ≤ Nat.card ({x : X // f x = y}) := by
  classical
  rcases exists_injective_fiber_map_of_mem_open_of_preimage_subset_iUnion_inj
      (f := f) (y := y) (V := V) (U := U) hpre hUinj hy' with ⟨g, hg⟩
  haveI : Finite ({x : X // f x = y}) := hfinite.to_subtype
  haveI : Finite ({x : X // f x = y'}) := Finite.of_injective g hg
  exact Nat.card_le_card_of_injective g hg

omit [PseudoMetricSpace X] [T2Space X] [TopologicalSpace Y] in
lemma exists_injective_fiber_map_of_mem_iInter_image_of_pairwise_disjoint
    {f : X → Y} {y : Y}
    {U : ({x : X // f x = y}) → Set X}
    (hUdisj : Pairwise (fun x x' => Disjoint (U x) (U x')))
    {y' : Y} (hy' : y' ∈ ⋂ x : ({x : X // f x = y}), f '' U x) :
    ∃ g : ({x : X // f x = y}) → ({x : X // f x = y'}),
      Function.Injective g := by
  classical
  let g : ({x : X // f x = y}) → ({x : X // f x = y'}) := fun x =>
    let hximg : y' ∈ f '' U x := Set.mem_iInter.mp hy' x
    ⟨Classical.choose hximg, (Classical.choose_spec hximg).2⟩
  have hgmem : ∀ x : ({x : X // f x = y}), (g x).1 ∈ U x := by
    intro x
    dsimp [g]
    exact (Classical.choose_spec (Set.mem_iInter.mp hy' x)).1
  refine ⟨g, ?_⟩
  intro x₁ x₂ hx
  by_contra hne
  have hx₁U : (g x₁).1 ∈ U x₁ := hgmem x₁
  have hx₂U : (g x₂).1 ∈ U x₂ := hgmem x₂
  have hx₁U' : (g x₁).1 ∈ U x₂ := by
    simpa [hx] using hx₂U
  have hdisj : Disjoint (U x₁) (U x₂) := hUdisj hne
  exact (Set.disjoint_left.mp hdisj) hx₁U hx₁U'

omit [PseudoMetricSpace X] [T2Space X] [TopologicalSpace Y] in
lemma natCard_fiber_eq_of_mem_open_of_preimage_subset_iUnion_disjoint_inj_and_mem_iInter_image
    {f : X → Y} {y : Y} {V : Set Y}
    {U : ({x : X // f x = y}) → Set X}
    (hpre : f ⁻¹' V ⊆ ⋃ x : ({x : X // f x = y}), U x)
    (hUinj : ∀ x, Set.InjOn f (U x))
    (hUdisj : Pairwise (fun x x' => Disjoint (U x) (U x')))
    (hfinite : ({x : X | f x = y} : Set X).Finite)
    {y' : Y} (hyV : y' ∈ V)
    (hyI : y' ∈ ⋂ x : ({x : X // f x = y}), f '' U x) :
    Nat.card ({x : X // f x = y'}) = Nat.card ({x : X // f x = y}) := by
  classical
  have hle :
      Nat.card ({x : X // f x = y'}) ≤ Nat.card ({x : X // f x = y}) :=
    natCard_fiber_le_of_mem_open_of_preimage_subset_iUnion_inj
      (f := f) (y := y) (V := V) (U := U) hpre hUinj hfinite hyV
  have hfinite' : ({x : X | f x = y'} : Set X).Finite :=
    finite_fiber_of_mem_open_of_preimage_subset_iUnion_inj
      (f := f) (y := y) (V := V) (U := U) hpre hUinj hfinite hyV
  rcases exists_injective_fiber_map_of_mem_iInter_image_of_pairwise_disjoint
      (f := f) (y := y) (U := U) hUdisj hyI with ⟨g, hg⟩
  haveI : Finite ({x : X // f x = y}) := hfinite.to_subtype
  haveI : Finite ({x : X // f x = y'}) := hfinite'.to_subtype
  have hge :
      Nat.card ({x : X // f x = y}) ≤ Nat.card ({x : X // f x = y'}) :=
    Nat.card_le_card_of_injective g hg
  exact le_antisymm hle hge

lemma exists_open_natCard_fiber_eq_of_closedMap_localHomeomorph_of_finite_fiber
    {f : X → Y} (hclosed : IsClosedMap f) (hlocal : IsLocalHomeomorph f) {y : Y}
    (hfinite : ({x : X | f x = y} : Set X).Finite) :
    ∃ V, IsOpen V ∧ y ∈ V ∧
      ∀ y' ∈ V, Nat.card ({x : X // f x = y'}) = Nat.card ({x : X // f x = y}) := by
  classical
  rcases exists_open_preimage_subset_iUnion_disjoint_inj_of_finite_fiber
      (f := f) hclosed hlocal (y := y) hfinite with
    ⟨V0, hV0open, hyV0, U, hUopen, hxU, hUinj, hUdisj, hpre⟩
  let I := ({x : X // f x = y})
  haveI : Finite I := hfinite.to_subtype
  letI : Fintype I := Fintype.ofFinite I
  have hOpenMap : IsOpenMap f := hlocal.isOpenMap
  let Iimgs : Set Y := ⋂ x : I, f '' U x
  have hIimgsOpen : IsOpen Iimgs := by
    unfold Iimgs
    simpa using
      (isOpen_biInter_finset (s := (Finset.univ : Finset I))
        (f := fun x : I => f '' U x) (by intro x _; exact hOpenMap _ (hUopen x)))
  let V : Set Y := V0 ∩ Iimgs
  have hVopen : IsOpen V := hV0open.inter hIimgsOpen
  have hyIimgs : y ∈ Iimgs := by
    refine Set.mem_iInter.mpr ?_
    intro x
    exact ⟨x.1, hxU x, by simp [x.2]⟩
  have hyV : y ∈ V := ⟨hyV0, hyIimgs⟩
  refine ⟨V, hVopen, hyV, ?_⟩
  intro y' hy'
  have hyV0' : y' ∈ V0 := hy'.1
  have hyI' : y' ∈ Iimgs := hy'.2
  exact natCard_fiber_eq_of_mem_open_of_preimage_subset_iUnion_disjoint_inj_and_mem_iInter_image
    (f := f) (y := y) (V := V0) (U := U) hpre hUinj hUdisj hfinite hyV0' hyI'

lemma natCard_fiber_isLocallyConstant_of_isProperMap_isLocalHomeomorph
    {f : X → Y} (hproper : IsProperMap f) (hlocal : IsLocalHomeomorph f) :
    IsLocallyConstant (fun y : Y => Nat.card ({x : X // f x = y})) := by
  refine (IsLocallyConstant.iff_exists_open _).2 ?_
  intro y
  have hfinite : ({x : X | f x = y} : Set X).Finite :=
    finite_fiber_of_isProperMap_isLocallyInjective
      (f := f) hproper hlocal.isLocallyInjective y
  rcases exists_open_natCard_fiber_eq_of_closedMap_localHomeomorph_of_finite_fiber
      (f := f) hproper.isClosedMap hlocal (y := y) hfinite with
    ⟨V, hVopen, hyV, hcard⟩
  refine ⟨V, hVopen, hyV, ?_⟩
  intro y' hy'
  exact hcard y' hy'

lemma natCard_fiber_eq_of_isProperMap_isLocalHomeomorph [PreconnectedSpace Y]
    {f : X → Y} (hproper : IsProperMap f) (hlocal : IsLocalHomeomorph f) :
    ∀ y y', Nat.card ({x : X // f x = y}) = Nat.card ({x : X // f x = y'}) := by
  have hloc :
      IsLocallyConstant (fun y : Y => Nat.card ({x : X // f x = y})) :=
    natCard_fiber_isLocallyConstant_of_isProperMap_isLocalHomeomorph
      (f := f) hproper hlocal
  exact (IsLocallyConstant.iff_is_const (f := fun y : Y =>
    Nat.card ({x : X // f x = y}))).1 hloc

omit [T2Space X] in
lemma surjective_of_isProperMap_isLocalHomeomorph [PreconnectedSpace Y] [Nonempty X]
    {f : X → Y} (hproper : IsProperMap f) (hlocal : IsLocalHomeomorph f) :
    Function.Surjective f := by
  have hclopen : IsClopen (Set.range f) := by
    exact ⟨hproper.isClosedMap.isClosed_range, hlocal.isOpenMap.isOpen_range⟩
  have hrange : Set.range f = Set.univ := by
    rcases isClopen_iff.mp hclopen with hempty | huniv
    · exact (Set.range_nonempty (f := f)).ne_empty hempty |> False.elim
    · exact huniv
  intro y
  have hy : y ∈ Set.range f := by simp [hrange]
  exact hy

omit [T2Space X] in
lemma natCard_fiber_pos_of_isProperMap_isLocalHomeomorph [PreconnectedSpace Y] [Nonempty X]
    {f : X → Y} (hproper : IsProperMap f) (hlocal : IsLocalHomeomorph f) (y : Y) :
    0 < Nat.card ({x : X // f x = y}) := by
  have hfinite : ({x : X | f x = y} : Set X).Finite :=
    finite_fiber_of_isProperMap_isLocallyInjective
      (f := f) hproper hlocal.isLocallyInjective y
  have hsurj : Function.Surjective f :=
    surjective_of_isProperMap_isLocalHomeomorph (f := f) hproper hlocal
  letI : Finite ({x : X // f x = y}) := hfinite.to_subtype
  letI : Fintype ({x : X // f x = y}) := Fintype.ofFinite ({x : X // f x = y})
  rcases hsurj y with ⟨x, hx⟩
  have hpos : 0 < Fintype.card ({x : X // f x = y}) := by
    exact Fintype.card_pos_iff.mpr ⟨⟨x, hx⟩⟩
  simpa [Nat.card_eq_fintype_card] using hpos

end ProperLocalHomeomorphFibers

/-- Large circles in the outside-open domain for `c = 2`. -/
noncomputable def outsideOpenCircleLoopTwo (R : ℝ) (hR : 4 < R) :
    C(unitInterval, {z : ℂ // ‖z‖ > ‖(2 : ℂ)‖ + 2}) where
  toFun t :=
    ⟨circleMap 0 R (2 * Real.pi * (t : ℝ)), by
      have hRpos : 0 < R := by linarith
      have hnorm :
          ‖circleMap 0 R (2 * Real.pi * (t : ℝ))‖ = R := by
        simpa [abs_of_pos hRpos] using norm_circleMap_zero R (2 * Real.pi * (t : ℝ))
      have hfour : ‖(2 : ℂ)‖ + 2 = 4 := by norm_num
      rw [hfour, hnorm]
      exact hR⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_circleMap 0 R).comp (by continuity)

/-- The corresponding large circles viewed in the exterior target. -/
noncomputable def exteriorCircleLoopTwo (R : ℝ) (hR : 4 < R) :
    C(unitInterval, {w : ℂ // 1 < ‖w‖}) where
  toFun t :=
    ⟨circleMap 0 R (2 * Real.pi * (t : ℝ)), by
      have hRpos : 0 < R := by linarith
      have hnorm :
          ‖circleMap 0 R (2 * Real.pi * (t : ℝ))‖ = R := by
        simpa [abs_of_pos hRpos] using norm_circleMap_zero R (2 * Real.pi * (t : ℝ))
      rw [hnorm]
      linarith⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_circleMap 0 R).comp (by continuity)

/-- The normalization at infinity already gives the large-circle estimate from the
degree-one proof sketch: for some sufficiently large radius, the straight-line homotopy from the
standard circle to its Böttcher-image stays entirely in the exterior. This is the formalized
asymptotic half of the winding-number argument. -/
theorem exists_large_radius_straight_line_homotopy_in_exterior_two :
    ∃ R : ℝ, 4 < R ∧
      ∀ s t : unitInterval,
        1 <
          ‖circleMap 0 R (2 * π * (t : ℝ)) +
            ((s : ℝ) : ℂ) *
              (MLC.Quadratic.bottcher_map (2 : ℂ)
                  (circleMap 0 R (2 * π * (t : ℝ))) -
                circleMap 0 R (2 * π * (t : ℝ)))‖ := by
  have hnorm : MLC.bottcher_normalized_at_infty (2 : ℂ) :=
    MLC.bottcher_normalized_at_infty_of_green (2 : ℂ)
  rcases MLC.bottcher_map_minus_id_bound_of_normalized (2 : ℂ) hnorm (1 / 2) (by norm_num) with
    ⟨R₀, hR₀⟩
  let R : ℝ := max R₀ 5
  have hRgt4 : 4 < R := by
    have hRge5 : (5 : ℝ) ≤ R := le_max_right _ _
    linarith
  have hRnonneg : 0 ≤ R := by linarith
  refine ⟨R, hRgt4, ?_⟩
  intro s t
  let z : ℂ := circleMap 0 R (2 * π * (t : ℝ))
  have hznorm : ‖z‖ = R := by
    dsimp [z]
    simpa [abs_of_nonneg hRnonneg] using norm_circleMap_zero R (2 * π * (t : ℝ))
  have hR₀le : R₀ ≤ ‖z‖ := by
    have : R₀ ≤ R := le_max_left _ _
    simpa [hznorm] using this
  have hbound : ‖MLC.Quadratic.bottcher_map (2 : ℂ) z - z‖ ≤ (1 / 2) * ‖z‖ := hR₀ z hR₀le
  have hs_nonneg : 0 ≤ (s : ℝ) := s.2.1
  have hs_le_one : (s : ℝ) ≤ 1 := s.2.2
  have hscaled :
      ‖(((s : ℝ) : ℂ) * (MLC.Quadratic.bottcher_map (2 : ℂ) z - z))‖ ≤ (1 / 2) * ‖z‖ := by
    calc
      ‖(((s : ℝ) : ℂ) * (MLC.Quadratic.bottcher_map (2 : ℂ) z - z))‖ =
          ‖((s : ℝ) : ℂ)‖ * ‖MLC.Quadratic.bottcher_map (2 : ℂ) z - z‖ := by
            simpa using norm_mul (((s : ℝ) : ℂ)) (MLC.Quadratic.bottcher_map (2 : ℂ) z - z)
      _ = (s : ℝ) * ‖MLC.Quadratic.bottcher_map (2 : ℂ) z - z‖ := by
            simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs_nonneg]
      _ ≤ (s : ℝ) * ((1 / 2) * ‖z‖) := by
            gcongr
      _ ≤ (1 / 2) * ‖z‖ := by
            nlinarith [norm_nonneg (MLC.Quadratic.bottcher_map (2 : ℂ) z - z)]
  have hlower :
      ‖z‖ - ‖(((s : ℝ) : ℂ) * (MLC.Quadratic.bottcher_map (2 : ℂ) z - z))‖ ≤
        ‖z + (((s : ℝ) : ℂ) * (MLC.Quadratic.bottcher_map (2 : ℂ) z - z))‖ := by
    simpa using norm_sub_norm_le z (-(((s : ℝ) : ℂ) *
      (MLC.Quadratic.bottcher_map (2 : ℂ) z - z)))
  have hhalf :
      ‖z‖ / 2 ≤ ‖z + (((s : ℝ) : ℂ) * (MLC.Quadratic.bottcher_map (2 : ℂ) z - z))‖ := by
    nlinarith
  have hgt1 : 1 < ‖z + (((s : ℝ) : ℂ) * (MLC.Quadratic.bottcher_map (2 : ℂ) z - z))‖ := by
    have : 1 < ‖z‖ / 2 := by
      rw [hznorm]
      nlinarith
    exact lt_of_lt_of_le this hhalf
  simpa [z] using hgt1

/-- The large-circle estimate promoted to an actual free homotopy of loops in the exterior. This
packages the geometric part of the winding argument in a form usable by later covering-space
reasoning. -/
theorem exists_large_radius_circle_homotopy_two
    (hcont : Continuous (MLC.bottcher_map_outside_open_to_exterior (2 : ℂ))) :
    ∃ R : ℝ, ∃ hR : 4 < R,
      Nonempty
        (ContinuousMap.Homotopy
          (exteriorCircleLoopTwo R hR)
          ((ContinuousMap.mk _ hcont).comp (outsideOpenCircleLoopTwo R hR))) := by
  rcases exists_large_radius_straight_line_homotopy_in_exterior_two with ⟨R, hR, hH⟩
  refine ⟨R, hR, ⟨?_⟩⟩
  let σ := exteriorCircleLoopTwo R hR
  let σdom := outsideOpenCircleLoopTwo R hR
  let τ : C(unitInterval, {w : ℂ // 1 < ‖w‖}) := (ContinuousMap.mk _ hcont).comp σdom
  refine
    { toFun := fun st =>
        ⟨(σ st.2 : ℂ) + (((st.1 : unitInterval) : ℝ) : ℂ) * ((τ st.2 : ℂ) - (σ st.2 : ℂ)), by
          simpa [σ, σdom, τ, outsideOpenCircleLoopTwo, exteriorCircleLoopTwo,
            MLC.bottcher_map_outside_open_to_exterior]
            using hH st.1 st.2⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        have hσ : Continuous fun st : unitInterval × unitInterval => (σ st.2 : ℂ) := by
          exact continuous_subtype_val.comp (σ.continuous.comp continuous_snd)
        have hτ : Continuous fun st : unitInterval × unitInterval => (τ st.2 : ℂ) := by
          exact continuous_subtype_val.comp (τ.continuous.comp continuous_snd)
        have hs : Continuous fun st : unitInterval × unitInterval =>
            ((((st.1 : unitInterval) : ℝ) : ℂ)) := by
          exact Complex.continuous_ofReal.comp
            (continuous_subtype_val.comp continuous_fst)
        simpa using hσ.add (hs.mul (hτ.sub hσ))
      map_zero_left := by
        intro t
        apply Subtype.ext
        simp [σ]
      map_one_left := by
        intro t
        apply Subtype.ext
        simp [σ, τ, σdom, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] }

/-- If every fiber of a map has cardinality one, then the map is injective.

This is the final purely set-theoretic step in the degree-one covering
argument: once the topological/winding calculation has shown that every sheet
fiber has one point, no topology remains. -/
lemma injective_of_forall_natCard_fiber_eq_one
    {X Y : Type*} (f : X → Y)
    (hcard : ∀ y : Y, Nat.card ({x : X // f x = y}) = 1) :
    Function.Injective f := by
  intro x x' hxx'
  have hsub :
      Subsingleton ({z : X // f z = f x}) :=
    (Nat.card_eq_one_iff_unique.mp (hcard (f x))).1
  have hx_eq :
      (⟨x, rfl⟩ : {z : X // f z = f x}) =
        ⟨x', hxx'.symm⟩ :=
    Subsingleton.elim _ _
  exact congrArg Subtype.val hx_eq

/-- Fiber cardinality of the restricted outside-open Böttcher map at `c = 2`. -/
noncomputable def RestrictedFiberCardTwo (y : {w : ℂ // 1 < ‖w‖}) : ℕ :=
  Nat.card
    ({x : {z : ℂ // ‖z‖ > ‖(2 : ℂ)‖ + 2} //
        MLC.bottcher_map_outside_open_to_exterior (2 : ℂ) x = y})

/-- The restricted outside-open Böttcher map at `c = 2` has one-point fibers.

This is the formal target of the covering-degree/winding-number calculation:
proper local-homeomorphy supplies a finite constant covering degree, and the
asymptotic winding computation identifies that degree as `1`. -/
def RestrictedDegreeOneFibersTwo : Prop :=
  ∀ y : {w : ℂ // 1 < ‖w‖}, RestrictedFiberCardTwo y = 1

/-- The finite-sheeted covering degree is independent of the base point. This
is the formal counterpart of the covering-space part of the proof. -/
def RestrictedCoveringDegreeConstantTwo : Prop :=
  ∀ y y' : {w : ℂ // 1 < ‖w‖},
    RestrictedFiberCardTwo y = RestrictedFiberCardTwo y'

/-- The asymptotic winding calculation identifies the restricted covering
degree as one. Since the degree is constant, it is enough to record one fiber
with cardinality one. -/
def RestrictedAsymptoticWindingDegreeOneTwo : Prop :=
  ∃ y : {w : ℂ // 1 < ‖w‖}, RestrictedFiberCardTwo y = 1

/-- Exact remaining algebraic-topology bridge from the proof sketch:
once the restricted outside-open map at `c = 2` is known to be proper and a
local homeomorphism, the already-formalized large-circle homotopy should force
the covering degree to be `1`. -/
def RestrictedAsymptoticWindingBridgeTwo : Prop :=
  ∀ (h_proper : IsProperMap (MLC.bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (h_local : IsLocalHomeomorph (MLC.bottcher_map_outside_open_to_exterior (2 : ℂ))),
      RestrictedAsymptoticWindingDegreeOneTwo

/-- Exact remaining generator calculation from the proof sketch: Lean already
formalizes the positive constant covering degree for the restricted map once
properness and local-homeomorphy are available. The residual algebraic-topology
content is that a free homotopy from a large image loop to the standard
positive exterior circle forces that degree to equal `1`. -/
def RestrictedCoveringDegreeOneFromPositiveConstantAndCircleHomotopyTwo : Prop :=
  ∀ (h_cont : Continuous (MLC.bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (d : ℕ), 0 < d →
      (∀ y : {w : ℂ // 1 < ‖w‖}, RestrictedFiberCardTwo y = d) →
        (∃ R : ℝ, ∃ hR : 4 < R,
          Nonempty
            (ContinuousMap.Homotopy
              (exteriorCircleLoopTwo R hR)
              ((ContinuousMap.mk _ h_cont).comp
                (outsideOpenCircleLoopTwo R hR)))) →
          d = 1

/-- Exact remaining annulus-covering theorem isolated from the proof sketch:
if the restricted map is proper and a local homeomorphism, then any
already-formalized free homotopy between a large standard exterior circle and
its image loop should force the covering degree to be `1`. -/
def RestrictedAnnulusCoveringDegreeOneStepTwo : Prop :=
  ∀ (h_proper : IsProperMap (MLC.bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (h_local : IsLocalHomeomorph (MLC.bottcher_map_outside_open_to_exterior (2 : ℂ))),
      (∃ R : ℝ, ∃ hR : 4 < R,
        Nonempty
          (ContinuousMap.Homotopy
            (exteriorCircleLoopTwo R hR)
            ((ContinuousMap.mk _ h_local.continuous).comp
              (outsideOpenCircleLoopTwo R hR)))) →
        RestrictedAsymptoticWindingDegreeOneTwo

/-- The only Bottcher-specific analytic input needed by the remaining topology
step is now the already formalized large-circle free homotopy. -/
theorem restrictedAsymptoticWindingBridgeTwo_of_annulusCoveringDegreeOneStep
    (htopo : RestrictedAnnulusCoveringDegreeOneStepTwo) :
    RestrictedAsymptoticWindingBridgeTwo := by
  intro h_proper h_local
  rcases exists_large_radius_circle_homotopy_two h_local.continuous with
    ⟨R, hR, hhom⟩
  exact htopo h_proper h_local ⟨R, hR, hhom⟩

/-- The abstract annulus-covering degree-one step already implies the concrete
singleton-fiber conclusion for the restricted Böttcher map once the proper/local
witness is supplied. -/
theorem restrictedAsymptoticWindingDegreeOneTwo_of_annulusCoveringDegreeOneStep
    (htopo : RestrictedAnnulusCoveringDegreeOneStepTwo)
    (h_proper : IsProperMap (MLC.bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (h_local : IsLocalHomeomorph (MLC.bottcher_map_outside_open_to_exterior (2 : ℂ))) :
    RestrictedAsymptoticWindingDegreeOneTwo :=
  restrictedAsymptoticWindingBridgeTwo_of_annulusCoveringDegreeOneStep htopo
    h_proper h_local

/-- Proper local-homeomorphy of the restricted outside-open map makes the
restricted fiber cardinality independent of the exterior base point. -/
theorem restricted_covering_degree_constant_two_of_isProperMap_isLocalHomeomorph
    (h_proper : IsProperMap (MLC.bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (h_local : IsLocalHomeomorph (MLC.bottcher_map_outside_open_to_exterior (2 : ℂ))) :
    RestrictedCoveringDegreeConstantTwo := by
  letI : ConnectedSpace {w : ℂ // 1 < ‖w‖} :=
    (isConnected_iff_connectedSpace).1 MLC.isConnected_exterior
  intro y y'
  simpa [RestrictedFiberCardTwo] using
    (natCard_fiber_eq_of_isProperMap_isLocalHomeomorph
      (f := MLC.bottcher_map_outside_open_to_exterior (2 : ℂ)) h_proper h_local y y')

/-- Proper local-homeomorphy of the restricted outside-open map gives a positive
constant covering degree on the exterior target. This formalizes the finite,
surjective covering part of the degree-one proof before the winding calculation
identifies the degree as `1`. -/
theorem restricted_covering_degree_positive_two_of_isProperMap_isLocalHomeomorph
    (h_proper : IsProperMap (MLC.bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (h_local : IsLocalHomeomorph (MLC.bottcher_map_outside_open_to_exterior (2 : ℂ))) :
    ∃ d : ℕ, 0 < d ∧ ∀ y : {w : ℂ // 1 < ‖w‖}, RestrictedFiberCardTwo y = d := by
  letI : ConnectedSpace {w : ℂ // 1 < ‖w‖} :=
    (isConnected_iff_connectedSpace).1 MLC.isConnected_exterior
  letI : Nonempty {z : ℂ // ‖z‖ > ‖(2 : ℂ)‖ + 2} := by
    refine ⟨⟨(5 : ℂ), ?_⟩⟩
    norm_num
  let y0 : {w : ℂ // 1 < ‖w‖} := ⟨(2 : ℂ), by norm_num⟩
  refine ⟨RestrictedFiberCardTwo y0, ?_, ?_⟩
  · simpa [RestrictedFiberCardTwo, y0] using
      (natCard_fiber_pos_of_isProperMap_isLocalHomeomorph
        (f := MLC.bottcher_map_outside_open_to_exterior (2 : ℂ)) h_proper h_local y0)
  · intro y
    simpa [y0] using
      (restricted_covering_degree_constant_two_of_isProperMap_isLocalHomeomorph
        h_proper h_local y y0)

/-- Bottcher-facing singleton-fiber corollary of the exact remaining
generator-calculation kernel from the proof sketch. -/
theorem restrictedAsymptoticWindingDegreeOneTwo_of_coveringDegreeOneFromPositiveConstantAndCircleHomotopy
    (hkernel : RestrictedCoveringDegreeOneFromPositiveConstantAndCircleHomotopyTwo)
    (h_proper : IsProperMap (MLC.bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (h_local : IsLocalHomeomorph (MLC.bottcher_map_outside_open_to_exterior (2 : ℂ))) :
    (∃ R : ℝ, ∃ hR : 4 < R,
      Nonempty
        (ContinuousMap.Homotopy
          (exteriorCircleLoopTwo R hR)
          ((ContinuousMap.mk _ h_local.continuous).comp
            (outsideOpenCircleLoopTwo R hR)))) →
      RestrictedAsymptoticWindingDegreeOneTwo := by
  intro hhom
  rcases restricted_covering_degree_positive_two_of_isProperMap_isLocalHomeomorph h_proper h_local with
    ⟨d, hdpos, hdeg⟩
  have hd : d = 1 := hkernel h_local.continuous d hdpos hdeg hhom
  let y0 : {w : ℂ // 1 < ‖w‖} := ⟨(2 : ℂ), by norm_num⟩
  refine ⟨y0, ?_⟩
  simpa [y0, hd] using hdeg y0

/-- The exact remaining annulus-covering theorem follows from the more precise
generator-calculation kernel, since the finite positive constant covering degree
has already been formalized separately. -/
theorem restrictedAnnulusCoveringDegreeOneStepTwo_of_coveringDegreeOneFromPositiveConstantAndCircleHomotopy
    (hkernel : RestrictedCoveringDegreeOneFromPositiveConstantAndCircleHomotopyTwo) :
    RestrictedAnnulusCoveringDegreeOneStepTwo := by
  intro h_proper h_local
  exact
    restrictedAsymptoticWindingDegreeOneTwo_of_coveringDegreeOneFromPositiveConstantAndCircleHomotopy
      hkernel h_proper h_local

/-- Combining constant covering degree with the winding-number degree-one
calculation gives one-point fibers over every exterior point. -/
theorem restricted_degree_one_fibers_two_of_constant_of_winding
    (hconst : RestrictedCoveringDegreeConstantTwo)
    (hwinding : RestrictedAsymptoticWindingDegreeOneTwo) :
    RestrictedDegreeOneFibersTwo := by
  intro y
  rcases hwinding with ⟨y0, hy0⟩
  calc
    RestrictedFiberCardTwo y = RestrictedFiberCardTwo y0 := hconst y y0
    _ = 1 := hy0

/-- The exact proof-sketch bridge implies degree-one fibers once the proper/local
restricted-map witness is available. -/
theorem restricted_degree_one_fibers_two_of_winding_bridge
    (hbridge : RestrictedAsymptoticWindingBridgeTwo)
    (h_proper : IsProperMap (MLC.bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (h_local : IsLocalHomeomorph (MLC.bottcher_map_outside_open_to_exterior (2 : ℂ))) :
    RestrictedDegreeOneFibersTwo := by
  exact
    restricted_degree_one_fibers_two_of_constant_of_winding
      (restricted_covering_degree_constant_two_of_isProperMap_isLocalHomeomorph h_proper h_local)
      (hbridge h_proper h_local)

/-- If the restricted outside-open map has degree-one fibers, then the original
Böttcher map is injective on the outside-open domain. -/
theorem injOn_outside_open_two_of_restricted_degree_one_fibers
    (hdegree : RestrictedDegreeOneFibersTwo) :
    Set.InjOn (MLC.Quadratic.bottcher_map (2 : ℂ))
      {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2} := by
  let f := MLC.bottcher_map_outside_open_to_exterior (2 : ℂ)
  have hf_inj : Function.Injective f :=
    injective_of_forall_natCard_fiber_eq_one f hdegree
  intro z hz z' hz' hzz'
  let x : {z : ℂ // ‖z‖ > ‖(2 : ℂ)‖ + 2} := ⟨z, hz⟩
  let x' : {z : ℂ // ‖z‖ > ‖(2 : ℂ)‖ + 2} := ⟨z', hz'⟩
  have hx_image : f x = f x' := by
    apply Subtype.ext
    simpa [f, x, x', MLC.bottcher_map_outside_open_to_exterior] using hzz'
  exact congrArg Subtype.val (hf_inj hx_image)

/-- Outside-open injectivity from the two formal pieces of the degree-one proof:
constant covering degree and asymptotic winding degree one. -/
theorem injOn_outside_open_two_of_restricted_covering_degree_constant_of_winding
    (hconst : RestrictedCoveringDegreeConstantTwo)
    (hwinding : RestrictedAsymptoticWindingDegreeOneTwo) :
    Set.InjOn (MLC.Quadratic.bottcher_map (2 : ℂ))
      {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2} := by
  exact injOn_outside_open_two_of_restricted_degree_one_fibers
    (restricted_degree_one_fibers_two_of_constant_of_winding hconst hwinding)

/-- Outside-open injectivity from the exact remaining proof-sketch bridge. -/
theorem injOn_outside_open_two_of_winding_bridge
    (hbridge : RestrictedAsymptoticWindingBridgeTwo)
    (h_proper : IsProperMap (MLC.bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (h_local : IsLocalHomeomorph (MLC.bottcher_map_outside_open_to_exterior (2 : ℂ))) :
    Set.InjOn (MLC.Quadratic.bottcher_map (2 : ℂ))
      {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2} := by
  exact
    injOn_outside_open_two_of_restricted_degree_one_fibers
      (restricted_degree_one_fibers_two_of_winding_bridge hbridge h_proper h_local)

/-- Proper local-homeomorphy gives exterior surjectivity, and the degree-one
fiber conclusion gives outside-open injectivity. Together they construct the
external-ray map package at `c = 2`. -/
theorem external_ray_map_exists_two_of_proper_localHomeomorph_restrict_of_restricted_degree_one_fibers
    (h_proper : IsProperMap (MLC.bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (h_local : IsLocalHomeomorph (MLC.bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (hdegree : RestrictedDegreeOneFibersTwo) :
    MLC.Quadratic.ExternalRayMapData (2 : ℂ) := by
  exact
    MLC.external_ray_map_data_of_injOn_outside_open_of_surj_exterior (2 : ℂ)
      (injOn_outside_open_two_of_restricted_degree_one_fibers hdegree)
      (MLC.bottcherSurjOnExteriorFromOutsideOpen_two_of_isClosedRange_restrict_of_isLocalHomeomorph_restrict
        (MLC.isClosed_range_bottcher_map_outside_open_to_exterior_of_isProperMap (2 : ℂ)
          h_proper)
        h_local)

/-- External-ray map data from proper local-homeomorphy plus the two formal
pieces of the degree-one proof: constant covering degree and asymptotic winding
degree one. -/
theorem external_ray_map_exists_two_of_proper_localHomeomorph_restrict_of_covering_degree_constant_of_winding
    (h_proper : IsProperMap (MLC.bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (h_local : IsLocalHomeomorph (MLC.bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (hconst : RestrictedCoveringDegreeConstantTwo)
    (hwinding : RestrictedAsymptoticWindingDegreeOneTwo) :
    MLC.Quadratic.ExternalRayMapData (2 : ℂ) := by
  exact
    external_ray_map_exists_two_of_proper_localHomeomorph_restrict_of_restricted_degree_one_fibers
      h_proper h_local
      (restricted_degree_one_fibers_two_of_constant_of_winding hconst hwinding)

/-- External-ray map data from proper local-homeomorphy plus the asymptotic
winding degree-one calculation; the restricted covering-degree constancy is
supplied by proper local-homeomorphy. -/
theorem external_ray_map_exists_two_of_proper_localHomeomorph_restrict_of_winding
    (h_proper : IsProperMap (MLC.bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (h_local : IsLocalHomeomorph (MLC.bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (hwinding : RestrictedAsymptoticWindingDegreeOneTwo) :
    MLC.Quadratic.ExternalRayMapData (2 : ℂ) := by
  exact
    external_ray_map_exists_two_of_proper_localHomeomorph_restrict_of_covering_degree_constant_of_winding
      h_proper h_local
      (restricted_covering_degree_constant_two_of_isProperMap_isLocalHomeomorph
        h_proper h_local)
      hwinding

/-- External-ray map data from the exact remaining proof-sketch bridge:
proper/local-homeomorphy of the restricted map plus the unresolved
algebraic-topology theorem. -/
theorem external_ray_map_exists_two_of_proper_localHomeomorph_restrict_of_winding_bridge
    (hbridge : RestrictedAsymptoticWindingBridgeTwo)
    (h_proper : IsProperMap (MLC.bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (h_local : IsLocalHomeomorph (MLC.bottcher_map_outside_open_to_exterior (2 : ℂ))) :
    MLC.Quadratic.ExternalRayMapData (2 : ℂ) := by
  exact
    external_ray_map_exists_two_of_proper_localHomeomorph_restrict_of_winding
      h_proper h_local (hbridge h_proper h_local)

/-- External-ray map data from the exact remaining abstract annulus theorem. -/
theorem external_ray_map_exists_two_of_proper_localHomeomorph_restrict_of_annulusCoveringDegreeOneStep
    (htopo : RestrictedAnnulusCoveringDegreeOneStepTwo)
    (h_proper : IsProperMap (MLC.bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (h_local : IsLocalHomeomorph (MLC.bottcher_map_outside_open_to_exterior (2 : ℂ))) :
    MLC.Quadratic.ExternalRayMapData (2 : ℂ) := by
  exact
    external_ray_map_exists_two_of_proper_localHomeomorph_restrict_of_winding
      h_proper h_local
      (restrictedAsymptoticWindingDegreeOneTwo_of_annulusCoveringDegreeOneStep
        htopo h_proper h_local)

/-- Proper local-homeomorphy of the restricted outside-open map already gives
exterior surjectivity via the clopen-image argument. -/
theorem bottcherSurjOnExteriorFromOutsideOpen_two_of_isProperMap_restrict_of_isLocalHomeomorph_restrict
    (h_proper : IsProperMap (MLC.bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (h_local : IsLocalHomeomorph (MLC.bottcher_map_outside_open_to_exterior (2 : ℂ))) :
    MLC.BottcherSurjOnExteriorFromOutsideOpen (2 : ℂ) := by
  exact
    MLC.bottcherSurjOnExteriorFromOutsideOpen_two_of_isClosedRange_restrict_of_isLocalHomeomorph_restrict
      (MLC.isClosed_range_bottcher_map_outside_open_to_exterior_of_isProperMap (2 : ℂ) h_proper)
      h_local

/-- Direct proper/local restricted-map route at `c = 2`: once outside-open
injectivity is available, proper local-homeomorphy supplies the missing
exterior surjectivity and therefore closes the full external-ray package.

This integrates the surjectivity half of the degree-one proof non-circularly.
The remaining missing ingredient for the full route is now exactly the
outside-open injectivity theorem. -/
theorem external_ray_map_exists_two_of_proper_localHomeomorph_restrict_of_injOn
    (h_proper : IsProperMap (MLC.bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (h_local : IsLocalHomeomorph (MLC.bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (h_inj :
      Set.InjOn (MLC.Quadratic.bottcher_map (2 : ℂ))
        {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2}) :
    MLC.Quadratic.ExternalRayMapData (2 : ℂ) := by
  exact
    MLC.external_ray_map_data_of_injOn_outside_open_of_surj_exterior (2 : ℂ) h_inj
      (bottcherSurjOnExteriorFromOutsideOpen_two_of_isProperMap_restrict_of_isLocalHomeomorph_restrict
        h_proper h_local)

end Mlc.Bottcher.DegreeOne
