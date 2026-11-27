import Mlc.Research.ReturnBudget
import Mathlib.Topology.Connected.LocallyConnected

/-!
# From a separation budget to connected parameter neighborhoods

The geometric estimate is a named hypothesis. No conformal-modulus theorem
or classical parapuzzle realization is asserted by these definitions.
-/

namespace MLC.Research

open Set Filter Topology Metric

noncomputable section

def LocallyConnectedAtSet (S : Set ℂ) (c : S) : Prop :=
  ∀ U ∈ 𝓝 c, ∃ V ∈ 𝓝 c, IsPreconnected V ∧ V ⊆ U

theorem locallyConnectedSpace_iff_pointwise (S : Set ℂ) :
    LocallyConnectedSpace S ↔ ∀ c : S, LocallyConnectedAtSet S c := by
  exact locallyConnectedSpace_iff_connected_subsets

theorem hasBasis_nhds_of_iInter_singleton
    {α : Type*} [TopologicalSpace α] [T2Space α]
    {K : ℕ → Set α} (h_compact : ∀ n, IsCompact (K n))
    (h_nested : ∀ n, K (n + 1) ⊆ K n)
    {x : α} (h_inter : (⋂ n, K n) = {x})
    (h_nhd : ∀ n, K n ∈ 𝓝 x) :
    (𝓝 x).HasBasis (fun _ => True) K := by
  refine ⟨fun U => ⟨fun hU => ?_, fun ⟨n, _, hn_sub⟩ => ?_⟩⟩
  · obtain ⟨V, hV_sub, hV_open, hxV⟩ := mem_nhds_iff.mp hU
    by_contra! h_neg
    let F := fun n => K n \ V
    have hF_nonempty : ∀ n, (F n).Nonempty := by
      intro n
      rw [Set.diff_nonempty]
      intro h_sub
      exact (h_neg n trivial) (h_sub.trans hV_sub)
    have hF_nested : ∀ n, F (n + 1) ⊆ F n :=
      fun n => diff_subset_diff (h_nested n) (subset_refl V)
    have hF_compact : ∀ n, IsCompact (F n) :=
      fun n => (h_compact n).diff hV_open
    have hF_closed : ∀ n, IsClosed (F n) :=
      fun n => (hF_compact n).isClosed
    obtain ⟨y, hy⟩ :=
      IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
        F hF_nested hF_nonempty (hF_compact 0) hF_closed
    have h_inter_F : (⋂ n, F n) = (⋂ n, K n) \ V := by
      ext z
      simp [F, forall_and]
    rw [h_inter_F, h_inter] at hy
    have h_empty : ({x} : Set α) \ V = ∅ :=
      Set.diff_eq_empty.mpr (singleton_subset_iff.mpr hxV)
    rw [h_empty] at hy
    exact (Set.mem_empty_iff_false y).mp hy
  · exact mem_of_superset (h_nhd n) hn_sub

/-- Actual parameter subsets; shrinking is not a field. -/
structure ConnectedNest (S : Set ℂ) (c : ℂ) where
  piece : ℕ → Set ℂ
  open_piece : ∀ n, IsOpen (piece n)
  contains : ∀ n, c ∈ piece n
  connected : ∀ n, IsConnected (piece n ∩ S)
  compact_closure : ∀ n, IsCompact (closure (piece n))
  nested : ∀ n, piece (n + 1) ⊆ piece n

namespace ConnectedNest

variable {S : Set ℂ} {c : ℂ} (D : ConnectedNest S c)

def kernel : Set ℂ := ⋂ n, closure (D.piece n)
def relativePiece (n : ℕ) : Set S := {z : S | z.1 ∈ D.piece n}

theorem mem_closure (n : ℕ) : c ∈ closure (D.piece n) :=
  subset_closure (D.contains n)

theorem mem_kernel : c ∈ D.kernel := mem_iInter.mpr D.mem_closure

theorem closure_nested (n : ℕ) :
    closure (D.piece (n + 1)) ⊆ closure (D.piece n) :=
  closure_mono (D.nested n)

theorem kernel_subset_closure (n : ℕ) : D.kernel ⊆ closure (D.piece n) :=
  iInter_subset _ n

theorem closure_mem_nhds (n : ℕ) : closure (D.piece n) ∈ 𝓝 c :=
  mem_of_superset ((D.open_piece n).mem_nhds (D.contains n)) subset_closure

theorem relativePiece_open (n : ℕ) : IsOpen (D.relativePiece n) :=
  (D.open_piece n).preimage continuous_subtype_val

theorem relativePiece_contains (hc : c ∈ S) (n : ℕ) :
    (⟨c, hc⟩ : S) ∈ D.relativePiece n := D.contains n

theorem relativePiece_mem_nhds (hc : c ∈ S) (n : ℕ) :
    D.relativePiece n ∈ 𝓝 (⟨c, hc⟩ : S) :=
  (D.relativePiece_open n).mem_nhds (D.relativePiece_contains hc n)

theorem relativePiece_image (n : ℕ) :
    Subtype.val '' D.relativePiece n = D.piece n ∩ S := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨hx, x.property⟩
  · rintro ⟨hz, hzS⟩
    exact ⟨⟨z, hzS⟩, hz, rfl⟩

theorem relativePiece_preconnected (n : ℕ) : IsPreconnected (D.relativePiece n) := by
  apply (Topology.IsInducing.isPreconnected_image
    (s := D.relativePiece n) (IsEmbedding.subtypeVal.isInducing)).mp
  rw [D.relativePiece_image]
  exact (D.connected n).isPreconnected

/-- The capacity estimate needed from genuine parameter annuli. If a piece
still reaches distance epsilon, its accumulated separation cost is bounded. -/
def SeparationEstimate (cost : ℕ → ℝ) : Prop :=
  ∀ ε > (0 : ℝ), ∃ C : ℝ, ∀ n z, z ∈ closure (D.piece n) →
    ε ≤ dist z c → (∑ j ∈ Finset.range n, cost j) ≤ C

theorem dist_lt_of_large_budget
    {cost : ℕ → ℝ} {ε C : ℝ} {n : ℕ}
    (hbound : ∀ z ∈ closure (D.piece n), ε ≤ dist z c →
      (∑ j ∈ Finset.range n, cost j) ≤ C)
    (hlarge : C < ∑ j ∈ Finset.range n, cost j)
    {z : ℂ} (hz : z ∈ closure (D.piece n)) : dist z c < ε := by
  by_contra h
  exact (not_le_of_gt hlarge) (hbound z hz (not_lt.mp h))

theorem exists_closure_subset_ball
    {cost : ℕ → ℝ} (hsep : D.SeparationEstimate cost)
    (hbudget : UnboundedBudget cost) {ε : ℝ} (hε : 0 < ε) :
    ∃ n, closure (D.piece n) ⊆ ball c ε := by
  obtain ⟨C, hC⟩ := hsep ε hε
  obtain ⟨n, hn⟩ := hbudget C
  exact ⟨n, fun z hz => D.dist_lt_of_large_budget (hC n) hn hz⟩

theorem kernel_dist_lt
    {cost : ℕ → ℝ} (hsep : D.SeparationEstimate cost)
    (hbudget : UnboundedBudget cost) {z : ℂ} (hz : z ∈ D.kernel)
    {ε : ℝ} (hε : 0 < ε) : dist z c < ε := by
  obtain ⟨n, hn⟩ := D.exists_closure_subset_ball hsep hbudget hε
  exact hn (D.kernel_subset_closure n hz)

theorem kernel_subset_singleton
    {cost : ℕ → ℝ} (hsep : D.SeparationEstimate cost)
    (hbudget : UnboundedBudget cost) : D.kernel ⊆ {c} := by
  intro z hz
  apply Set.mem_singleton_iff.mpr
  apply eq_of_dist_eq_zero
  apply le_antisymm _ dist_nonneg
  exact le_of_forall_gt_imp_ge_of_dense fun ε hε =>
    le_of_lt (D.kernel_dist_lt hsep hbudget hz hε)

theorem kernel_eq_singleton
    {cost : ℕ → ℝ} (hsep : D.SeparationEstimate cost)
    (hbudget : UnboundedBudget cost) : D.kernel = {c} :=
  subset_antisymm (D.kernel_subset_singleton hsep hbudget)
    (singleton_subset_iff.mpr D.mem_kernel)

theorem closure_basis_of_singleton (h : D.kernel = {c}) :
    (𝓝 c).HasBasis (fun _ : ℕ => True) (fun n => closure (D.piece n)) :=
  hasBasis_nhds_of_iInter_singleton
    D.compact_closure D.closure_nested h D.closure_mem_nhds

theorem piece_cofinal_of_singleton (h : D.kernel = {c}) :
    ∀ U ∈ 𝓝 c, ∃ n, D.piece n ⊆ U := by
  intro U hU
  obtain ⟨n, _, hn⟩ := (D.closure_basis_of_singleton h).mem_iff.mp hU
  exact ⟨n, subset_closure.trans hn⟩

theorem relativePiece_cofinal (hc : c ∈ S) (h : D.kernel = {c}) :
    ∀ U ∈ 𝓝 (⟨c, hc⟩ : S), ∃ n, D.relativePiece n ⊆ U := by
  intro U hU
  obtain ⟨V, hVU, hVopen, hcV⟩ := _root_.mem_nhds_iff.mp hU
  obtain ⟨W, hWopen, hW⟩ := isOpen_induced_iff.mp hVopen
  rw [← hW] at hcV hVU
  obtain ⟨n, hn⟩ := D.piece_cofinal_of_singleton h W (hWopen.mem_nhds hcV)
  exact ⟨n, fun z hz => hVU (hn hz)⟩

theorem locallyConnectedAt_of_singleton (hc : c ∈ S) (h : D.kernel = {c}) :
    LocallyConnectedAtSet S ⟨c, hc⟩ := by
  intro U hU
  obtain ⟨n, hn⟩ := D.relativePiece_cofinal hc h U hU
  exact ⟨D.relativePiece n, D.relativePiece_mem_nhds hc n,
    D.relativePiece_preconnected n, hn⟩

theorem locallyConnectedAt_of_budget (hc : c ∈ S)
    {cost : ℕ → ℝ} (hsep : D.SeparationEstimate cost)
    (hbudget : UnboundedBudget cost) : LocallyConnectedAtSet S ⟨c, hc⟩ :=
  D.locallyConnectedAt_of_singleton hc (D.kernel_eq_singleton hsep hbudget)

end ConnectedNest

/-- The numerical recurrence has been realized by actual connected parameter
pieces and a capacity estimate. Constructing this is M1's analytic task. -/
structure ParameterRealization (S : Set ℂ) (c : ℂ) (b : ReturnBudget) where
  nest : ConnectedNest S c
  separation : nest.SeparationEstimate b.cost

theorem ParameterRealization.locallyConnectedAt
    {S : Set ℂ} {c : ℂ} {b : ReturnBudget}
    (D : ParameterRealization S c b) (hc : c ∈ S) (h : b.LinearLossControl) :
    LocallyConnectedAtSet S ⟨c, hc⟩ :=
  D.nest.locallyConnectedAt_of_budget hc D.separation (b.unbounded_of_linearLossControl h)

end
end MLC.Research
