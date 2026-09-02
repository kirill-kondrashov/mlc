import Yoccoz.Quadratic.Complex.Basic
import Yoccoz.Quadratic.Complex.Escape
import Yoccoz.Quadratic.Complex.Green
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Compactness.Compact
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Filled Julia set connectivity

Proves `IsConnected (K c)` for `c ∈ MandelbrotSet`, replacing an earlier
axiom-backed placeholder.

## Proof outline

1. **Sublemma** (`isPreconnected_sq_preimage`): If `A ⊆ ℂ` is closed,
   preconnected, and `0 ∈ A`, then `{z | z ^ 2 ∈ A}` is preconnected.

2. **Intersection theorem** (`isPreconnected_iInter_of_sequence`): A decreasing
   intersection of nonempty compact preconnected sets is preconnected.

3. **Assembly**: `K(c) = ⋂_n {z | ‖f^n(z)‖ ≤ R}` is a decreasing intersection
   of compact preconnected sets.
-/

namespace MLC.Quadratic

open Complex Topology Set Filter Metric

noncomputable section

/-! ## Part 1: Connected preimage under squaring -/

private lemma neg_sq (z : ℂ) : (-z) ^ 2 = z ^ 2 := by ring

/-- Every complex number has a square root. -/
private lemma complex_exists_sq_root (a : ℂ) : ∃ z : ℂ, z ^ 2 = a :=
  IsAlgClosed.exists_pow_nat_eq a (by norm_num : 0 < 2)

/-- If `A ⊆ ℂ` is closed, preconnected, and `0 ∈ A`, then
`{z | z ^ 2 ∈ A}` is preconnected.

The proof uses the involution `z ↦ -z` to show that any disjoint closed
decomposition of `B = {z | z² ∈ A}` induces a disjoint closed decomposition
of `A`, contradicting its preconnectedness. -/
theorem isPreconnected_sq_preimage {A : Set ℂ}
    (hA : IsPreconnected A) (hAclosed : IsClosed A) (h0 : (0 : ℂ) ∈ A) :
    IsPreconnected {z : ℂ | z ^ 2 ∈ A} := by
  set B := {z : ℂ | z ^ 2 ∈ A} with hB_def
  have hBclosed : IsClosed B := hAclosed.preimage (continuous_pow 2)
  have h0B : (0 : ℂ) ∈ B := by simp [hB_def, h0]
  have h_neg_B : ∀ z ∈ B, -z ∈ B := fun z hz => by
    show (-z) ^ 2 ∈ A; rwa [neg_sq]
  -- The squaring map z ↦ z² is proper (preimage of compact is compact), hence a closed map.
  have sq_closed : IsClosedMap (fun z : ℂ => z ^ 2) := by
    apply IsProperMap.isClosedMap
    rw [isProperMap_iff_isCompact_preimage]
    refine ⟨continuous_pow 2, fun K hK => ?_⟩
    obtain ⟨r, hKsub⟩ := Metric.isBounded_iff_subset_closedBall (0 : ℂ) |>.mp hK.isBounded
    apply isCompact_of_isClosed_isBounded
    · exact hK.isClosed.preimage (continuous_pow 2)
    · refine Metric.isBounded_iff_subset_closedBall (0 : ℂ) |>.2 ⟨Real.sqrt r, ?_⟩
      intro z hz
      rw [Metric.mem_closedBall, dist_zero_right]
      have hzK : z ^ 2 ∈ K := hz
      have hzK' := hKsub hzK
      rw [Metric.mem_closedBall, dist_zero_right] at hzK'
      have hzK'' : ‖z‖ ^ 2 ≤ r := by simpa [norm_pow] using hzK'
      calc ‖z‖ = Real.sqrt (‖z‖ ^ 2) := (Real.sqrt_sq (norm_nonneg z)).symm
      _ ≤ Real.sqrt r := Real.sqrt_le_sqrt hzK''
  rw [isPreconnected_iff_subset_of_fully_disjoint_closed hBclosed]
  intro U V hUcl hVcl hBUV hdisj
  -- It suffices to show: if 0 ∈ W₁, then B ⊆ W₁ (then apply to (U,V) or (V,U)).
  suffices key : ∀ W₁ W₂ : Set ℂ, IsClosed W₁ → IsClosed W₂ → B ⊆ W₁ ∪ W₂ →
      Disjoint W₁ W₂ → (0 : ℂ) ∈ W₁ → B ⊆ W₁ by
    rcases hBUV h0B with h0U | h0V
    · exact Or.inl (key U V hUcl hVcl hBUV hdisj h0U)
    · exact Or.inr (key V U hVcl hUcl (fun x hx => by
          rcases hBUV hx with h | h; exact Or.inr h; exact Or.inl h)
        hdisj.symm h0V)
  intro W₁ W₂ hW₁ hW₂ hBW hWdisj h0W₁
  -- Partition B by how the pair (z, −z) falls in W₁ or W₂.
  let B₁₁ : Set ℂ := B ∩ W₁ ∩ ((fun z : ℂ => -z) ⁻¹' W₁)
  let B₂₂ : Set ℂ := B ∩ W₂ ∩ ((fun z : ℂ => -z) ⁻¹' W₂)
  let B₁₂ : Set ℂ := B ∩ W₁ ∩ ((fun z : ℂ => -z) ⁻¹' W₂)
  have hB₁₁_cl : IsClosed B₁₁ :=
    (hBclosed.inter hW₁).inter (hW₁.preimage continuous_neg)
  have hB₂₂_cl : IsClosed B₂₂ :=
    (hBclosed.inter hW₂).inter (hW₂.preimage continuous_neg)
  have hB₁₂_cl : IsClosed B₁₂ :=
    (hBclosed.inter hW₁).inter (hW₂.preimage continuous_neg)
  -- The sq-images of these sets lie in A and are closed.
  let A₁ : Set ℂ := (· ^ 2) '' B₁₁
  let A₂ : Set ℂ := (· ^ 2) '' B₂₂
  let A₁₂ : Set ℂ := (· ^ 2) '' B₁₂
  have hA₁_cl : IsClosed A₁ := sq_closed B₁₁ hB₁₁_cl
  have hA₂₁₂_cl : IsClosed (A₂ ∪ A₁₂) :=
    (sq_closed B₂₂ hB₂₂_cl).union (sq_closed B₁₂ hB₁₂_cl)
  -- 0 ∈ A₁ (since 0 ∈ B₁₁).
  have h0A₁ : (0 : ℂ) ∈ A₁ := by
    refine ⟨0, ?_, by norm_num⟩
    simp [B₁₁, h0B, h0W₁]
  -- Every element of A lies in A₁ ∪ A₂ ∪ A₁₂.
  have hA_cov : A ⊆ A₁ ∪ (A₂ ∪ A₁₂) := by
    intro a ha
    obtain ⟨z, hz⟩ := complex_exists_sq_root a
    have hzB : z ∈ B := show z ^ 2 ∈ A from hz ▸ ha
    have h_negB : -z ∈ B := h_neg_B z hzB
    rcases hBW hzB with hzW₁ | hzW₂
    · rcases hBW h_negB with h_negW₁ | h_negW₂
      · exact Or.inl ⟨z, ⟨⟨hzB, hzW₁⟩, h_negW₁⟩, hz⟩
      · exact Or.inr (Or.inr ⟨z, ⟨⟨hzB, hzW₁⟩, h_negW₂⟩, hz⟩)
    · rcases hBW h_negB with h_negW₁ | h_negW₂
      · -- z ∈ W₂, −z ∈ W₁: use −z ∈ B₁₂ with (−z)² = z² = a
        exact Or.inr (Or.inr ⟨-z, ⟨⟨h_negB, h_negW₁⟩, by simpa using hzW₂⟩,
                                by simpa [neg_sq] using hz⟩)
      · exact Or.inr (Or.inl ⟨z, ⟨⟨hzB, hzW₂⟩, h_negW₂⟩, hz⟩)
  -- A₁ and A₂ ∪ A₁₂ are disjoint.
  have hA_disj : Disjoint A₁ (A₂ ∪ A₁₂) := by
    rw [Set.disjoint_left]
    rintro a ⟨z₁, ⟨⟨_, hz₁W₁⟩, h_negz₁W₁⟩, hz₁⟩ (⟨z₂, ⟨⟨_, hz₂W₂⟩, _⟩, hz₂⟩ |
                                                    ⟨z₂, ⟨⟨_, hz₂W₁⟩, h_negz₂W₂⟩, hz₂⟩)
    · -- a ∈ A₁ ∩ A₂: z₁² = z₂², z₁ ∈ W₁, z₂ ∈ W₂
      have hsquare : z₁ ^ 2 = z₂ ^ 2 := by simpa using hz₁.trans hz₂.symm
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsquare with rfl | rfl
      · -- z₁ = z₂ ∈ W₁ ∩ W₂
        exact absurd (Set.disjoint_left.mp hWdisj hz₁W₁) (by simp [hz₂W₂])
      · -- z₁ = -z₂: z₂ = -z₁ ∈ W₁ (since -z₁ ∈ W₁ from B₁₁)
        have hz₂W₁' : z₂ ∈ W₁ := by simpa using h_negz₁W₁
        exact (Set.disjoint_left.mp hWdisj hz₂W₁' hz₂W₂).elim
    · -- a ∈ A₁ ∩ A₁₂: z₁² = z₂², z₁ ∈ W₁, -z₁ ∈ W₁, z₂ ∈ W₁, -z₂ ∈ W₂
      have hsquare : z₁ ^ 2 = z₂ ^ 2 := by simpa using hz₁.trans hz₂.symm
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsquare with rfl | rfl
      · -- z₁ = z₂: -z₁ = -z₂ ∈ W₁ ∩ W₂
        have hnegz₁W₂ : -z₁ ∈ W₂ := by simpa using h_negz₂W₂
        exact (Set.disjoint_left.mp hWdisj h_negz₁W₁ hnegz₁W₂).elim
      · -- z₁ = -z₂: -z₂ = z₁ ∈ W₁. -z₂ ∈ W₂ (from B₁₂). So z₁ = -z₂ ∈ W₁ ∩ W₂.
        have hnegz₂W₁ : -z₂ ∈ W₁ := by simpa using hz₁W₁
        have hnegz₂W₂ : -z₂ ∈ W₂ := by simpa using h_negz₂W₂
        exact (Set.disjoint_left.mp hWdisj hnegz₂W₁ hnegz₂W₂).elim
  -- By preconnectedness of A, A ⊆ A₁ (since A ⊆ A₁ ∪ (A₂ ∪ A₁₂), both closed, disjoint,
  -- and 0 ∈ A₁ prevents A ⊆ A₂ ∪ A₁₂).
  rcases (isPreconnected_iff_subset_of_fully_disjoint_closed hAclosed).mp hA
      A₁ (A₂ ∪ A₁₂) hA₁_cl hA₂₁₂_cl hA_cov hA_disj with hAinA₁ | hAinA₂₁₂
  · -- A ⊆ A₁: every z ∈ B has z² ∈ A₁, so some w with w² = z² ∈ W₁ and -w ∈ W₁ → z ∈ W₁.
    intro z hz
    obtain ⟨w, ⟨⟨_, hwW₁⟩, h_negwW₁⟩, hw⟩ := hAinA₁ (show z ^ 2 ∈ A from hz)
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hw with rfl | rfl
    · exact hwW₁
    · -- w = -z: then `-w = z`, so the preimage-membership field gives `z ∈ W₁`.
      simpa using h_negwW₁
  · -- A ⊆ A₂ ∪ A₁₂ contradicts 0 ∈ A₁ and Disjoint A₁ (A₂ ∪ A₁₂).
    exact absurd (Set.disjoint_left.mp hA_disj h0A₁ (hAinA₂₁₂ h0)) id

/-- If `A ⊆ ℂ` is closed, preconnected, and contains `c`, then the pullback
under `z ↦ z^2 + c` is preconnected. -/
theorem isPreconnected_quadratic_preimage {A : Set ℂ} {c : ℂ}
    (hA : IsPreconnected A) (hAclosed : IsClosed A) (hc : c ∈ A) :
    IsPreconnected {z : ℂ | z ^ 2 + c ∈ A} := by
  let T : Homeomorph ℂ ℂ := Homeomorph.addRight (-c)
  have hpre_eq : IsPreconnected ((fun z : ℂ => z + (-c)) '' A) ↔ IsPreconnected A :=
    T.isEmbedding.isInducing.isPreconnected_image
  have hA' : IsPreconnected ((fun z : ℂ => z + (-c)) '' A) := hpre_eq.2 hA
  have hAclosed' : IsClosed ((fun z : ℂ => z + (-c)) '' A) :=
    T.isClosedMap _ hAclosed
  have h0' : (0 : ℂ) ∈ (fun z : ℂ => z + (-c)) '' A := by
    refine ⟨c, hc, by simp⟩
  have hsq : IsPreconnected {z : ℂ | z ^ 2 ∈ (fun z : ℂ => z + (-c)) '' A} :=
    isPreconnected_sq_preimage hA' hAclosed' h0'
  have hEq : {z : ℂ | z ^ 2 ∈ (fun z : ℂ => z + (-c)) '' A} = {z : ℂ | z ^ 2 + c ∈ A} := by
    ext z
    simp [Set.mem_image, exists_eq_right, add_comm, add_left_comm, add_assoc]
  simpa [hEq] using hsq

/-! ## Part 2: Decreasing intersection of compact connected sets -/

/-- A decreasing intersection of nonempty compact preconnected subsets
of a T2 space is preconnected. -/
theorem isPreconnected_iInter_of_sequence {X : Type*} [TopologicalSpace X]
    [T2Space X] {S : ℕ → Set X}
    (h_anti : Antitone S) (h_ne : ∀ n, (S n).Nonempty)
    (h_compact : ∀ n, IsCompact (S n))
    (h_conn : ∀ n, IsPreconnected (S n)) :
    IsPreconnected (⋂ n, S n) := by
  set I := ⋂ n, S n with hI_def
  rw [isPreconnected_iff_subset_of_disjoint_closed]
  intro U V hUcl hVcl hIUV hIUV_disj
  -- A = I ∩ U and B = I ∩ V are compact, disjoint, and cover I
  set A := I ∩ U with hA_def
  set B := I ∩ V with hB_def
  have hI_closed : IsClosed I := isClosed_iInter (fun i => (h_compact i).isClosed)
  have hA_closed : IsClosed A := hI_closed.inter hUcl
  have hB_closed : IsClosed B := hI_closed.inter hVcl
  have hA_compact : IsCompact A :=
    (h_compact 0).of_isClosed_subset hA_closed
      ((inter_subset_left).trans (iInter_subset S 0))
  have hB_compact : IsCompact B :=
    (h_compact 0).of_isClosed_subset hB_closed
      ((inter_subset_left).trans (iInter_subset S 0))
  have hAB_disj : Disjoint A B := by
    rw [Set.disjoint_iff]
    intro x ⟨⟨hxI, hxU⟩, ⟨_, hxV⟩⟩
    have : x ∈ I ∩ (U ∩ V) := ⟨hxI, hxU, hxV⟩
    rw [hIUV_disj] at this; exact this
  -- If both A, B nonempty, separate by disjoint open sets (T2 + compact)
  by_cases hA_ne : A.Nonempty
  · by_cases hB_ne : B.Nonempty
    · -- Both nonempty → get disjoint open separation
      have hsep := SeparatedNhds.of_isCompact_isCompact hA_compact hB_compact hAB_disj
      obtain ⟨W₁, W₂, hW₁open, hW₂open, hAW₁, hBW₂, hW_disj⟩ := hsep
      -- I ⊆ W₁ ∪ W₂
      have hI_sub : I ⊆ W₁ ∪ W₂ := by
        intro x hx
        have hx_UV := hIUV hx
        rcases hx_UV with hxU | hxV
        · exact Or.inl (hAW₁ ⟨hx, hxU⟩)
        · exact Or.inr (hBW₂ ⟨hx, hxV⟩)
      -- Cantor: ∃ N, S_N ⊆ W₁ ∪ W₂
      have h_eventually : ∃ N, S N ⊆ W₁ ∪ W₂ := by
        by_contra h
        push_neg at h
        have h_ne' : ∀ n, (S n \ (W₁ ∪ W₂)).Nonempty :=
          fun n => nonempty_of_not_subset (h n)
        have h_closed' : ∀ n, IsClosed (S n \ (W₁ ∪ W₂)) := fun n =>
          (h_compact n).isClosed.sdiff (hW₁open.union hW₂open)
        have h_anti' : ∀ n, S (n + 1) \ (W₁ ∪ W₂) ⊆ S n \ (W₁ ∪ W₂) :=
          fun n => diff_subset_diff_left (h_anti (Nat.le_succ n))
        have h_sub0 : ∀ n, S n \ (W₁ ∪ W₂) ⊆ S 0 :=
          fun n => (diff_subset_diff_left (h_anti (Nat.zero_le n))).trans diff_subset
        have h_compact_n : ∀ n, IsCompact (S n \ (W₁ ∪ W₂)) := fun n =>
          (h_compact 0).of_isClosed_subset (h_closed' n) (h_sub0 n)
        have h_iInter_ne :=
          IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
            (fun n => S n \ (W₁ ∪ W₂)) h_anti' h_ne' (h_compact_n 0) h_closed'
        have h_eq : (⋂ n, S n \ (W₁ ∪ W₂)) = I \ (W₁ ∪ W₂) := by
          ext x; simp only [mem_iInter, mem_diff, mem_union, hI_def]; constructor
          · intro h; exact ⟨fun i => (h i).1, fun huv => (h 0).2 huv⟩
          · intro ⟨h1, h2⟩ i; exact ⟨h1 i, h2⟩
        rw [h_eq] at h_iInter_ne
        obtain ⟨x, hx_in, hx_not⟩ := h_iInter_ne
        exact hx_not (hI_sub hx_in)
      obtain ⟨N, hN⟩ := h_eventually
      -- S_N ∩ W₁ and S_N ∩ W₂ both nonempty (A, B ⊆ S_N)
      have hSN_W1 : (S N ∩ W₁).Nonempty := by
        obtain ⟨a, ha⟩ := hA_ne
        exact ⟨a, (iInter_subset S N) ha.1, hAW₁ ha⟩
      have hSN_W2 : (S N ∩ W₂).Nonempty := by
        obtain ⟨b, hb⟩ := hB_ne
        exact ⟨b, (iInter_subset S N) hb.1, hBW₂ hb⟩
      -- S_N preconnected → S_N ∩ W₁ ∩ W₂ ≠ ∅
      have := h_conn N W₁ W₂ hW₁open hW₂open hN hSN_W1 hSN_W2
      -- But W₁ ∩ W₂ = ∅ — contradiction
      obtain ⟨x, _, hxW1, hxW2⟩ := this
      exact (Set.disjoint_left.mp hW_disj hxW1 hxW2).elim
    · -- B empty → I ⊆ U
      left; intro x hx
      have := hIUV hx
      rcases this with hxU | hxV
      · exact hxU
      · exact absurd ⟨x, hx, hxV⟩ hB_ne
  · -- A empty → I ⊆ V
    right; intro x hx
    have := hIUV hx
    rcases this with hxU | hxV
    · exact absurd ⟨x, hx, hxU⟩ hA_ne
    · exact hxV

/-! ## Part 3: Filled Julia set connectivity -/

/-- The filled Julia set `K c` is connected for `c ∈ MandelbrotSet`. -/
theorem filled_julia_set_connected_proved {c : ℂ} (hc : c ∈ MandelbrotSet) :
    IsConnected (K c) := by
  let S : ℕ → Set ℂ := fun n => {z : ℂ | ‖orbit c z n‖ ≤ R c}
  have horbit_fc : ∀ n z, orbit c (fc c z) n = orbit c z (n + 1) := by
    intro n z
    induction n with
    | zero => simp [fc, orbit_succ]
    | succ n ih => simp [orbit_succ, ih]
  have hS_closed : ∀ n, IsClosed (S n) := by
    intro n
    dsimp [S]
    simpa using isClosed_le ((continuous_orbit c n).norm) continuous_const
  have hS_compact : ∀ n, IsCompact (S n) := by
    intro n
    have hsubset : S n ⊆ Metric.closedBall (0 : ℂ) (R c) := by
      intro z hz
      rcases le_or_gt ‖z‖ (R c) with hle | hgt
      · simpa [Metric.mem_closedBall, dist_zero_right] using hle
      · exfalso
        have hge : ‖orbit c z n‖ ≥ ‖z‖ := norm_orbit_ge_of_norm_ge_R c z n hgt
        exact not_lt_of_ge (le_trans hge hz) hgt
    refine (isCompact_closedBall (x := (0 : ℂ)) (r := R c)).of_isClosed_subset (hS_closed n) hsubset
  have hcrit : ∀ n, ‖orbit c 0 n‖ ≤ R c := by
    intro n
    rcases hc with ⟨M, hM⟩
    by_cases hgt : ‖orbit c 0 n‖ > R c
    · exfalso
      rcases escape_lemma (c := c) (z := 0) n hgt M with ⟨N, hN⟩
      have hbig := hN (max N n) (le_max_left _ _)
      have hbound := hM (max N n)
      exact not_lt_of_ge hbound hbig
    · exact le_of_not_gt hgt
  have hS_nonempty : ∀ n, (S n).Nonempty := by
    intro n
    exact ⟨0, by simpa [S] using hcrit n⟩
  have hS_pre : ∀ n, IsPreconnected (S n) := by
    intro n
    induction n with
    | zero =>
        have hEq : S 0 = Metric.closedBall (0 : ℂ) (R c) := by
          ext z
          simp [S, Metric.mem_closedBall, dist_zero_right]
        rw [hEq]
        exact (convex_closedBall (0 : ℂ) (R c)).isPreconnected
    | succ n ihn =>
        have hEq : S (n + 1) = {z : ℂ | z ^ 2 + c ∈ S n} := by
          ext z
          change ‖orbit c z (n + 1)‖ ≤ R c ↔ z ^ 2 + c ∈ S n
          rw [show orbit c z (n + 1) = orbit c (fc c z) n by simpa [horbit_fc]]
          simp [S, fc]
        have hcrit_shift : orbit c c n = orbit c 0 (n + 1) := by
          simpa [fc, orbit_zero] using (horbit_fc n 0)
        have hcSn : c ∈ S n := by
          change ‖orbit c c n‖ ≤ R c
          rw [hcrit_shift]
          exact hcrit (n + 1)
        rw [hEq]
        exact isPreconnected_quadratic_preimage ihn (hS_closed n) hcSn
  have hS_anti_step : ∀ n, S (n + 1) ⊆ S n := by
    intro n z hz
    by_cases hgt : ‖orbit c z n‖ > R c
    · have hge : ‖orbit c z (n + 1)‖ ≥ ‖orbit c z n‖ := by
        simpa [orbit_succ] using norm_orbit_ge_of_norm_ge_R c (orbit c z n) 1 hgt
      exact (not_lt_of_ge (le_trans hge hz) hgt).elim
    · exact le_of_not_gt hgt
  have hS_anti : Antitone S := by
    intro m n hmn
    induction hmn with
    | refl => intro z hz; exact hz
    | @step n hle ih => exact Set.Subset.trans (hS_anti_step n) ih
  have hK_subset : K c ⊆ ⋂ k, S k := by
    intro z hz
    rw [Set.mem_iInter]
    intro k
    rcases hz with ⟨M, hM⟩
    change ‖orbit c z k‖ ≤ R c
    by_cases hgt : ‖orbit c z k‖ > R c
    · exfalso
      rcases escape_lemma (c := c) (z := z) k hgt M with ⟨N, hN⟩
      have hbig := hN (max N k) (le_max_left _ _)
      have hbound := hM (max N k)
      exact not_lt_of_ge hbound hbig
    · exact le_of_not_gt hgt
  have hK_superset : (⋂ k, S k) ⊆ K c := by
    intro z hz
    refine ⟨R c, ?_⟩
    intro k
    have hk : z ∈ S k := by
      rw [Set.mem_iInter] at hz
      exact hz k
    exact hk
  have hK_eq : K c = ⋂ n, S n := by
    exact Set.Subset.antisymm hK_subset hK_superset
  have hpre : IsPreconnected (K c) := by
    rw [hK_eq]
    exact isPreconnected_iInter_of_sequence hS_anti hS_nonempty hS_compact hS_pre
  have hne : (K c).Nonempty := by
    rw [hK_eq]
    have h_inter := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      S (fun n => hS_anti_step n) hS_nonempty (hS_compact 0) hS_closed
    simpa [Set.mem_iInter] using h_inter
  exact ⟨hne, hpre⟩

end
