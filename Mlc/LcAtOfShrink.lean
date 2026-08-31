import Yoccoz.Quadratic.Complex.Basic
import Yoccoz.Quadratic.Complex.Puzzle
import Mlc.Quadratic.Complex.PuzzleLemmas2
import Mlc.Quadratic.Complex.PuzzleBoundaryMotion
import Mlc.Quadratic.Complex.ParaPuzzle
import Mlc.BMolFilledJulia
import Mlc.AnalyticQuadraticLikeFamilyCore
import Mathlib.Topology.Connected.LocallyConnected
import Lean

open Lean Elab Command

namespace MLC

open Quadratic Complex Topology Set Filter
open Molecule

/-- Replacement hook for connectivity of parameter puzzle pieces on `M`. -/
abbrev ParaPuzzlePieceInterMandelbrotConnectedData : Prop :=
  Quadratic.ParaPuzzlePieceInterMandelbrotConnectedData

/-- Focused consumer interface for a depth-indexed moving parameter-piece family
at a fixed base parameter. This packages only the hypotheses actually used by
`LcAtOfShrink`: openness, base-point membership, a basis property, and
connectedness of the induced Mandelbrot pieces. -/
structure ParameterPieceLcAtData (c : ℂ) (P : ℕ → Set ℂ) : Prop where
  piece_open : ∀ n, IsOpen (P n)
  base_mem : ∀ n, c ∈ P n
  basis : ∀ U ∈ 𝓝 c, ∃ n, P n ⊆ U
  inter_mandelbrot_connected :
    ∀ n, IsConnected (P n ∩ MandelbrotSet)

/-- Honest finite-level moving connectedness-locus slices coming from
quadratic-like parameter families. These are not assumed open in the ambient
parameter plane. -/
def connectednessLocusParameterPiece
    (F : ℕ → BMolParameterFamily ℂ) (n : ℕ) : Set ℂ :=
  (F n).connectednessLocus

@[simp] lemma mem_connectednessLocusParameterPiece_iff
    (F : ℕ → BMolParameterFamily ℂ) (n : ℕ) (c : ℂ) :
    c ∈ connectednessLocusParameterPiece F n ↔
      c ∈ (F n).parameterSet ∧ FilledJuliaConnected ((F n).map c) :=
  Iff.rfl

@[simp] lemma connectednessLocusParameterPiece_eq
    (F : ℕ → BMolParameterFamily ℂ) (n : ℕ) :
    connectednessLocusParameterPiece F n = (F n).connectednessLocus :=
  rfl

/-- The ambient open parameter window attached to a family level. -/
def connectednessWindowParameterPiece
    (F : ℕ → BMolParameterFamily ℂ) (n : ℕ) : Set ℂ :=
  (F n).parameterSet

@[simp] lemma mem_connectednessWindowParameterPiece_iff
    (F : ℕ → BMolParameterFamily ℂ) (n : ℕ) (c : ℂ) :
    c ∈ connectednessWindowParameterPiece F n ↔ c ∈ (F n).parameterSet :=
  Iff.rfl

@[simp] lemma connectednessWindowParameterPiece_eq
    (F : ℕ → BMolParameterFamily ℂ) (n : ℕ) :
    connectednessWindowParameterPiece F n = (F n).parameterSet :=
  rfl

lemma connectednessLocusParameterPiece_subset_window
    (F : ℕ → BMolParameterFamily ℂ) (n : ℕ) :
    connectednessLocusParameterPiece F n ⊆ connectednessWindowParameterPiece F n := by
  intro c hc
  exact (mem_connectednessLocusParameterPiece_iff F n c).1 hc |>.1

lemma connectednessLocusParameterPiece_inter_mandelbrot_subset_window_inter_mandelbrot
    (F : ℕ → BMolParameterFamily ℂ) (n : ℕ) :
    connectednessLocusParameterPiece F n ∩ MandelbrotSet ⊆
      connectednessWindowParameterPiece F n ∩ MandelbrotSet := by
  intro c hc
  exact ⟨connectednessLocusParameterPiece_subset_window F n hc.1, hc.2⟩

/-- Corrected moving-family adapter: local connectivity consumes the open window
family, while connectedness is supplied for the relative Mandelbrot slices cut
out by those windows. A separate connectedness locus can be tracked inside the
window, but is not required to be open. -/
structure ConnectednessWindowParameterPieceData
    (c : ℂ) (W K : ℕ → Set ℂ) : Prop where
  window_open : ∀ n, IsOpen (W n)
  base_mem_window : ∀ n, c ∈ W n
  basis : ∀ U ∈ 𝓝 c, ∃ n, W n ⊆ U
  locus_subset_window : ∀ n, K n ⊆ W n
  inter_mandelbrot_connected : ∀ n, IsConnected (W n ∩ MandelbrotSet)

lemma ConnectednessWindowParameterPieceData.toParameterPieceLcAtData
    {c : ℂ} {W K : ℕ → Set ℂ}
    (hWK : ConnectednessWindowParameterPieceData c W K) :
    ParameterPieceLcAtData c W where
  piece_open := hWK.window_open
  base_mem := hWK.base_mem_window
  basis := hWK.basis
  inter_mandelbrot_connected := hWK.inter_mandelbrot_connected

/-- Specialization of the corrected window/locus split to an honest BMol family.
`W` is the ambient parameter window, `K` is the connectedness locus inside it. -/
structure ConnectednessLocusWindowFamilyData
    (c : ℂ) (F : ℕ → BMolParameterFamily ℂ) : Prop where
  window_open : ∀ n, IsOpen (connectednessWindowParameterPiece F n)
  base_mem_window : ∀ n, c ∈ connectednessWindowParameterPiece F n
  basis : ∀ U ∈ 𝓝 c, ∃ n, connectednessWindowParameterPiece F n ⊆ U
  inter_mandelbrot_connected :
    ∀ n, IsConnected (connectednessWindowParameterPiece F n ∩ MandelbrotSet)

lemma ConnectednessLocusWindowFamilyData.toConnectednessWindowParameterPieceData
    {c : ℂ} {F : ℕ → BMolParameterFamily ℂ}
    (hF : ConnectednessLocusWindowFamilyData c F) :
    ConnectednessWindowParameterPieceData c
      (connectednessWindowParameterPiece F)
      (connectednessLocusParameterPiece F) where
  window_open := hF.window_open
  base_mem_window := hF.base_mem_window
  basis := hF.basis
  locus_subset_window := connectednessLocusParameterPiece_subset_window F
  inter_mandelbrot_connected := hF.inter_mandelbrot_connected

/-- The smallest honest finite moving parameter window presently available from a
BMol-family level: its parameter domain. -/
def finiteMovingParameterWindow
    (F : BMolParameterFamily ℂ) : Set ℂ :=
  F.parameterSet

@[simp] lemma mem_finiteMovingParameterWindow_iff
    (F : BMolParameterFamily ℂ) (c : ℂ) :
    c ∈ finiteMovingParameterWindow F ↔ c ∈ F.parameterSet :=
  Iff.rfl

@[simp] lemma finiteMovingParameterWindow_eq_parameterSet
    (F : BMolParameterFamily ℂ) :
    finiteMovingParameterWindow F = F.parameterSet :=
  rfl

/-- A finite-level analytically-scoped moving parameter window coming from the
existing quadratic-like family core is exactly its parameter domain. -/
def analyticCoreFiniteMovingParameterWindow
    (F : AnalyticQuadraticLikeFamilyCore) : Set ℂ :=
  F.parameterSet

@[simp] lemma analyticCoreFiniteMovingParameterWindow_eq
    (F : AnalyticQuadraticLikeFamilyCore) :
    analyticCoreFiniteMovingParameterWindow F = F.parameterSet :=
  rfl

lemma isOpen_analyticCoreFiniteMovingParameterWindow
    (F : AnalyticQuadraticLikeFamilyCore) :
    IsOpen (analyticCoreFiniteMovingParameterWindow F) := by
  simpa [analyticCoreFiniteMovingParameterWindow_eq F] using F.isOpen_parameterSet

lemma mem_analyticCoreFiniteMovingParameterWindow
    (F : AnalyticQuadraticLikeFamilyCore) {c : ℂ} (hc : c ∈ F.parameterSet) :
    c ∈ analyticCoreFiniteMovingParameterWindow F := by
  simpa [analyticCoreFiniteMovingParameterWindow_eq F] using hc

/-- Stronger bridge target implying para-puzzle connectedness on `M`. -/
abbrev ParaPuzzleMandelbrotSubsetData : Prop :=
  Quadratic.ParaPuzzleMandelbrotSubsetData

/-- Transport-witness bridge target for para-puzzle connectedness on `M`. -/
abbrev ParaPuzzleInterMandelbrotTransportData :=
  Quadratic.ParaPuzzleInterMandelbrotTransportData

/-- Existential transport-witness bridge target for para-puzzle connectedness
    on `M`. -/
abbrev ParaPuzzleInterMandelbrotTransportExistsData : Prop :=
  Quadratic.ParaPuzzleInterMandelbrotTransportExistsData

/-- Local connectivity at a point in a topological space. -/
def LocallyConnectedAt (X : Type*) [TopologicalSpace X] (x : X) : Prop :=
  ∀ U ∈ 𝓝 x, ∃ V ∈ 𝓝 x, V ⊆ U ∧ IsConnected V

/-- If a space is locally connected at every point, it is a locally connected space. -/
lemma locallyConnectedSpace_of_locallyConnectedAt {X : Type*} [TopologicalSpace X]
    (h : ∀ x : X, LocallyConnectedAt X x) : LocallyConnectedSpace X := by
  rw [locallyConnectedSpace_iff_connectedComponentIn_open]
  intro F hF x _
  rw [isOpen_iff_mem_nhds]
  intro y hy
  have hyF : y ∈ F := connectedComponentIn_subset F x hy
  have h_nhds : F ∈ 𝓝 y := hF.mem_nhds hyF
  obtain ⟨V, hV_nhds, hV_sub, hV_conn⟩ := h y F h_nhds
  filter_upwards [hV_nhds] with z hz
  have hy_in_V : y ∈ V := mem_of_mem_nhds hV_nhds
  have hV_sub_comp : V ⊆ connectedComponentIn F y :=
    IsPreconnected.subset_connectedComponentIn hV_conn.isPreconnected hy_in_V hV_sub
  have h_eq : connectedComponentIn F y = connectedComponentIn F x :=
    (connectedComponentIn_eq hy).symm
  rw [← h_eq]
  exact hV_sub_comp hz

/-- A set in a subtype is connected iff its image in the ambient space is connected. -/
lemma isConnected_subtype_val_image {X : Type*} [TopologicalSpace X] {p : X → Prop}
    (s : Set { x // p x }) :
    IsConnected ((Subtype.val : { x // p x } → X) '' s) ↔ IsConnected s := by
  classical
  -- First reduce to preconnectedness using the general theorem for inducing maps.
  have h_pre :
      IsPreconnected ((Subtype.val : { x // p x } → X) '' s) ↔ IsPreconnected s :=
    Topology.IsInducing.isPreconnected_image (s := s)
      (f := (Subtype.val : { x // p x } → X))
      (IsEmbedding.subtypeVal.isInducing)
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · -- Nonemptiness transfers from the image back to the subtype.
      rcases h.1 with ⟨x, hx⟩
      rcases hx with ⟨y, hy, rfl⟩
      exact ⟨y, hy⟩
    · -- And preconnectedness is equivalent by `isPreconnected_image`.
      exact h_pre.1 h.2
  · intro h
    refine ⟨?_, ?_⟩
    · -- Nonemptiness transfers from the subtype to the image.
      rcases h.1 with ⟨y, hy⟩
      exact ⟨Subtype.val y, ⟨y, hy, rfl⟩⟩
    · exact h_pre.2 h.2

/-- Connectedness in the subtype, parameterized by the replacement hook. -/
lemma para_puzzle_piece_induced_connected_of_data
    (h_conn : ParaPuzzlePieceInterMandelbrotConnectedData)
    (c : ℂ) (hc : c ∈ MandelbrotSet) (n : ℕ) :
    IsConnected { x : MandelbrotSet | x.val ∈ ParaPuzzlePieceAt c n } := by
  rw [← isConnected_subtype_val_image]
  rw [show { x : MandelbrotSet | x.val ∈ ParaPuzzlePieceAt c n } =
        (Subtype.val : MandelbrotSet → ℂ) ⁻¹' (ParaPuzzlePieceAt c n) by rfl]
  rw [Subtype.image_preimage_coe]
  try rw [Set.inter_comm]
  exact h_conn c hc n

/-- Pointwise-at-`c` route for subtype connectedness. -/
lemma para_puzzle_piece_induced_connected_of_at
    (c : ℂ)
    (h_conn_at : ∀ n, IsConnected (ParaPuzzlePieceAt c n ∩ MandelbrotSet))
    (n : ℕ) :
    IsConnected { x : MandelbrotSet | x.val ∈ ParaPuzzlePieceAt c n } := by
  rw [← isConnected_subtype_val_image]
  rw [show { x : MandelbrotSet | x.val ∈ ParaPuzzlePieceAt c n } =
        (Subtype.val : MandelbrotSet → ℂ) ⁻¹' (ParaPuzzlePieceAt c n) by rfl]
  rw [Subtype.image_preimage_coe]
  try rw [Set.inter_comm]
  exact h_conn_at n

/-- The intersection of a parameter puzzle piece with the Mandelbrot set is
    connected in the subtype topology. -/
lemma para_puzzle_piece_induced_connected (c : ℂ) (hc : c ∈ MandelbrotSet) (n : ℕ) :
    IsConnected { x : MandelbrotSet | x.val ∈ ParaPuzzlePieceAt c n } :=
  para_puzzle_piece_induced_connected_of_data
    (Quadratic.para_puzzle_piece_inter_mandelbrot_connected_data_of_transport_exists_data
      Quadratic.para_puzzle_transport_exists_data_of_motion_default)
    c hc n

/-- Subset-data route for subtype connectedness. -/
lemma para_puzzle_piece_induced_connected_of_mandelbrot_subset_data
    (hsub : ParaPuzzleMandelbrotSubsetData)
    (c : ℂ) (hc : c ∈ MandelbrotSet) (n : ℕ) :
    IsConnected { x : MandelbrotSet | x.val ∈ ParaPuzzlePieceAt c n } :=
  para_puzzle_piece_induced_connected_of_data
    (Quadratic.para_puzzle_piece_inter_mandelbrot_connected_data_of_mandelbrot_subset_data hsub)
    c hc n

/-- Transport-data route for subtype connectedness. -/
lemma para_puzzle_piece_induced_connected_of_transport_data
    (htr : ParaPuzzleInterMandelbrotTransportData)
    (c : ℂ) (hc : c ∈ MandelbrotSet) (n : ℕ) :
    IsConnected { x : MandelbrotSet | x.val ∈ ParaPuzzlePieceAt c n } :=
  para_puzzle_piece_induced_connected_of_data
    (Quadratic.para_puzzle_piece_inter_mandelbrot_connected_data_of_transport_data htr)
    c hc n

/-- Existential-transport-data route for subtype connectedness. -/
lemma para_puzzle_piece_induced_connected_of_transport_exists_data
    (hex : ParaPuzzleInterMandelbrotTransportExistsData)
    (c : ℂ) (hc : c ∈ MandelbrotSet) (n : ℕ) :
    IsConnected { x : MandelbrotSet | x.val ∈ ParaPuzzlePieceAt c n } :=
  para_puzzle_piece_induced_connected_of_data
    (Quadratic.para_puzzle_piece_inter_mandelbrot_connected_data_of_transport_exists_data hex)
    c hc n

/-- Generic connectedness transport from the ambient plane to the Mandelbrot
subtype for a depth-indexed parameter-piece family. -/
lemma parameter_piece_induced_connected
    (P : ℕ → Set ℂ)
    (h_conn : ∀ n, IsConnected (P n ∩ MandelbrotSet))
    (n : ℕ) :
    IsConnected { x : MandelbrotSet | x.val ∈ P n } := by
  rw [← isConnected_subtype_val_image]
  rw [show { x : MandelbrotSet | x.val ∈ P n } =
        (Subtype.val : MandelbrotSet → ℂ) ⁻¹' (P n) by rfl]
  rw [Subtype.image_preimage_coe]
  try rw [Set.inter_comm]
  exact h_conn n

/-- Generic neighborhood-basis transfer from the ambient plane to the Mandelbrot
subtype for a depth-indexed parameter-piece family. -/
lemma parameter_piece_basis_induced
    (c : ℂ) (hc : c ∈ MandelbrotSet)
    (P : ℕ → Set ℂ)
    (h_basis : ∀ U ∈ 𝓝 c, ∃ n, P n ⊆ U) :
    ∀ U ∈ 𝓝 (⟨c, hc⟩ : MandelbrotSet), ∃ n,
      { x : MandelbrotSet | x.val ∈ P n } ⊆ U := by
  intro U hU
  rw [mem_nhds_iff] at hU
  obtain ⟨V, hV_sub_U, hV_open, hc_in_V⟩ := hU
  obtain ⟨W, hW_open, hW_eq⟩ := isOpen_induced_iff.mp hV_open
  rw [← hW_eq] at hc_in_V hV_sub_U
  have hc_in_W : c ∈ W := hc_in_V
  have hW_nhds : W ∈ 𝓝 c := hW_open.mem_nhds hc_in_W
  obtain ⟨n, hn_sub⟩ := h_basis W hW_nhds
  use n
  intro x hx
  apply hV_sub_U
  exact hn_sub hx

/-- If parameter pieces shrink to a point, they form a basis of neighborhoods for c in the Mandelbrot set.
    Proof idea: Since the intersection of all parameter pieces `ParaPuzzlePieceAt c n` is exactly `{c}`,
    for any open neighborhood `U` of `c`, there must be some `n` such that `ParaPuzzlePieceAt c n ⊆ U`.
    This uses the compactness argument implicit in the "shrink to point" property for nested compact sets
    (or similar topological argument). Here we formalize it by showing `M ∩ P_n` eventually lies in `U`. -/
lemma para_puzzle_piece_basis_induced (c : ℂ) (hc : c ∈ MandelbrotSet)
    (h : (⋂ n, ParaPuzzlePieceAt c n) = {c}) :
    ∀ U ∈ 𝓝 (⟨c, hc⟩ : MandelbrotSet), ∃ n,
      { x : MandelbrotSet | x.val ∈ ParaPuzzlePieceAt c n } ⊆ U := by
  intro U hU
  rw [mem_nhds_iff] at hU
  obtain ⟨V, hV_sub_U, hV_open, hc_in_V⟩ := hU
  obtain ⟨W, hW_open, hW_eq⟩ := isOpen_induced_iff.mp hV_open
  rw [← hW_eq] at hc_in_V hV_sub_U
  have hc_in_W : c ∈ W := hc_in_V
  have hW_nhds : W ∈ 𝓝 c := hW_open.mem_nhds hc_in_W
  obtain ⟨n, hn_sub⟩ := para_puzzle_piece_basis c h W hW_nhds
  use n
  intro x hx
  apply hV_sub_U
  exact hn_sub hx

lemma lc_at_of_shrink_of_family_data
    (c : ℂ) (hc : c ∈ MandelbrotSet)
    (P : ℕ → Set ℂ)
    (hdata : ParameterPieceLcAtData c P) :
    LocallyConnectedAt MandelbrotSet ⟨c, hc⟩ := by
  rw [LocallyConnectedAt]
  intro U hU
  obtain ⟨n, hn_sub⟩ :=
    parameter_piece_basis_induced c hc P hdata.basis U hU
  let V' := { x : MandelbrotSet | x.val ∈ P n }
  use V'
  constructor
  · rw [mem_nhds_iff]
    use V'
    constructor
    · exact subset_rfl
    · constructor
      · rw [isOpen_induced_iff]
        use P n
        constructor
        · exact hdata.piece_open n
        · rfl
      · exact hdata.base_mem n
  · constructor
    · exact hn_sub
    · exact parameter_piece_induced_connected P hdata.inter_mandelbrot_connected n

lemma lc_at_of_connectednessWindow_family_data
    (c : ℂ) (hc : c ∈ MandelbrotSet)
    (W K : ℕ → Set ℂ)
    (hdata : ConnectednessWindowParameterPieceData c W K) :
    LocallyConnectedAt MandelbrotSet ⟨c, hc⟩ := by
  exact lc_at_of_shrink_of_family_data c hc W hdata.toParameterPieceLcAtData

lemma lc_at_of_connectednessLocus_family_data
    (c : ℂ) (hc : c ∈ MandelbrotSet)
    (F : ℕ → BMolParameterFamily ℂ)
    (hdata : ConnectednessLocusWindowFamilyData c F) :
    LocallyConnectedAt MandelbrotSet ⟨c, hc⟩ := by
  exact lc_at_of_connectednessWindow_family_data c hc
    (connectednessWindowParameterPiece F)
    (connectednessLocusParameterPiece F)
    hdata.toConnectednessWindowParameterPieceData

lemma lc_at_of_shrink_of_data
    (h_conn : ParaPuzzlePieceInterMandelbrotConnectedData)
    (c : ℂ) (hc : c ∈ MandelbrotSet)
    (h : (⋂ n, ParaPuzzlePieceAt c n) = {c}) :
    LocallyConnectedAt MandelbrotSet ⟨c, hc⟩ := by
  exact lc_at_of_shrink_of_family_data c hc (fun n => ParaPuzzlePieceAt c n)
    { piece_open := fun n => para_puzzle_piece_open c n
      base_mem := by
        intro n
        have hc_in_inter : c ∈ ⋂ k, ParaPuzzlePieceAt c k := by
          rw [h]
          exact Set.mem_singleton c
        exact Set.mem_iInter.mp hc_in_inter n
      basis := fun U hU => para_puzzle_piece_basis c h U hU
      inter_mandelbrot_connected :=
        fun n => h_conn c hc n }

/-- Pointwise-at-`c` connectedness route for local-connectivity from
    para-puzzle shrinkage. -/
lemma lc_at_of_shrink_of_connected_at
    (c : ℂ) (hc : c ∈ MandelbrotSet)
    (h_conn_at : ∀ n, IsConnected (ParaPuzzlePieceAt c n ∩ MandelbrotSet))
    (h : (⋂ n, ParaPuzzlePieceAt c n) = {c}) :
    LocallyConnectedAt MandelbrotSet ⟨c, hc⟩ := by
  rw [LocallyConnectedAt]
  intro U hU
  obtain ⟨n, hn_sub⟩ := para_puzzle_piece_basis_induced c hc h U hU
  let V' := { x : MandelbrotSet | x.val ∈ ParaPuzzlePieceAt c n }
  use V'
  constructor
  · rw [mem_nhds_iff]
    use V'
    constructor
    · exact subset_rfl
    · constructor
      · rw [isOpen_induced_iff]
        use ParaPuzzlePieceAt c n
        constructor
        · exact para_puzzle_piece_open c n
        · rfl
      · have hc_in_inter : c ∈ ⋂ k, ParaPuzzlePieceAt c k := by
          rw [h]
          exact Set.mem_singleton c
        exact Set.mem_iInter.mp hc_in_inter n
  · constructor
    · exact hn_sub
    · exact para_puzzle_piece_induced_connected_of_at c h_conn_at n

/-- If parameter pieces shrink to a point, M is locally connected at c.
    Proof idea: We construct a basis of connected neighborhoods for `c`.
    1.  The parameter pieces `P_n` are open (by `para_puzzle_piece_open`).
    2.  Their intersection with `M` is connected (by `para_puzzle_piece_induced_connected`).
    3.  They shrink to `{c}` (hypothesis).
    4.  Therefore, for any neighborhood `U`, we can find a `P_n` inside it. `P_n ∩ M` serves
        as the connected neighborhood of `c` contained in `U`, proving local connectivity. -/
lemma lc_at_of_shrink (c : ℂ) (hc : c ∈ MandelbrotSet)
    (h : (⋂ n, ParaPuzzlePieceAt c n) = {c}) :
    LocallyConnectedAt MandelbrotSet ⟨c, hc⟩ :=
  lc_at_of_shrink_of_data
    (Quadratic.para_puzzle_piece_inter_mandelbrot_connected_data_of_transport_exists_data
      Quadratic.para_puzzle_transport_exists_data_of_motion_default)
    c hc h

/-- Subset-data route for local-connectivity from para-puzzle shrinkage. -/
lemma lc_at_of_shrink_of_mandelbrot_subset_data
    (hsub : ParaPuzzleMandelbrotSubsetData)
    (c : ℂ) (hc : c ∈ MandelbrotSet)
    (h : (⋂ n, ParaPuzzlePieceAt c n) = {c}) :
    LocallyConnectedAt MandelbrotSet ⟨c, hc⟩ :=
  lc_at_of_shrink_of_data
    (Quadratic.para_puzzle_piece_inter_mandelbrot_connected_data_of_mandelbrot_subset_data hsub)
    c hc h

/-- A para-puzzle transport witness can be repackaged as a generic moving-window
family at a fixed base point, without changing the mathematical content. This is
an interface migration step only: the windows remain `ParaPuzzlePieceAt c n`. -/
lemma connectednessWindowData_of_paraPuzzleTransportData
    (htr : ParaPuzzleInterMandelbrotTransportData)
    (c : ℂ) (hc : c ∈ MandelbrotSet)
    (h : (⋂ n, ParaPuzzlePieceAt c n) = {c}) :
    ConnectednessWindowParameterPieceData c
      (fun n => ParaPuzzlePieceAt c n)
      (fun n => htr.transportSet c n) where
  window_open := fun n => para_puzzle_piece_open c n
  base_mem_window := by
    intro n
    have hc_in_inter : c ∈ ⋂ k, ParaPuzzlePieceAt c k := by
      rw [h]
      exact Set.mem_singleton c
    exact Set.mem_iInter.mp hc_in_inter n
  basis := fun U hU => para_puzzle_piece_basis c h U hU
  locus_subset_window := by
    intro n z hz
    have h_eq : htr.transportSet c n = ParaPuzzlePieceAt c n ∩ MandelbrotSet :=
      htr.eq_inter c hc n
    have hz' : z ∈ ParaPuzzlePieceAt c n ∩ MandelbrotSet := by simpa [h_eq] using hz
    exact hz'.1
  inter_mandelbrot_connected := by
    intro n
    exact Quadratic.para_puzzle_piece_inter_mandelbrot_connected_data_of_transport_data htr c hc n

/-- Transport-data route for local-connectivity from para-puzzle shrinkage. -/
lemma lc_at_of_shrink_of_transport_data
    (htr : ParaPuzzleInterMandelbrotTransportData)
    (c : ℂ) (hc : c ∈ MandelbrotSet)
    (h : (⋂ n, ParaPuzzlePieceAt c n) = {c}) :
    LocallyConnectedAt MandelbrotSet ⟨c, hc⟩ :=
  lc_at_of_connectednessWindow_family_data c hc
    (fun n => ParaPuzzlePieceAt c n)
    (fun n => htr.transportSet c n)
    (connectednessWindowData_of_paraPuzzleTransportData htr c hc h)

/-- Existential-transport-data route for local-connectivity from
    para-puzzle shrinkage. -/
lemma lc_at_of_shrink_of_transport_exists_data
    (hex : ParaPuzzleInterMandelbrotTransportExistsData)
    (c : ℂ) (hc : c ∈ MandelbrotSet)
    (h : (⋂ n, ParaPuzzlePieceAt c n) = {c}) :
    LocallyConnectedAt MandelbrotSet ⟨c, hc⟩ :=
  lc_at_of_shrink_of_data
    (Quadratic.para_puzzle_piece_inter_mandelbrot_connected_data_of_transport_exists_data hex)
    c hc h

end MLC
