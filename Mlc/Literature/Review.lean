import Mlc.Core
import Mlc.ParameterClassification
import Mlc.Quadratic.Complex.ParaPuzzleBasis
import Mlc.Quadratic.Complex.YoccozConformal
import Mlc.RenormalizationTypes
import Mathlib.Topology.Connected.LocallyConnected

/-!
# Literature-facing interfaces for the MLC review

This namespace separates three different claims which are easy to conflate:

* a theorem already proved by the Lean library;
* a theorem interface whose analytic hypotheses still have to be formalized;
* the global MLC target.

The declarations in this file are propositions and metadata only.  In
particular, no declaration below turns an external result into an axiom.
-/

namespace MLC
namespace Literature

open Filter Set Topology

noncomputable section

variable {X : Type*} [TopologicalSpace X]

/-- Pointwise local connectedness in the form used by the Mathlib criterion. -/
def LocallyConnectedAt (X : Type*) [TopologicalSpace X] (x : X) : Prop :=
  ∀ U ∈ 𝓝 x, ∃ V ∈ 𝓝 x, IsPreconnected V ∧ V ⊆ U

theorem locallyConnectedAt_iff :
    LocallyConnectedSpace X ↔ ∀ x : X, LocallyConnectedAt X x := by
  simpa [LocallyConnectedAt] using
    (locallyConnectedSpace_iff_connected_subsets (α := X))

/-- Local connectedness of the Mandelbrot set at a specified parameter. -/
def MandelbrotLocallyConnectedAt
    (c : ℂ) (hc : c ∈ MLC.mandelbrotSet) : Prop :=
  LocallyConnectedAt MLC.mandelbrotSet ⟨c, hc⟩

/-- The global MLC target, named for use by the literature ledger. -/
def GlobalMLC : Prop :=
  LocallyConnectedSpace MLC.mandelbrotSet

theorem globalMLC_implies_pointwise
    (h : GlobalMLC) (c : ℂ) (hc : c ∈ MLC.mandelbrotSet) :
    MandelbrotLocallyConnectedAt c hc := by
  exact (locallyConnectedAt_iff (X := MLC.mandelbrotSet)).mp h ⟨c, hc⟩

/-- A reusable logical shape for a theorem proving MLC at a parameter class. -/
def PointwiseMLCResult (parameterClass : ℂ → Prop) : Prop :=
  ∀ (c : ℂ) (hc : c ∈ MLC.mandelbrotSet),
    parameterClass c → MandelbrotLocallyConnectedAt c hc

/-- The finite-level data needed to turn Yoccoz parapuzzles into a local
connectivity proof at one parameter. -/
structure ParaPuzzleCertificate
    (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet) : Prop where
  connected :
    ∀ n, IsConnected
      (MLC.Quadratic.ParaPuzzlePieceAt c n ∩
        MLC.Quadratic.MandelbrotSet)
  shrinks :
    (⋂ n, MLC.Quadratic.ParaPuzzlePieceAt c n) = {c}

/-- The topological phase from a connected shrinking parapuzzle basis to MLC. -/
theorem localConnectivity_of_paraPuzzleCertificate
    (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet)
    (data : ParaPuzzleCertificate c hc) :
    MandelbrotLocallyConnectedAt c hc := by
  exact MLC.preconnected_nhds_of_shrink_of_connected_at
    c hc data.connected data.shrinks

/-- The unresolved existence statement for a Yoccoz-style parameter basis. -/
def YoccozParameterPuzzleResult : Prop :=
  ∀ (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet),
    Nonempty (ParaPuzzleCertificate c hc)

/-- The finitely-renormalizable pointwise result in its formal target shape. -/
def FinitelyRenormalizableMLC : Prop :=
  PointwiseMLCResult MLC.FinitelyRenormalizable

/-- The attracting-cycle pointwise result in its formal target shape. -/
def AttractingCycleMLC : Prop :=
  PointwiseMLCResult ParameterClassification.HasAttractingCycle

/-- A parameterized interface for a bounded-type satellite theorem.

The exact combinatorial predicate is intentionally supplied by the eventual
renormalization formalization; this declaration does not guess its definition.
-/
def BoundedTypeSatelliteMLC (isBoundedTypeSatellite : ℂ → Prop) : Prop :=
  PointwiseMLCResult isBoundedTypeSatellite

/-- A parameterized interface for a Feigenbaum theorem. -/
def FeigenbaumMLC (isFeigenbaum : ℂ → Prop) : Prop :=
  PointwiseMLCResult isFeigenbaum

/-- The local puzzle-shrinkage theorem already available in this repository. -/
theorem yoccoz_puzzle_shrinkage (c : ℂ)
    (h : MLC.FinitelyRenormalizable c) :
    (⋂ n, MLC.Quadratic.DynamicalPuzzlePiece c n 0) = {0} :=
  MLC.Quadratic.yoccoz_theorem_conformal c h

/-- The local parameter-basis interface used by a future parapuzzle theorem. -/
theorem paraPuzzle_basis_interface
    (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet)
    (hshrinks :
      (⋂ n, MLC.Quadratic.ParaPuzzlePieceAt c n) = {c}) :
    ∀ U ∈ 𝓝 (⟨c, hc⟩ : MLC.Quadratic.MandelbrotSet), ∃ n,
      {x : MLC.Quadratic.MandelbrotSet |
        x.val ∈ MLC.Quadratic.ParaPuzzlePieceAt c n} ⊆ U :=
  MLC.para_puzzle_piece_basis_induced c hc hshrinks

/-- The existing conditional global root in the same ledger vocabulary. -/
theorem uniformOuterBuffer_implies_globalMLC :
    ParameterComponent.MandelbrotUniformOuterBuffer → GlobalMLC :=
  MLC.mlc_conjecture_of_uniformOuterBuffer

inductive ProofStatus
  | provedInLibrary
  | interfaceOnly
  | openObligation
  deriving Repr, DecidableEq

structure Reference where
  key : String
  authors : String
  title : String
  locator : String
  url : String
  deriving Repr, DecidableEq

structure ResultRecord where
  key : String
  statement : String
  status : ProofStatus
  reference : Reference
  deriving Repr, DecidableEq

def douadyHubbard : Reference :=
  { key := "douady-hubbard-orsay"
    authors := "A. Douady and J. H. Hubbard"
    title := "Exploring the Mandelbrot Set: The Orsay Notes"
    locator := "Chapters 2--8"
    url := "https://pi.math.cornell.edu/~hubbard/OrsayEnglish.pdf" }

def yoccoz : Reference :=
  { key := "yoccoz-1995"
    authors := "J.-C. Yoccoz"
    title := "Theoreme de Siegel, nombres de Bruno et polynomes quadratiques"
    locator := "Asterisque 231 (1995), pp. 1--88"
    url := "https://www.numdam.org/book-part/AST_1995__231__1_0/" }

def lyubichGeometry : Reference :=
  { key := "lyubich-geometry-1993"
    authors := "M. Lyubich"
    title := "Geometry of quadratic polynomials: moduli, rigidity and local connectivity"
    locator := "arXiv:math/9309215"
    url := "https://arxiv.org/abs/math/9309215" }

def lyubichDynamics : Reference :=
  { key := "lyubich-dynamics-1997"
    authors := "M. Lyubich"
    title := "Dynamics of quadratic polynomials, I--II"
    locator := "Acta Mathematica 178 (1997), no. 2, pp. 185--297"
    url := "https://doi.org/10.1007/BF02392694" }

def lyubichVolumeThree : Reference :=
  { key := "lyubich-dynamics-iii"
    authors := "M. Lyubich"
    title := "Dynamics of quadratic polynomials, III: parapuzzle and SBR measures"
    locator := "Asterisque 261 (2000), pp. 173--200"
    url := "https://numdam.org/item/AST_2000__261__173_0/" }

def lyubichConformalNotes : Reference :=
  { key := "lyubich-conformal-notes"
    authors := "M. Lyubich"
    title := "Conformal Geometry and Dynamics of Quadratic Polynomials"
    locator := "ICTP lecture notes, 2013"
    url := "https://indico.ictp.it/event/a12182/session/2/contribution/1/material/0/0.pdf" }

def dudkoLyubichSatellite : Reference :=
  { key := "dudko-lyubich-satellite"
    authors := "D. Dudko and M. Lyubich"
    title := "Local connectivity of the Mandelbrot set at some satellite parameter of bounded type"
    locator := "arXiv:1808.10425; GAFA 33 (2023), no. 4, pp. 912--1047"
    url := "https://arxiv.org/abs/1808.10425" }

def dudkoLyubichFeigenbaum : Reference :=
  { key := "dudko-lyubich-feigenbaum"
    authors := "D. Dudko and M. Lyubich"
    title := "MLC at Feigenbaum points"
    locator := "arXiv:2309.02107; Publ. Math. IHES 143 (2026), pp. 97--141"
    url := "https://arxiv.org/abs/2309.02107" }

def dudkoMLC : Reference :=
  { key := "dudko-mlc-2025"
    authors := "D. Dudko"
    title := "On the MLC Conjecture and the Renormalization Theory in Complex Dynamics"
    locator := "arXiv:2512.24171"
    url := "https://arxiv.org/abs/2512.24171" }

def reviewedResults : List ResultRecord :=
  [ { key := "yoccoz-puzzle-shrinkage"
      statement := "Divergent puzzle-annulus moduli force the critical puzzle pieces to shrink to the critical point."
      status := .provedInLibrary
      reference := yoccoz }
  , { key := "douady-hubbard-phase-parameter"
      statement := "The phase--parameter and external-ray machinery needed for parameter puzzles."
      status := .interfaceOnly
      reference := douadyHubbard }
  , { key := "lyubich-renormalization"
      statement := "Principal nests, a priori bounds, renormalization, and parameter-puzzle control."
      status := .interfaceOnly
      reference := lyubichDynamics }
  , { key := "lyubich-parapuzzle"
      statement := "Parapuzzle and parameter-plane machinery for quadratic dynamics."
      status := .interfaceOnly
      reference := lyubichVolumeThree }
  , { key := "lyubich-conformal-notes"
      statement := "Expository conformal and dynamical background used to organize the formalization."
      status := .interfaceOnly
      reference := lyubichConformalNotes }
  , { key := "dudko-lyubich-satellite-mlc"
      statement := "Local connectivity at the bounded-type satellite parameters covered by the paper."
      status := .openObligation
      reference := dudkoLyubichSatellite }
  , { key := "dudko-lyubich-feigenbaum-mlc"
      statement := "Local connectivity at the Feigenbaum points covered by the paper."
      status := .openObligation
      reference := dudkoLyubichFeigenbaum }
  , { key := "global-mlc"
      statement := "The Mandelbrot set is locally connected."
      status := .openObligation
      reference := dudkoMLC } ]

end

end Literature
end MLC
