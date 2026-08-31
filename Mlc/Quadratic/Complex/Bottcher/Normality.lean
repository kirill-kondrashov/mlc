import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mlc.Quadratic.Complex.Bottcher.ChordalMetric

/-!
# Topological normality via Arzelà–Ascoli

Building on the Marty equicontinuity engine of `ChordalMetric.lean`, this file delivers the
**topological form of Montel's normality theorem**: a family `f` of holomorphic functions on a
compact convex set `s`, whose spherical derivatives are uniformly bounded, is a *normal family*
in the sense that the range of the sphere-lifted family has **compact closure** in the
compact-open topology.

The key idea is completeness-free: the images `stereo (f i z)` all lie on the unit sphere of
`ℝ³`, a **compact** metric space.  So the family, bundled as bounded continuous functions
`↥s →ᵇ EuclideanSpace ℝ (Fin 3)`, has range inside a fixed compact ball, and — being uniformly
equicontinuous (`uniformEquicontinuous_stereo_comp`) — satisfies the hypotheses of Mathlib's
`BoundedContinuousFunction.arzela_ascoli`, whose conclusion `IsCompact (closure …)` is exactly
topological normality.

This is the Arzelà–Ascoli half of the Zalcman route to *strong* Montel; combined with the
Zalcman rescaling lemma and `little_picard` it discharges the parameter-puzzle straddling axiom.
-/

namespace MLC.Quadratic

open Set BoundedContinuousFunction

open BoundedContinuousFunction in
/-- The holomorphic family `f`, lifted through the inverse stereographic embedding to the
compact sphere and bundled as bounded continuous functions on the compact domain `↥s`. -/
noncomputable def sphereLift {ι : Type*} {s : Set ℂ} [CompactSpace ↥s] (f : ι → ℂ → ℂ)
    (hdiff : ∀ i, ∀ z ∈ s, DifferentiableAt ℂ (f i) z) (i : ι) :
    ↥s →ᵇ EuclideanSpace ℝ (Fin 3) :=
  mkOfCompact ⟨fun p => stereo (f i ↑p),
    continuous_stereo.comp (ContinuousOn.restrict
      (fun z hz => (hdiff i z hz).continuousAt.continuousWithinAt))⟩

@[simp] lemma sphereLift_apply {ι : Type*} {s : Set ℂ} [CompactSpace ↥s] (f : ι → ℂ → ℂ)
    (hdiff : ∀ i, ∀ z ∈ s, DifferentiableAt ℂ (f i) z) (i : ι) (p : ↥s) :
    sphereLift f hdiff i p = stereo (f i ↑p) := rfl

/-- **Topological Montel normality.**  A family of holomorphic functions on a compact convex set
`s` with uniformly bounded spherical derivative is *normal*: the sphere-lifted family has compact
closure in the compact-open topology.  Proved by Arzelà–Ascoli, using that the codomain sphere is
compact and the family is uniformly (chordally) equicontinuous. -/
theorem normal_family {ι : Type*} {s : Set ℂ} [CompactSpace ↥s] (hsconv : Convex ℝ s)
    (f : ι → ℂ → ℂ) (M : ℝ)
    (hdiff : ∀ i, ∀ z ∈ s, DifferentiableAt ℂ (f i) z)
    (hb : ∀ i, ∀ z ∈ s, sphericalDeriv (f i) z ≤ M) :
    IsCompact (closure (Set.range (sphereLift f hdiff))) := by
  set A : Set (↥s →ᵇ EuclideanSpace ℝ (Fin 3)) := Set.range (sphereLift f hdiff) with hA
  have hin : ∀ (g : ↥s →ᵇ EuclideanSpace ℝ (Fin 3)) (x : ↥s), g ∈ A →
      g x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
    rintro g x ⟨i, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right, sphereLift_apply]
    exact le_of_eq (stereo_norm _)
  have hEqui_ι : Equicontinuous (fun (i : ι) (p : ↥s) => stereo (f i ↑p)) :=
    (uniformEquicontinuous_stereo_comp hsconv f M hdiff hb).equicontinuous
  classical
  let φ : A → ι := fun a => (Set.mem_range.1 a.2).choose
  have hφ : ∀ a : A, sphereLift f hdiff (φ a) = a.1 := fun a => (Set.mem_range.1 a.2).choose_spec
  have hfeq : ((↑) : A → ↥s → EuclideanSpace ℝ (Fin 3))
      = (fun (i : ι) (p : ↥s) => stereo (f i ↑p)) ∘ φ := by
    funext a p
    have h := congrArg (fun g : ↥s →ᵇ _ => g p) (hφ a)
    simpa using h.symm
  have H : Equicontinuous ((↑) : A → ↥s → EuclideanSpace ℝ (Fin 3)) := by
    rw [hfeq]; exact hEqui_ι.comp φ
  exact BoundedContinuousFunction.arzela_ascoli
    (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) (isCompact_closedBall _ _) A hin H

/-- **Sequential form of Montel normality.**  Under the hypotheses of `normal_family`, every
sequence drawn from the family admits a subsequence whose sphere lift converges uniformly on the
compact domain `↥s` to a continuous limit.  This is the concrete "normal family" statement
consumed by the Zalcman rescaling / strong-Montel argument: a compact-open relatively compact
family is sequentially compact because the space of bounded continuous functions is metric. -/
theorem normal_family_seq {ι : Type*} {s : Set ℂ} [CompactSpace ↥s] (hsconv : Convex ℝ s)
    (f : ι → ℂ → ℂ) (M : ℝ)
    (hdiff : ∀ i, ∀ z ∈ s, DifferentiableAt ℂ (f i) z)
    (hb : ∀ i, ∀ z ∈ s, sphericalDeriv (f i) z ≤ M)
    (a : ℕ → ι) :
    ∃ (g : ↥s →ᵇ EuclideanSpace ℝ (Fin 3)) (φ : ℕ → ℕ), StrictMono φ ∧
      Filter.Tendsto (fun n => sphereLift f hdiff (a (φ n))) Filter.atTop (nhds g) := by
  have hcpt : IsCompact (closure (Set.range (sphereLift f hdiff))) :=
    normal_family hsconv f M hdiff hb
  have hseq := hcpt.isSeqCompact
  have hmem : ∀ n, sphereLift f hdiff (a n) ∈ closure (Set.range (sphereLift f hdiff)) :=
    fun n => subset_closure ⟨a n, rfl⟩
  obtain ⟨g, _, φ, hφ, htends⟩ := hseq hmem
  exact ⟨g, φ, hφ, htends⟩

end MLC.Quadratic
