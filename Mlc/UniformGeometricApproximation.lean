import Mlc.CategoricalMandelbrot
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Conditional uniform geometric retractions

An `OrbitRetractionTower` consists only of continuous finite-stage maps and
explicit numerical certificates. Its adjacent-map bound is summable. On a
compact parameter domain this gives a continuous uniform limit, with error
at most `16 * (1 / 2) ^ n`. The finite-orbit proximity and fixing certificates
force the limit to take values in, and fix, the Mandelbrot set.

No tower is constructed here: constructing one is a separate geometric
problem. In particular, none of the fields assumes a limit, continuity of a
limit, or surjectivity.
-/

namespace MLC.UniformGeometry

open Set Filter Topology

noncomputable section

/-- Finite-stage data for a conditional geometric retraction theorem.
The depths are natural orbit-prefix lengths; they need not be monotone.
The `maps_to` field is available for subsequent deformations inside `K`,
although convergence itself does not use it. -/
structure OrbitRetractionTower (K : Set ℂ) where
  depth : ℕ → ℕ
  le_depth : ∀ n, n ≤ depth n
  map : ℕ → C(K, ℂ)
  maps_to : ∀ n x, map n x ∈ K
  fixes_outer :
    ∀ n (x : K),
      (x : ℂ) ∈ MLC.Categorical.Mandelbrot.outerOrbitSet (depth n) →
        map n x = x
  near_outer :
    ∀ n x, ∃ y ∈ MLC.Categorical.Mandelbrot.outerOrbitSet (depth n),
      dist (map n x) y ≤ (1 / 2 : ℝ) ^ n
  adjacent_bound :
    ∀ n x, dist (map (n + 1) x) (map n x) ≤ 8 * (1 / 2 : ℝ) ^ n

namespace OrbitRetractionTower

variable {K : Set ℂ}

/-- Summability of the adjacent sup-distance bounds produces a continuous
uniform limit with the explicit geometric tail estimate. -/
theorem exists_uniform_limit (T : OrbitRetractionTower K) (hcompact : IsCompact K) :
    ∃ r : C(K, ℂ),
      TendstoUniformly (fun n x => T.map n x) r atTop ∧
      ∀ n x, dist (T.map n x) (r x) ≤ 16 * (1 / 2 : ℝ) ^ n := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hcompact
  have hadj : ∀ n, dist (T.map n) (T.map (n + 1)) ≤ 8 * (1 / 2 : ℝ) ^ n := by
    intro n
    apply (ContinuousMap.dist_le (by positivity)).mpr
    intro x
    simpa only [dist_comm] using T.adjacent_bound n x
  have hcauchy : CauchySeq T.map :=
    cauchySeq_of_le_geometric (1 / 2) 8 (by norm_num) hadj
  obtain ⟨r, hr⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨r, ?_, ?_⟩
  · apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hr ε hε
    filter_upwards [eventually_ge_atTop N] with n hn
    intro x
    exact (ContinuousMap.dist_apply_le_dist x).trans_lt
      (by simpa only [dist_comm] using hN n hn)
  · intro n x
    have htail := dist_le_of_le_geometric_of_tendsto
      (1 / 2) 8 (by norm_num) hadj hr n
    have htail' : dist (T.map n) r ≤ 16 * (1 / 2 : ℝ) ^ n := by
      convert htail using 1
      ring
    exact (ContinuousMap.dist_apply_le_dist x).trans htail'

/-- A map satisfying the certified tail bound takes values in every closed
finite-orbit stage, hence in their intersection, the Mandelbrot set. -/
theorem limit_mem_mandelbrot (T : OrbitRetractionTower K)
    {r : K → ℂ}
    (htail : ∀ n x, dist (T.map n x) (r x) ≤ 16 * (1 / 2 : ℝ) ^ n)
    (x : K) :
    r x ∈ MLC.Categorical.Mandelbrot.set := by
  rw [← MLC.Categorical.Mandelbrot.iInter_outerOrbitSet_eq_set]
  refine mem_iInter.mpr ?_
  intro k
  apply (MLC.Categorical.Mandelbrot.isClosed_outerOrbitSet k).closure_subset
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (1 / 2 : ℝ) ^ m < ε / 17 :=
    exists_pow_lt_of_lt_one (by positivity) (by norm_num)
  let n := max k m
  have hkn : k ≤ T.depth n := (Nat.le_max_left k m).trans (T.le_depth n)
  have hpow : (1 / 2 : ℝ) ^ n ≤ (1 / 2 : ℝ) ^ m :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_max_right k m)
  obtain ⟨y, hy, hxy⟩ := T.near_outer n x
  refine ⟨y, MLC.Categorical.Mandelbrot.outerOrbitSet_antitone hkn hy, ?_⟩
  have hdist : dist (r x) y ≤ 17 * (1 / 2 : ℝ) ^ n := by
    calc
      dist (r x) y ≤ dist (r x) (T.map n x) + dist (T.map n x) y :=
        dist_triangle _ _ _
      _ ≤ 16 * (1 / 2 : ℝ) ^ n + (1 / 2 : ℝ) ^ n := by
        exact add_le_add (by simpa only [dist_comm] using htail n x) hxy
      _ = 17 * (1 / 2 : ℝ) ^ n := by ring
  exact hdist.trans_lt (by linarith)

/-- Every pointwise limit fixes the Mandelbrot points of the domain, since
every finite-stage map already fixes them. -/
theorem limit_fixes_mandelbrot (T : OrbitRetractionTower K)
    {r : K → ℂ}
    (hlimit : ∀ x, Tendsto (fun n => T.map n x) atTop (𝓝 (r x)))
    (x : K) (hx : (x : ℂ) ∈ MLC.Categorical.Mandelbrot.set) :
    r x = x := by
  have hfixed : ∀ n, T.map n x = x := fun n =>
    T.fixes_outer n x (MLC.Categorical.Mandelbrot.set_subset_outerOrbitSet _ hx)
  have hconst : Tendsto (fun n => T.map n x) atTop (𝓝 (x : ℂ)) := by
    simpa only [hfixed] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (x : ℂ))
      atTop (𝓝 (x : ℂ)))
  exact tendsto_nhds_unique (hlimit x) hconst

end OrbitRetractionTower

/-- A compact-domain tower yields a continuous retraction onto the
Mandelbrot set, with uniform convergence and error `16 * (1 / 2) ^ n`.
The returned map has codomain `ℂ`; its range equality and fixing property
express that it is a retraction. Only the exact-range conclusion needs
the hypothesis that the domain contains the whole Mandelbrot set. -/
theorem exists_continuous_retraction {K : Set ℂ}
    (hcompact : IsCompact K) (hMK : MLC.Categorical.Mandelbrot.set ⊆ K)
    (T : OrbitRetractionTower K) :
    ∃ r : C(K, ℂ),
      TendstoUniformly (fun n x => T.map n x) r atTop ∧
      (∀ n x, dist (T.map n x) (r x) ≤ 16 * (1 / 2 : ℝ) ^ n) ∧
      Set.range r = MLC.Categorical.Mandelbrot.set ∧
      ∀ x : K, (x : ℂ) ∈ MLC.Categorical.Mandelbrot.set → r x = x := by
  obtain ⟨r, huniform, htail⟩ := T.exists_uniform_limit hcompact
  have hfix : ∀ x : K, (x : ℂ) ∈ MLC.Categorical.Mandelbrot.set → r x = x :=
    T.limit_fixes_mandelbrot (fun x => huniform.tendsto_at x)
  refine ⟨r, huniform, htail, ?_, hfix⟩
  apply Set.Subset.antisymm
  · rintro y ⟨x, rfl⟩
    exact T.limit_mem_mandelbrot htail x
  · intro y hy
    exact ⟨⟨y, hMK hy⟩, hfix ⟨y, hMK hy⟩ hy⟩

end

end MLC.UniformGeometry
