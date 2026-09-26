import Mlc.CategoricalMandelbrot

/-!
# Finite combinatorial outer approximations

The finite combinatorial content is represented by a finite family of compact
cells at each resolution.  The fields of `FiniteCellOuterApproximation` are
the exact certificates that a concrete interval, cubical, or CAD
implementation must check.  The limit theorem below is proved from those
certificates and does not introduce an axiom.
-/

namespace MLC
namespace CertifiedOrbit

open Set Metric

noncomputable section

def dyadicRadius (n : ℕ) : ℝ :=
  (1 / 2 : ℝ) ^ n

lemma dyadicRadius_pos (n : ℕ) : 0 < dyadicRadius n := by
  dsimp [dyadicRadius]
  positivity

lemma exists_dyadicRadius_lt {ε : ℝ} (hε : 0 < ε) :
    ∃ n, dyadicRadius n < ε := by
  exact exists_pow_lt_of_lt_one hε (by norm_num)

/-- Number of subdivisions in each coordinate of the parameter square. -/
def dyadicGridCount (n : ℕ) : ℕ :=
  2 ^ n

/-- Side length of a dyadic grid square at resolution `n`. -/
def dyadicGridStep (n : ℕ) : ℝ :=
  4 / (dyadicGridCount n : ℝ)

def dyadicGridLower (n : ℕ) (i : Fin (dyadicGridCount n)) : ℝ :=
  -2 + (i.val : ℝ) * dyadicGridStep n

def dyadicGridBox (n : ℕ) (i j : Fin (dyadicGridCount n)) : Set ℂ :=
  {z | dyadicGridLower n i ≤ z.re ∧
    z.re ≤ dyadicGridLower n i + dyadicGridStep n ∧
    dyadicGridLower n j ≤ z.im ∧
    z.im ≤ dyadicGridLower n j + dyadicGridStep n}

lemma dyadicGridCount_pos (n : ℕ) : 0 < dyadicGridCount n := by
  simp [dyadicGridCount]

noncomputable def dyadicGridCoordinateIndex (n : ℕ) (x : ℝ) :
    Fin (dyadicGridCount n) :=
  ⟨min (Nat.floor ((x + 2) / dyadicGridStep n))
      (dyadicGridCount n - 1),
    by
      have hN := dyadicGridCount_pos n
      have hlast : dyadicGridCount n - 1 < dyadicGridCount n := by omega
      exact lt_of_le_of_lt (Nat.min_le_right _ _) hlast⟩

lemma dyadicGridStep_pos (n : ℕ) : 0 < dyadicGridStep n := by
  rw [dyadicGridStep]
  exact div_pos (by norm_num)
    (Nat.cast_pos.mpr (dyadicGridCount_pos n))

lemma dyadicGridStep_mul_count (n : ℕ) :
    dyadicGridStep n * (dyadicGridCount n : ℝ) = 4 := by
  rw [dyadicGridStep]
  have hcount : (dyadicGridCount n : ℝ) ≠ 0 :=
    (Nat.cast_pos.mpr (dyadicGridCount_pos n)).ne'
  field_simp [hcount]

lemma dyadicGridStep_eq_four_radius (n : ℕ) :
    dyadicGridStep n = 4 * dyadicRadius n := by
  calc
    dyadicGridStep n = 4 * ((2 : ℝ) ^ n)⁻¹ := by
      simp [dyadicGridStep, dyadicGridCount, div_eq_mul_inv]
    _ = 4 * ((2 : ℝ)⁻¹) ^ n := by rw [inv_pow]
    _ = 4 * (1 / 2 : ℝ) ^ n := by norm_num
    _ = 4 * dyadicRadius n := by rfl

lemma dyadicGridCount_succ (n : ℕ) :
    dyadicGridCount (n + 1) = 2 * dyadicGridCount n := by
  simp [dyadicGridCount, pow_succ, Nat.mul_comm]

lemma dyadicGridStep_succ (n : ℕ) :
    dyadicGridStep (n + 1) = dyadicGridStep n / 2 := by
  calc
    dyadicGridStep (n + 1) =
        4 / (2 * (dyadicGridCount n : ℝ)) := by
          simp [dyadicGridStep, dyadicGridCount_succ, Nat.cast_mul]
    _ = (4 / (dyadicGridCount n : ℝ)) / 2 := by ring
    _ = dyadicGridStep n / 2 := by rw [dyadicGridStep]

lemma isClosed_dyadicGridBox (n : ℕ)
    (i j : Fin (dyadicGridCount n)) :
    IsClosed (dyadicGridBox n i j) := by
  unfold dyadicGridBox
  exact (isClosed_le continuous_const Complex.continuous_re).inter
    ((isClosed_le Complex.continuous_re continuous_const).inter
      ((isClosed_le continuous_const Complex.continuous_im).inter
        (isClosed_le Complex.continuous_im continuous_const)))

/-- Every real coordinate in `[-2,2]` belongs to one interval of the finite
dyadic grid. -/
lemma dyadicGridCoordinateIndex_mem (n : ℕ) {x : ℝ}
    (hxlo : -2 ≤ x) (hxhi : x ≤ 2) :
    dyadicGridLower n (dyadicGridCoordinateIndex n x) ≤ x ∧
      x ≤ dyadicGridLower n (dyadicGridCoordinateIndex n x) +
        dyadicGridStep n := by
  let N := dyadicGridCount n
  let q : ℝ := (x + 2) / dyadicGridStep n
  have hstep : 0 < dyadicGridStep n := dyadicGridStep_pos n
  have hN : 0 < N := by dsimp [N]; exact dyadicGridCount_pos n
  have hstepN : dyadicGridStep n * (N : ℝ) = 4 := by
    simpa [N] using dyadicGridStep_mul_count n
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    exact div_nonneg (by linarith) hstep.le
  have hq_le : q ≤ (N : ℝ) := by
    dsimp [q]
    rw [div_le_iff₀ hstep]
    calc
      x + 2 ≤ 4 := by linarith
      _ = (N : ℝ) * dyadicGridStep n := by
        rw [mul_comm]
        exact hstepN.symm
  let k := min (Nat.floor q) (N - 1)
  have hk_floor : (k : ℝ) ≤ (Nat.floor q : ℝ) := by
    exact_mod_cast (Nat.min_le_left (Nat.floor q) (N - 1))
  have hk_le_q : (k : ℝ) ≤ q :=
    hk_floor.trans (Nat.floor_le hq_nonneg)
  have hq_le_succ_k : q ≤ (k : ℝ) + 1 := by
    by_cases hfloor : Nat.floor q ≤ N - 1
    · have hk : k = Nat.floor q := min_eq_left hfloor
      rw [hk]
      exact (Nat.lt_floor_add_one q).le
    · have hlast_floor : N - 1 ≤ Nat.floor q :=
        Nat.le_of_lt (lt_of_not_ge hfloor)
      have hk : k = N - 1 := min_eq_right hlast_floor
      rw [hk]
      have hcast : (N : ℝ) = ((N - 1 : ℕ) : ℝ) + 1 := by
        norm_cast
        omega
      rw [← hcast]
      exact hq_le
  have hleft : (k : ℝ) * dyadicGridStep n ≤ x + 2 :=
    (le_div_iff₀ hstep).mp hk_le_q
  have hright : x + 2 ≤ ((k : ℝ) + 1) * dyadicGridStep n :=
    (div_le_iff₀ hstep).mp hq_le_succ_k
  constructor
  · change -2 + (k : ℝ) * dyadicGridStep n ≤ x
    linarith
  · change x ≤ -2 + (k : ℝ) * dyadicGridStep n +
      dyadicGridStep n
    nlinarith [hright]

lemma exists_dyadicGridInterval (n : ℕ) {x : ℝ}
    (hxlo : -2 ≤ x) (hxhi : x ≤ 2) :
    ∃ i : Fin (dyadicGridCount n),
      dyadicGridLower n i ≤ x ∧
        x ≤ dyadicGridLower n i + dyadicGridStep n :=
  ⟨dyadicGridCoordinateIndex n x,
    dyadicGridCoordinateIndex_mem n hxlo hxhi⟩

lemma dyadicGridCoordinateIndex_parent (n : ℕ) {x : ℝ}
    (hxlo : -2 ≤ x) (hxhi : x ≤ 2) :
    (dyadicGridCoordinateIndex (n + 1) x).val / 2 =
      (dyadicGridCoordinateIndex n x).val := by
  let N := dyadicGridCount n
  let q : ℝ := (x + 2) / dyadicGridStep n
  have hstep : 0 < dyadicGridStep n := dyadicGridStep_pos n
  have hN : 0 < N := by dsimp [N]; exact dyadicGridCount_pos n
  have hcount : dyadicGridCount (n + 1) = 2 * N := by
    simpa [N] using dyadicGridCount_succ n
  have hstepN : dyadicGridStep n * (N : ℝ) = 4 := by
    simpa [N] using dyadicGridStep_mul_count n
  have hNstep : 4 = (N : ℝ) * dyadicGridStep n := by
    rw [mul_comm]
    exact hstepN.symm
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    exact div_nonneg (by linarith) hstep.le
  have hq_succ :
      (x + 2) / dyadicGridStep (n + 1) = 2 * q := by
    dsimp [q]
    rw [dyadicGridStep_succ]
    field_simp [hstep.ne']
  by_cases hx : x = 2
  · subst x
    have hq_eq : q = (N : ℝ) := by
      dsimp [q]
      rw [div_eq_iff hstep.ne']
      norm_num
      exact hNstep
    have hfloorq : Nat.floor q = N := by
      rw [hq_eq]
      simp
    have hfloor2q : Nat.floor (2 * q) = 2 * N := by
      rw [hq_eq]
      have hcast : (2 : ℝ) * (N : ℝ) = ((2 * N : ℕ) : ℝ) := by
        norm_cast
      rw [hcast]
      exact Nat.floor_natCast (2 * N)
    have hparentVal :
        (dyadicGridCoordinateIndex n 2).val = N - 1 := by
      change min (Nat.floor q) (N - 1) = N - 1
      rw [hfloorq]
      omega
    have hchildVal :
        (dyadicGridCoordinateIndex (n + 1) 2).val = 2 * N - 1 := by
      change min (Nat.floor ((2 + 2) / dyadicGridStep (n + 1)))
        (dyadicGridCount (n + 1) - 1) = 2 * N - 1
      rw [hq_succ, hfloor2q, hcount]
      omega
    rw [hchildVal, hparentVal]
    omega
  · have hxlt : x < 2 := lt_of_le_of_ne hxhi hx
    have hq_lt : q < (N : ℝ) := by
      dsimp [q]
      rw [div_lt_iff₀ hstep]
      calc
        x + 2 < 4 := by linarith
        _ = (N : ℝ) * dyadicGridStep n := hNstep
    have hfloor_lt : Nat.floor q < N :=
      (Nat.floor_lt hq_nonneg).2 hq_lt
    have h2q_nonneg : 0 ≤ 2 * q := by positivity
    have h2q_lt : 2 * q < (2 * N : ℕ) := by
      have hmul := mul_lt_mul_of_pos_left hq_lt (by norm_num : 0 < (2 : ℝ))
      simpa [Nat.cast_mul] using hmul
    have hfloor2_lt : Nat.floor (2 * q) < 2 * N :=
      (Nat.floor_lt h2q_nonneg).2 h2q_lt
    have hparentVal :
        (dyadicGridCoordinateIndex n x).val = Nat.floor q := by
      change min (Nat.floor q) (N - 1) = Nat.floor q
      exact min_eq_left (by omega)
    have hchildVal :
        (dyadicGridCoordinateIndex (n + 1) x).val = Nat.floor (2 * q) := by
      change min (Nat.floor ((x + 2) / dyadicGridStep (n + 1)))
        (dyadicGridCount (n + 1) - 1) = Nat.floor (2 * q)
      rw [hq_succ, hcount]
      exact min_eq_left (by omega)
    rw [hchildVal, hparentVal]
    exact Nat.cast_mul_floor_div_cancel (R := ℝ) (n := 2)
      (by norm_num) q

lemma dyadicGridLower_succ_bounds (n : ℕ)
    (i : Fin (dyadicGridCount n))
    (i' : Fin (dyadicGridCount (n + 1)))
    (hparent : i'.val / 2 = i.val) :
    dyadicGridLower n i ≤ dyadicGridLower (n + 1) i' ∧
      dyadicGridLower (n + 1) i' + dyadicGridStep (n + 1) ≤
        dyadicGridLower n i + dyadicGridStep n := by
  have hval : i'.val = 2 * i.val ∨ i'.val = 2 * i.val + 1 := by omega
  rcases hval with hval | hval
  · simp only [dyadicGridLower, dyadicGridStep_succ, hval, Nat.cast_mul]
    constructor <;> ring_nf <;> linarith [dyadicGridStep_pos n]
  · simp only [dyadicGridLower, dyadicGridStep_succ, hval, Nat.cast_mul,
      Nat.cast_add, Nat.cast_one]
    constructor <;> ring_nf <;> linarith [dyadicGridStep_pos n]

/-- A child grid box lies in the parent box selected by halving both indices. -/
lemma dyadicGridBox_succ_subset (n : ℕ)
    (i j : Fin (dyadicGridCount n))
    (i' j' : Fin (dyadicGridCount (n + 1)))
    (hi : i'.val / 2 = i.val) (hj : j'.val / 2 = j.val) :
    dyadicGridBox (n + 1) i' j' ⊆ dyadicGridBox n i j := by
  obtain ⟨hirl, hiru⟩ := dyadicGridLower_succ_bounds n i i' hi
  obtain ⟨hirlm, hirum⟩ := dyadicGridLower_succ_bounds n j j' hj
  intro z hz
  rcases hz with ⟨hzrl, hzru, hzim, hziu⟩
  exact ⟨hirl.trans hzrl, hzru.trans hiru, hirlm.trans hzim,
    hziu.trans hirum⟩

/-- Every point of the universal parameter disk belongs to a grid box. -/
lemma exists_mem_dyadicGridBox (n : ℕ) {z : ℂ} (hz : ‖z‖ ≤ 2) :
    ∃ i j : Fin (dyadicGridCount n), z ∈ dyadicGridBox n i j := by
  have hre := abs_le.mp ((Complex.abs_re_le_norm z).trans hz)
  have him := abs_le.mp ((Complex.abs_im_le_norm z).trans hz)
  obtain ⟨i, hrei, hreu⟩ := exists_dyadicGridInterval n hre.1 hre.2
  obtain ⟨j, himi, himu⟩ := exists_dyadicGridInterval n him.1 him.2
  exact ⟨i, j, hrei, hreu, himi, himu⟩

/-- Two points in one grid box are at most twice its side length apart in the
complex metric. -/
lemma dist_le_dyadicGridBox (n : ℕ) (i j : Fin (dyadicGridCount n))
    {x y : ℂ} (hx : x ∈ dyadicGridBox n i j)
    (hy : y ∈ dyadicGridBox n i j) :
    dist x y ≤ 8 * dyadicRadius n := by
  rcases hx with ⟨hxl, hxu, hxi, hxiu⟩
  rcases hy with ⟨hyl, hyu, hyi, hyiu⟩
  have hre : |x.re - y.re| ≤ dyadicGridStep n := by
    apply abs_le.mpr
    constructor <;> linarith
  have him : |x.im - y.im| ≤ dyadicGridStep n := by
    apply abs_le.mpr
    constructor <;> linarith
  have hre' : |(x - y).re| ≤ dyadicGridStep n := by
    simpa only [Complex.sub_re] using hre
  have him' : |(x - y).im| ≤ dyadicGridStep n := by
    simpa only [Complex.sub_im] using him
  calc
    dist x y = ‖x - y‖ := dist_eq_norm x y
    _ ≤ |(x - y).re| + |(x - y).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ ≤ dyadicGridStep n + dyadicGridStep n := add_le_add hre' him'
    _ = 8 * dyadicRadius n := by
      rw [dyadicGridStep_eq_four_radius]
      ring

/-- A finite family of compact cells selected from the exact finite-orbit
    outer stages. Empty cells are allowed; an address records separately
    that each of its chosen cells is nonempty. -/
structure FiniteCellOuterApproximation where
  index : ℕ → Type
  finite_index : ∀ n, Finite (index n)
  cell : ∀ n, index n → Set ℂ
  cell_compact : ∀ n i, IsCompact (cell n i)
  stage_antitone :
    ∀ {n m}, n ≤ m →
      (⋃ i, cell m i) ⊆ (⋃ i, cell n i)
  mandelbrot_subset_stage :
    ∀ n, MLC.Categorical.Mandelbrot.set ⊆ ⋃ i, cell n i
  cell_near_outer :
    ∀ n i x, x ∈ cell n i →
      ∃ y ∈ MLC.Categorical.Mandelbrot.outerOrbitSet n,
        dist x y ≤ dyadicRadius n

def stage (A : FiniteCellOuterApproximation) (n : ℕ) : Set ℂ :=
  ⋃ i, A.cell n i

theorem stage_antitone (A : FiniteCellOuterApproximation)
    {n m : ℕ} (h : n ≤ m) :
    stage A m ⊆ stage A n :=
  A.stage_antitone h

theorem mandelbrot_subset_stage (A : FiniteCellOuterApproximation) (n : ℕ) :
    MLC.Categorical.Mandelbrot.set ⊆ stage A n :=
  A.mandelbrot_subset_stage n

theorem isCompact_stage (A : FiniteCellOuterApproximation) (n : ℕ) :
    IsCompact (stage A n) := by
  letI := A.finite_index n
  exact isCompact_iUnion (fun i => A.cell_compact n i)

theorem stage_subset_outerNeighborhood (A : FiniteCellOuterApproximation)
    (n : ℕ) :
    stage A n ⊆
      {x | ∃ y ∈ MLC.Categorical.Mandelbrot.outerOrbitSet n,
        dist x y ≤ dyadicRadius n} := by
  intro x hx
  rcases mem_iUnion.mp hx with ⟨i, hxi⟩
  exact A.cell_near_outer n i x hxi

theorem iInter_stage_eq_mandelbrot (A : FiniteCellOuterApproximation) :
    (⋂ n, stage A n) = MLC.Categorical.Mandelbrot.set := by
  apply Subset.antisymm
  · intro x hx
    rw [← MLC.Categorical.Mandelbrot.iInter_outerOrbitSet_eq_set]
    refine mem_iInter.mpr ?_
    intro k
    apply (MLC.Categorical.Mandelbrot.isClosed_outerOrbitSet k).closure_subset
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨m, hm⟩ := exists_dyadicRadius_lt hε
    let n := max k m
    have hkn : k ≤ n := Nat.le_max_left _ _
    have hmn : m ≤ n := Nat.le_max_right _ _
    have hpow : dyadicRadius n ≤ dyadicRadius m := by
      dsimp [dyadicRadius]
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hmn
    have hradius : dyadicRadius n < ε := lt_of_le_of_lt hpow hm
    have hxn : x ∈ stage A n := mem_iInter.mp hx n
    rcases mem_iUnion.mp hxn with ⟨i, hxi⟩
    obtain ⟨y, hy, hxy⟩ := A.cell_near_outer n i x hxi
    refine ⟨y, ?_, ?_⟩
    · exact MLC.Categorical.Mandelbrot.outerOrbitSet_antitone hkn hy
    · exact lt_of_le_of_lt hxy hradius
  · exact subset_iInter (fun n => mandelbrot_subset_stage A n)

theorem stage_nested_compact (A : FiniteCellOuterApproximation) :
    (∀ n, IsCompact (stage A n)) ∧
      (∀ {n m}, n ≤ m → stage A m ⊆ stage A n) := by
  exact ⟨isCompact_stage A, A.stage_antitone⟩

/-! ## A verified baseline instance

The one-cell instance below is intentionally not a fine combinatorial
discretization: it records the exact finite-orbit outer stages already present
in the repository.  Any cubical or CAD implementation can be compared with
this baseline by proving the same certificate fields. -/

def exactOrbitOuterApproximation :
    FiniteCellOuterApproximation where
  index := fun _ => Unit
  finite_index := fun _ => inferInstance
  cell := fun n _ => MLC.Categorical.Mandelbrot.outerOrbitSet n
  cell_compact := by
    intro n _
    exact MLC.Categorical.Mandelbrot.isCompact_outerOrbitSet n
  stage_antitone := by
    intro n m h x hx
    rcases mem_iUnion.mp hx with ⟨i, hxi⟩
    exact mem_iUnion.mpr ⟨i, MLC.Categorical.Mandelbrot.outerOrbitSet_antitone h hxi⟩
  mandelbrot_subset_stage := by
    intro n x hx
    exact mem_iUnion.mpr ⟨(), MLC.Categorical.Mandelbrot.set_subset_outerOrbitSet n hx⟩
  cell_near_outer := by
    intro n _ x hx
    exact ⟨x, hx, by
      simp
      exact (dyadicRadius_pos n).le⟩

@[simp] theorem stage_exactOrbitOuterApproximation (n : ℕ) :
    stage exactOrbitOuterApproximation n =
      MLC.Categorical.Mandelbrot.outerOrbitSet n := by
  ext x
  constructor
  · intro hx
    rcases mem_iUnion.mp hx with ⟨i, hxi⟩
    simpa using hxi
  · intro hx
    exact mem_iUnion.mpr ⟨(), hx⟩

/-- A finite dyadic partition of each finite-orbit outer stage. The index set
is the full finite grid; cells not meeting the outer stage are empty. -/
def dyadicGridOuterApproximation : FiniteCellOuterApproximation where
  index := fun n => Fin (dyadicGridCount n) × Fin (dyadicGridCount n)
  finite_index := fun _ => inferInstance
  cell := fun n ij =>
    MLC.Categorical.Mandelbrot.outerOrbitSet n ∩
      dyadicGridBox n ij.1 ij.2
  cell_compact := by
    intro n ij
    exact (MLC.Categorical.Mandelbrot.isCompact_outerOrbitSet n).inter_right
      (isClosed_dyadicGridBox n ij.1 ij.2)
  stage_antitone := by
    intro n m h z hz
    rcases mem_iUnion.mp hz with ⟨ij, hij⟩
    change z ∈ MLC.Categorical.Mandelbrot.outerOrbitSet m ∩
      dyadicGridBox m ij.1 ij.2 at hij
    have houter :=
      MLC.Categorical.Mandelbrot.outerOrbitSet_antitone h hij.1
    obtain ⟨i, j, hbox⟩ := exists_mem_dyadicGridBox n houter.1
    exact mem_iUnion.mpr ⟨(i, j), ⟨houter, hbox⟩⟩
  mandelbrot_subset_stage := by
    intro n z hz
    have houter :=
      MLC.Categorical.Mandelbrot.set_subset_outerOrbitSet n hz
    obtain ⟨i, j, hbox⟩ := exists_mem_dyadicGridBox n houter.1
    exact mem_iUnion.mpr ⟨(i, j), ⟨houter, hbox⟩⟩
  cell_near_outer := by
    intro n ij x hx
    exact ⟨x, hx.1, by simpa using (dyadicRadius_pos n).le⟩

@[simp] theorem stage_dyadicGridOuterApproximation (n : ℕ) :
    stage dyadicGridOuterApproximation n =
      MLC.Categorical.Mandelbrot.outerOrbitSet n := by
  ext z
  constructor
  · intro hz
    rcases mem_iUnion.mp hz with ⟨ij, hij⟩
    change z ∈ MLC.Categorical.Mandelbrot.outerOrbitSet n ∩
      dyadicGridBox n ij.1 ij.2 at hij
    exact hij.1
  · intro hz
    obtain ⟨i, j, hbox⟩ :=
      exists_mem_dyadicGridBox n (by exact hz.1)
    exact mem_iUnion.mpr ⟨(i, j), ⟨hz, hbox⟩⟩

end
end CertifiedOrbit
end MLC
