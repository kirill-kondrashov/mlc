import Mlc.CategoricalMandelbrot
import Molecule.Mol

/-!
# Exhaustive parameter-classification interfaces

The exterior part is proved from the escape-radius identity.  The interior
and boundary predicates are recorded as a disjoint priority partition, with
the residual class retained explicitly.  This is a classification of cases,
not a claim that any of the predicates are decidable or that the residual
class is empty.
-/

namespace MLC
namespace ParameterClassification

open Set

noncomputable section

abbrev mandelbrotSet : Set ℂ :=
  MLC.Quadratic.MandelbrotSet

def escapeAt (c : ℂ) (n : ℕ) : Prop :=
  ‖MLC.Quadratic.orbit c 0 n‖ > (2 : ℝ)

def firstEscapeAt (c : ℂ) (n : ℕ) : Prop :=
  escapeAt c n ∧ ∀ m < n, ¬ escapeAt c m

theorem not_mem_mandelbrot_iff_exists_escape (c : ℂ) :
    c ∉ mandelbrotSet ↔ ∃ n, escapeAt c n := by
  change c ∉ MLC.Quadratic.MandelbrotSet ↔ ∃ n, escapeAt c n
  rw [Molecule.mandelbrot_eq_inter]
  simp [escapeAt, not_forall]

theorem exists_firstEscape_of_not_mem {c : ℂ}
    (hc : c ∉ mandelbrotSet) :
    ∃ n, firstEscapeAt c n := by
  classical
  obtain ⟨n, hn⟩ := (not_mem_mandelbrot_iff_exists_escape c).mp hc
  let k := Nat.find ⟨n, hn⟩
  refine ⟨k, Nat.find_spec ⟨n, hn⟩, ?_⟩
  intro m hm
  exact Nat.find_min ⟨n, hn⟩ hm

theorem firstEscape_excludes_mandelbrot {c n}
    (h : firstEscapeAt c n) :
    c ∉ mandelbrotSet :=
  (not_mem_mandelbrot_iff_exists_escape c).mpr ⟨n, h.1⟩

def HasAttractingCycle (c : ℂ) : Prop :=
  Molecule.HasAttractingPeriodicOrbit c

def PeriodicPoint (c : ℂ) (p : ℕ) (z : ℂ) : Prop :=
  0 < p ∧ (MLC.Quadratic.fc c)^[p] z = z

def multiplier (c : ℂ) (p : ℕ) (z : ℂ) : ℂ :=
  deriv ((MLC.Quadratic.fc c)^[p]) z

def HasParabolicCycle (c : ℂ) : Prop :=
  ∃ p : ℕ, ∃ z : ℂ, PeriodicPoint c p z ∧
    ∃ q : ℕ, 0 < q ∧ multiplier c p z ^ q = 1

/- A local analytic linearization certificate.  The injectivity condition is
   included explicitly, so this is a finite theorem interface rather than an
   informal reference to a germ. -/
structure LocalLinearization (c : ℂ) (p : ℕ) (z : ℂ) where
  radius : ℝ
  radius_pos : 0 < radius
  map : ℂ → ℂ
  map_zero : map 0 = z
  analytic_at_zero : AnalyticAt ℂ map 0
  derivative_ne_zero : deriv map 0 ≠ 0
  inj_on : Set.InjOn map (Metric.ball 0 radius)
  conjugacy :
    ∀ w ∈ Metric.ball (0 : ℂ) radius,
      (MLC.Quadratic.fc c)^[p] (map w) =
        map (multiplier c p z * w)

def HasSiegelCycle (c : ℂ) : Prop :=
  ∃ p : ℕ, ∃ z : ℂ, PeriodicPoint c p z ∧
    ‖multiplier c p z‖ = 1 ∧
      (∀ q : ℕ, 0 < q → multiplier c p z ^ q ≠ 1) ∧
        Nonempty (LocalLinearization c p z)

def HasCremerCycle (c : ℂ) : Prop :=
  ∃ p : ℕ, ∃ z : ℂ, PeriodicPoint c p z ∧
    ‖multiplier c p z‖ = 1 ∧
      (∀ q : ℕ, 0 < q → multiplier c p z ^ q ≠ 1) ∧
        ¬ Nonempty (LocalLinearization c p z)

def EventuallyPeriodicCriticalOrbit (c : ℂ) : Prop :=
  ∃ a b : ℕ, 0 < b ∧
    MLC.Quadratic.orbit c 0 (a + b) =
      MLC.Quadratic.orbit c 0 a

def ClassAttracting (c : ℂ) : Prop :=
  HasAttractingCycle c

def ClassParabolic (c : ℂ) : Prop :=
  ¬ ClassAttracting c ∧ HasParabolicCycle c

def ClassSiegel (c : ℂ) : Prop :=
  ¬ ClassAttracting c ∧ ¬ HasParabolicCycle c ∧ HasSiegelCycle c

def ClassCremer (c : ℂ) : Prop :=
  ¬ ClassAttracting c ∧ ¬ HasParabolicCycle c ∧
    ¬ HasSiegelCycle c ∧ HasCremerCycle c

def ClassEventuallyPeriodic (c : ℂ) : Prop :=
  ¬ ClassAttracting c ∧ ¬ HasParabolicCycle c ∧
    ¬ HasSiegelCycle c ∧ ¬ HasCremerCycle c ∧
    EventuallyPeriodicCriticalOrbit c

def ClassResidual (c : ℂ) : Prop :=
  ¬ ClassAttracting c ∧ ¬ HasParabolicCycle c ∧
    ¬ HasSiegelCycle c ∧ ¬ HasCremerCycle c ∧
    ¬ EventuallyPeriodicCriticalOrbit c

theorem classification_complete (c : ℂ) :
    ClassAttracting c ∨ ClassParabolic c ∨ ClassSiegel c ∨
      ClassCremer c ∨ ClassEventuallyPeriodic c ∨ ClassResidual c := by
  by_cases hA : ClassAttracting c
  · exact Or.inl hA
  · by_cases hP : HasParabolicCycle c
    · right
      left
      exact ⟨hA, hP⟩
    · by_cases hS : HasSiegelCycle c
      · right
        right
        left
        exact ⟨hA, hP, hS⟩
      · by_cases hC : HasCremerCycle c
        · right
          right
          right
          left
          exact ⟨hA, hP, hS, hC⟩
        · by_cases hF : EventuallyPeriodicCriticalOrbit c
          · right
            right
            right
            right
            left
            exact ⟨hA, hP, hS, hC, hF⟩
          · right
            right
            right
            right
            right
            exact ⟨hA, hP, hS, hC, hF⟩

theorem classification_complete_on_mandelbrot (c : ℂ) (_hc : c ∈ mandelbrotSet) :
    c ∈ {z | ClassAttracting z} ∨
      c ∈ {z | ClassParabolic z} ∨
      c ∈ {z | ClassSiegel z} ∨
      c ∈ {z | ClassCremer z} ∨
      c ∈ {z | ClassEventuallyPeriodic z} ∨
      c ∈ {z | ClassResidual z} := by
  simpa only [mem_setOf_eq] using classification_complete c

theorem residual_class_is_retained :
    ∀ c : ℂ, ClassResidual c ∨
      ClassAttracting c ∨ ClassParabolic c ∨ ClassSiegel c ∨
      ClassCremer c ∨ ClassEventuallyPeriodic c := by
  intro c
  rcases classification_complete c with h | h | h | h | h | h
  · right
    left
    exact h
  · right
    right
    left
    exact h
  · right
    right
    right
    left
    exact h
  · right
    right
    right
    right
    left
    exact h
  · right
    right
    right
    right
    right
    exact h
  · left
    exact h

end
end ParameterClassification
end MLC
