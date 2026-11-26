import Mathlib.Data.Nat.Notation
import Mathlib.Data.Int.Notation

/-!
# Computational part of the grid certificate

Fixed-point critical-orbit enclosures, the trapping scan, the classifier of
dyadic squares and the subdivision count. This module uses only core `Nat`,
`Int` and `List` operations, so that the generated tile modules, which evaluate
it by kernel reduction, load quickly and use little memory. The soundness
proofs are in `Mlc.GridCertificate`.
-/

namespace MLC.Certified

/-- The fixed-point scale `2^48`. -/
def SN : ℕ := 281474976710656

/-- A critical-orbit enclosure in fixed-point units. -/
structure Ball where
  a : ℤ
  b : ℤ
  R : ℕ

/-- One Newton step for an integer square root bound. -/
def newtonStep (S x : ℕ) : ℕ := (x + (S + x - 1) / x + 1) / 2

/-- The Newton candidate is used only when it passes the squaring test. -/
def normPick (S x3 x0 : ℕ) : ℕ := if S ≤ x3 * x3 then x3 else x0

def normAux (S x0 : ℕ) : ℕ :=
  normPick S (newtonStep S (newtonStep S (newtonStep S x0))) x0

/-- A natural bound `N` with `a² + b² ≤ N²`; the final test makes the
bound independent of the Newton iteration. -/
def normUB (a b : ℤ) : ℕ :=
  normAux (a.natAbs * a.natAbs + b.natAbs * b.natAbs) (a.natAbs + b.natAbs)

/-- The enclosure radius after one step, rounded outward. -/
def stepR (rc : ℕ) (m : Ball) (R : ℕ) : ℕ :=
  (R * (R + 2 * normUB m.a m.b) + (SN - 1)) / SN + rc + 2

/-- One step `z ↦ z² + c₀` on an enclosure, with outward rounding. -/
def stepBall (ca cb : ℤ) (rc : ℕ) (m : Ball) : Ball where
  a := (m.a * m.a - m.b * m.b) / (SN : ℤ) + ca
  b := (2 * m.a * m.b) / (SN : ℤ) + cb
  R := stepR rc m m.R

/-- The enclosure lies strictly outside the closed disk of radius `2 + ρ`. -/
def escaped (m : Ball) : Bool :=
  decide ((2 * SN + m.R) ^ 2 < m.a.natAbs ^ 2 + m.b.natAbs ^ 2)

/-- Scan for a period `p ≤ n` whose image disk returns into the disk of radius
`Rhat` around the base center `m0`. -/
def trapScan (ca cb : ℤ) (rc : ℕ) (m0 : Ball) (Rhat : ℕ) : ℕ → Ball → ℕ → Bool
  | 0, _, _ => false
  | n + 1, m, rhat =>
      if normUB ((stepBall ca cb rc m).a - m0.a) ((stepBall ca cb rc m).b - m0.b) +
          stepR rc m rhat ≤ Rhat then true
      else if 8 * SN < stepR rc m rhat then false
      else trapScan ca cb rc m0 Rhat n (stepBall ca cb rc m) (stepR rc m rhat)

/-- Trapping certificate at an orbit enclosure. -/
def trapTest (ca cb : ℤ) (rc pmax : ℕ) (m : Ball) : Bool :=
  trapScan ca cb rc m (3 * m.R / 2) pmax m (3 * m.R / 2)

/-- Classification of the critical orbit enclosure: `1` outside `M`, `2` inside `M`,
`0` unresolved. -/
def classifyLoop (ca cb : ℤ) (rc pmax : ℕ) : ℕ → Ball → ℕ
  | 0, m =>
      if escaped m then 1
      else if 8 * SN < m.R then 0
      else if trapTest ca cb rc pmax m then 2 else 0
  | n + 1, m =>
      if escaped m then 1
      else if 8 * SN < m.R then 0
      else classifyLoop ca cb rc pmax n (stepBall ca cb rc m)

/-- A closed dyadic square of side `2^(-k)` with lower-left corner
`(x, y) / 2^k`. -/
structure Sq where
  x : ℤ
  y : ℤ
  k : ℕ
  deriving DecidableEq

/-- Fixed-point real part of the center, valid for `k ≤ 47`. -/
def Sq.ca (q : Sq) : ℤ := (2 * q.x + 1) * ((2 ^ (47 - q.k) : ℕ) : ℤ)

/-- Fixed-point imaginary part of the center, valid for `k ≤ 47`. -/
def Sq.cb (q : Sq) : ℤ := (2 * q.y + 1) * ((2 ^ (47 - q.k) : ℕ) : ℤ)

/-- Fixed-point radius of a disk containing the square, valid for `k ≤ 47`. -/
def Sq.rc (q : Sq) : ℕ := (2 ^ (47 - q.k) * 363 + 255) / 256

def Sq.c00 (q : Sq) : Sq := ⟨2 * q.x, 2 * q.y, q.k + 1⟩
def Sq.c10 (q : Sq) : Sq := ⟨2 * q.x + 1, 2 * q.y, q.k + 1⟩
def Sq.c01 (q : Sq) : Sq := ⟨2 * q.x, 2 * q.y + 1, q.k + 1⟩
def Sq.c11 (q : Sq) : Sq := ⟨2 * q.x + 1, 2 * q.y + 1, q.k + 1⟩

/-- Classification of a dyadic square. -/
def Sq.cls (q : Sq) (pmax J : ℕ) : ℕ :=
  if q.k ≤ 47 then classifyLoop q.ca q.cb q.rc pmax J ⟨0, 0, 0⟩ else 0

/-- The square is certified to lie outside `M` or inside `M`. -/
def Sq.resolved (q : Sq) (pmax J : ℕ) : Bool :=
  decide (q.cls pmax J = 1 ∨ q.cls pmax J = 2)

/-- Number of finest cells (after `f` further subdivisions) that the
certificate leaves unresolved. -/
def cells (pmax J : ℕ) : ℕ → Sq → ℕ
  | 0, q => if q.resolved pmax J then 0 else 1
  | f + 1, q =>
      if q.resolved pmax J then 0
      else cells pmax J f q.c00 + cells pmax J f q.c10 + cells pmax J f q.c01 +
        cells pmax J f q.c11

/-- The 512 squares of side `1/8` covering `[-2, 2] × [0, 2]`. -/
def rootsUp : List Sq :=
  ((List.range 32).map fun (i : ℕ) => (i : ℤ) - 16).flatMap fun x =>
    ((List.range 16).map fun (j : ℕ) => (j : ℤ)).map fun y => (⟨x, y, 3⟩ : Sq)

/-- Unresolved cells over the upper root squares, `f` levels below side `1/8`. -/
def rootCellsUp (pmax J f : ℕ) : ℕ := (rootsUp.map (cells pmax J f)).sum

end MLC.Certified
