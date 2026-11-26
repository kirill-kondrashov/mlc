import Mathlib.Data.Nat.Notation
import Mathlib.Data.Int.Notation

/-!
# Computational part of the grid certificate

Fixed-point first-order models of the critical orbit, the certificates that a
dyadic square lies outside or inside the Mandelbrot set, and the verification of
a stream of hints that selects the certificates. This module uses only core
`Nat`, `Int` and `List` operations, so that the generated tile modules, which
evaluate it by kernel reduction, load quickly and use little memory. The
soundness proofs are in `Mlc.GridCertificate` and `Mlc.GridTMCertificate`.
-/

namespace MLC.Certified

/-- The fixed-point scale `2^48`. -/
def SN : ℕ := 281474976710656

/-- A critical-orbit enclosure in fixed-point units: the disk of radius `R`
around `a + b i`. -/
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

/-- The enclosure lies strictly outside the closed disk of radius `2 + ρ`. -/
def escaped (m : Ball) : Bool :=
  decide ((2 * SN + m.R) ^ 2 < m.a.natAbs ^ 2 + m.b.natAbs ^ 2)

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

/-! ### Taylor models and certificates with hints

A critical-orbit enclosure of the second kind keeps the iterate to first order
in the parameter: for every `c` in the parameter disk of radius `rc / 2^48`
around the center `c₀`, the iterate `z_n(c)` lies within `e / 2^48` of
`m + d (c - c₀)`, where `m = (mx + my i) / 2^48` and `d = (dx + dy i) / 2^48`.
The model follows the phases of the derivative, so it is much sharper than a
disk (`Ball`) after many steps. A square is certified by a natural number, its
hint, that the search program found; the kernel only verifies the hint. -/

/-- First-order model of a critical iterate over a parameter disk. -/
structure TBall where
  mx : ℤ
  my : ℤ
  dx : ℤ
  dy : ℤ
  e : ℕ

/-- The model of the zeroth iterate. -/
def TBall.zero : TBall := ⟨0, 0, 0, 0, 0⟩

/-- Radius of a disk around `m` enclosing the model over the parameter disk
of radius `rc`, rounded up. -/
def TBall.rho (rc : ℕ) (t : TBall) : ℕ := (normUB t.dx t.dy * rc + (SN - 1)) / SN + t.e

/-- The model seen as a disk enclosure. -/
def TBall.toBall (rc : ℕ) (t : TBall) : Ball := ⟨t.mx, t.my, t.rho rc⟩

/-- One step `z ↦ z² + c` of the model. The new derivative is `2 m d + 1`; the
remainder collects the second-order terms and the rounding errors. -/
def tmStep (ca cb : ℤ) (rc : ℕ) (t : TBall) : TBall where
  mx := (t.mx * t.mx - t.my * t.my) / (SN : ℤ) + ca
  my := (2 * t.mx * t.my) / (SN : ℤ) + cb
  dx := (2 * (t.mx * t.dx - t.my * t.dy)) / (SN : ℤ) + SN
  dy := (2 * (t.mx * t.dy + t.my * t.dx)) / (SN : ℤ)
  e := (t.rho rc * t.rho rc + 2 * normUB t.mx t.my * t.e + (SN - 1)) / SN + 2 +
    (2 * rc + (SN - 1)) / SN

/-- `n` steps of the model. -/
def tmIter (ca cb : ℤ) (rc : ℕ) : ℕ → TBall → TBall
  | 0, t => t
  | n + 1, t => tmIter ca cb rc n (tmStep ca cb rc t)

/-- Closure test of a moving disk: with remainder `e'` instead of `t.e`, the
model returns into itself after `p` steps. -/
def closes (ca cb : ℤ) (rc : ℕ) (t : TBall) (p e' : ℕ) : Bool :=
  let tp := tmIter ca cb rc p { t with e := e' }
  decide (normUB (tp.mx - t.mx) (tp.my - t.my) +
      (normUB (tp.dx - t.dx) (tp.dy - t.dy) * rc + (SN - 1)) / SN + tp.e ≤ e')

/-- Number of candidate remainders of an inside certificate. -/
def ladderLen : ℕ := 40

/-- Number of candidate periods of an inside certificate. -/
def periodLen : ℕ := 8

/-- Outside certificate: after `n` steps the model lies outside the disk of radius `2`. -/
def Sq.checkOut (q : Sq) (n : ℕ) : Bool :=
  decide (q.k ≤ 47) && escaped ((tmIter q.ca q.cb q.rc n TBall.zero).toBall q.rc)

/-- Inside certificate `(n, p, j)`: after `n` steps the moving disk of radius
`e + (rc / 4 + 1) 2^j` returns into itself after `p + 1` steps. -/
def Sq.checkIn (q : Sq) (n p j : ℕ) : Bool :=
  decide (q.k ≤ 47) &&
    (let t := tmIter q.ca q.cb q.rc n TBall.zero
     closes q.ca q.cb q.rc t (p + 1) (t.e + (q.rc / 4 + 1) * 2 ^ j))

/-- Verification of a hint `h ≥ 2`: `1` if the square is certified outside `M`,
`2` if certified inside `M`, `0` if the hint is not a valid certificate. An even
hint `2 n + 2` is an outside certificate with `n` steps; an odd hint `2 v + 3`
with `v = (n * periodLen + p) * ladderLen + j` is an inside certificate. -/
def Sq.certify (q : Sq) (h : ℕ) : ℕ :=
  if h % 2 = 0 then (if q.checkOut (h / 2 - 1) then 1 else 0)
  else if q.checkIn ((h / 2 - 1) / ladderLen / periodLen) ((h / 2 - 1) / ladderLen % periodLen)
      ((h / 2 - 1) % ladderLen) then 2 else 0

/-- Number of unresolved finest cells (`f` levels below `q`) according to a
stream of hints, and the unused hints. The hint `0` leaves a square unresolved,
`1` splits it into four squares, and a hint `h ≥ 2` is a certificate. A missing
or invalid hint leaves the square unresolved, so the count is always an upper
bound; it is exact for the stream written by the search program. -/
def verifyTree : ℕ → Sq → List ℕ → ℕ × List ℕ
  | f, _, [] => (4 ^ f, [])
  | 0, q, h :: hs =>
      if h = 0 then (1, hs) else if h = 1 then (1, hs)
      else if q.certify h = 0 then (1, hs) else (0, hs)
  | f + 1, q, h :: hs =>
      if h = 0 then (4 ^ (f + 1), hs)
      else if h = 1 then
        let r0 := verifyTree f q.c00 hs
        let r1 := verifyTree f q.c10 r0.2
        let r2 := verifyTree f q.c01 r1.2
        let r3 := verifyTree f q.c11 r2.2
        (r0.1 + r1.1 + r2.1 + r3.1, r3.2)
      else if q.certify h = 0 then (4 ^ (f + 1), hs) else (0, hs)

/-- Unresolved finest cells below the square `q` for the stream `hs`. -/
def cellsH (F : ℕ) (q : Sq) (hs : List ℕ) : ℕ := (verifyTree F q hs).1

/-- Walk over the squares of `L` in the order of a depth-first traversal: `r` is
covered if its first square is `r`, or if its four children are covered in turn.
The result is the list of the squares that are left. -/
def coverWalk : ℕ → Sq → List Sq → Option (List Sq)
  | _, _, [] => none
  | 0, r, s :: L => if s = r then some L else none
  | f + 1, r, s :: L =>
      if s = r then some L
      else
        match coverWalk f r.c00 (s :: L) with
        | none => none
        | some L1 =>
          match coverWalk f r.c10 L1 with
          | none => none
          | some L2 =>
            match coverWalk f r.c01 L2 with
            | none => none
            | some L3 => coverWalk f r.c11 L3

/-- The squares of `L` cover the squares `rs`, one after the other. -/
def coverAll (f : ℕ) : List Sq → List Sq → Bool
  | [], _ => true
  | r :: rs, L =>
      match coverWalk f r L with
      | none => false
      | some L' => coverAll f rs L'

/-- The 512 squares of side `1/8` covering `[-2, 2] × [0, 2]`. -/
def rootsUp : List Sq :=
  ((List.range 32).map fun (i : ℕ) => (i : ℤ) - 16).flatMap fun x =>
    ((List.range 16).map fun (j : ℕ) => (j : ℤ)).map fun y => (⟨x, y, 3⟩ : Sq)

end MLC.Certified
