/-!
Lists the squares of an older, classifier-based grid (upper half-plane; the map
mirrors them): `I x y k` for squares certified inside the Mandelbrot set and
`U x y k` for the unresolved finest cells. The square `(x, y, k)` is
`[x / 2^k, (x + 1) / 2^k] × [y / 2^k, (y + 1) / 2^k]`.

The arguments `pmax J fuel` select the parameters of the commit. The first
commits of the grid certified squares with disk balls and a fixed trapping
disk; the progress report reproduces their regions with this program (a copy of
that classifier, independent of the current library) after comparing the number
of `U` lines with the cell count recorded by the commit. Later grids store
their certificates as hint streams in `Mlc/GridTiles` and are read from there.
-/

def SN : Nat := 281474976710656

structure Ball where
  a : Int
  b : Int
  R : Nat

def newtonStep (S x : Nat) : Nat := (x + (S + x - 1) / x + 1) / 2

def normPick (S x3 x0 : Nat) : Nat := if S ≤ x3 * x3 then x3 else x0

def normAux (S x0 : Nat) : Nat :=
  normPick S (newtonStep S (newtonStep S (newtonStep S x0))) x0

def normUB (a b : Int) : Nat :=
  normAux (a.natAbs * a.natAbs + b.natAbs * b.natAbs) (a.natAbs + b.natAbs)

def stepR (rc : Nat) (m : Ball) (R : Nat) : Nat :=
  (R * (R + 2 * normUB m.a m.b) + (SN - 1)) / SN + rc + 2

def stepBall (ca cb : Int) (rc : Nat) (m : Ball) : Ball where
  a := (m.a * m.a - m.b * m.b) / (SN : Int) + ca
  b := (2 * m.a * m.b) / (SN : Int) + cb
  R := stepR rc m m.R

def escaped (m : Ball) : Bool :=
  decide ((2 * SN + m.R) ^ 2 < m.a.natAbs ^ 2 + m.b.natAbs ^ 2)

def trapScan (ca cb : Int) (rc : Nat) (m0 : Ball) (Rhat : Nat) : Nat → Ball → Nat → Bool
  | 0, _, _ => false
  | n + 1, m, rhat =>
      if normUB ((stepBall ca cb rc m).a - m0.a) ((stepBall ca cb rc m).b - m0.b) +
          stepR rc m rhat ≤ Rhat then true
      else if 8 * SN < stepR rc m rhat then false
      else trapScan ca cb rc m0 Rhat n (stepBall ca cb rc m) (stepR rc m rhat)

def trapTest (ca cb : Int) (rc pmax : Nat) (m : Ball) : Bool :=
  trapScan ca cb rc m (3 * m.R / 2) pmax m (3 * m.R / 2)

/-- `1` outside `M`, `2` inside `M`, `0` unresolved. -/
def classifyLoop (ca cb : Int) (rc pmax : Nat) : Nat → Ball → Nat
  | 0, m =>
      if escaped m then 1
      else if 8 * SN < m.R then 0
      else if trapTest ca cb rc pmax m then 2 else 0
  | n + 1, m =>
      if escaped m then 1
      else if 8 * SN < m.R then 0
      else classifyLoop ca cb rc pmax n (stepBall ca cb rc m)

structure Sq where
  x : Int
  y : Int
  k : Nat

def Sq.ca (q : Sq) : Int := (2 * q.x + 1) * ((2 ^ (47 - q.k) : Nat) : Int)
def Sq.cb (q : Sq) : Int := (2 * q.y + 1) * ((2 ^ (47 - q.k) : Nat) : Int)
def Sq.rc (q : Sq) : Nat := (2 ^ (47 - q.k) * 363 + 255) / 256

def Sq.c00 (q : Sq) : Sq := ⟨2 * q.x, 2 * q.y, q.k + 1⟩
def Sq.c10 (q : Sq) : Sq := ⟨2 * q.x + 1, 2 * q.y, q.k + 1⟩
def Sq.c01 (q : Sq) : Sq := ⟨2 * q.x, 2 * q.y + 1, q.k + 1⟩
def Sq.c11 (q : Sq) : Sq := ⟨2 * q.x + 1, 2 * q.y + 1, q.k + 1⟩

def Sq.cls (q : Sq) (pmax J : Nat) : Nat :=
  if q.k ≤ 47 then classifyLoop q.ca q.cb q.rc pmax J ⟨0, 0, 0⟩ else 0

/-- The 512 squares of side `1/8` covering `[-2, 2] × [0, 2]`. -/
def rootsUp : List Sq :=
  ((List.range 32).map fun (i : Nat) => (i : Int) - 16).flatMap fun x =>
    ((List.range 16).map fun (j : Nat) => (j : Int)).map fun y => (⟨x, y, 3⟩ : Sq)

def collect (pmax J : Nat) : Nat → Sq → List (Char × Sq)
  | 0, q =>
      let c := q.cls pmax J
      if c = 2 then [('I', q)] else if c = 1 then [] else [('U', q)]
  | f + 1, q =>
      let c := q.cls pmax J
      if c = 2 then [('I', q)]
      else if c = 1 then []
      else
        collect pmax J f q.c00 ++ collect pmax J f q.c10 ++
          collect pmax J f q.c01 ++ collect pmax J f q.c11

def main (args : List String) : IO UInt32 := do
  match args.map String.toNat? with
  | [some pmax, some J, some fuel] =>
      for q in rootsUp do
        for (tag, s) in collect pmax J fuel q do
          IO.println s!"{tag} {s.x} {s.y} {s.k}"
      return 0
  | _ =>
      IO.eprintln "usage: export_grid_regions pmax J fuel"
      return 1
