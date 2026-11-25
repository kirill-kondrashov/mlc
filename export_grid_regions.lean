import Mlc.GridCertified
import Mlc.GridParams

/-!
Lists the squares of the checked grid (upper half-plane; the map mirrors them): `I x y k` for squares certified inside
the Mandelbrot set and `U x y k` for the unresolved finest cells. The square
`(x, y, k)` is `[x / 2^k, (x + 1) / 2^k] × [y / 2^k, (y + 1) / 2^k]`.
-/

open MLC.Certified

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

def main : IO Unit := do
  for q in rootsUp do
    for (tag, s) in collect gridPmax gridJ gridFuel q do
      IO.println s!"{tag} {s.x} {s.y} {s.k}"
