import Mlc.GridDefs
import Mlc.GridParams

/-!
Prints `x y nodes cells` for every root square: the number of classifier calls
and the number of unresolved finest cells, evaluated natively.
-/

open MLC.Certified

def nodes (pmax J : Nat) : Nat → Sq → Nat
  | 0, _ => 1
  | f + 1, q =>
      if q.resolved pmax J then 1
      else 1 + nodes pmax J f q.c00 + nodes pmax J f q.c10 +
        nodes pmax J f q.c01 + nodes pmax J f q.c11

def main : IO Unit := do
  for q in rootsUp do
    IO.println s!"{q.x} {q.y} {nodes gridPmax gridJ gridFuel q} {cells gridPmax gridJ gridFuel q}"
