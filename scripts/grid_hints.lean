import Mlc.GridDefs

/-!
# Search for the certificates of the grid

This program is the prover of the grid certificate. For every root square it
subdivides the squares that it cannot certify and writes the stream of hints
that `MLC.Certified.verifyTree` consumes: `0` for an unresolved finest cell,
`1` for a split, and a certificate `h ≥ 2` otherwise (see `Sq.certify`). The
kernel checks every certificate again, so the search needs no proof.

Usage: `lake env lean --run scripts/grid_hints.lean F pmax J start stride` prints one line
`R x y count hint...` for each root square whose index among the 512 root squares is
congruent to `start` modulo `stride` (so that several processes can share the work), where `count` is the
number of unresolved finest cells below the root, `F` the number of
subdivisions below the root squares, `pmax ≤ 8` the largest period of an inside
certificate and `J` the largest number of steps of a certificate.
-/

open MLC.Certified

/-- Steps at which the search tries an inside certificate. -/
def checkpoint (n : ℕ) : Bool :=
  n ≤ 16 || (n ≤ 64 && n % 4 == 0) || (n ≤ 256 && n % 16 == 0) || n % 64 == 0

/-- The first inside certificate at the model `t` after `n` steps, in the order of
increasing period and remainder. A remainder below the displacement of the model
after `p` steps cannot satisfy the closure test, so it is skipped. -/
def tryIn (q : Sq) (t : TBall) (n pmax : ℕ) : Option ℕ :=
  (List.range pmax).findSome? fun i =>
    let t0 := tmIter q.ca q.cb q.rc (i + 1) { t with e := 0 }
    let lb := normUB (t0.mx - t.mx) (t0.my - t.my) +
      (normUB (t0.dx - t.dx) (t0.dy - t.dy) * q.rc + (SN - 1)) / SN
    if 4 * SN < lb then none else
    (List.range ladderLen).findSome? fun j =>
      let e' := t.e + (q.rc / 4 + 1) * 2 ^ j
      if lb ≤ e' && e' ≤ 4 * SN && closes q.ca q.cb q.rc t (i + 1) e'
      then some (2 * ((n * periodLen + i) * ladderLen + j) + 3) else none

/-- One pass over the steps `0, …, J`: the hint of the first certificate. -/
def searchPass (q : Sq) (J pmax : ℕ) : Option ℕ :=
  go J 0 TBall.zero
where
  go : ℕ → ℕ → TBall → Option ℕ
    | 0, n, t =>
        if escaped (t.toBall q.rc) then some (2 * n + 2)
        else if checkpoint n then tryIn q t n pmax else none
    | f + 1, n, t =>
        let m := t.toBall q.rc
        if escaped m then some (2 * n + 2)
        else if 8 * SN < m.R then none
        else
          match (if checkpoint n then tryIn q t n pmax else none) with
          | some h => some h
          | none => go f (n + 1) (tmStep q.ca q.cb q.rc t)

/-- The hint stream of the subtree below `q`, `f` levels deep. -/
def search (J pmax : ℕ) : ℕ → Sq → List ℕ
  | 0, q => match searchPass q J pmax with | some h => [h] | none => [0]
  | f + 1, q =>
      match searchPass q J pmax with
      | some h => [h]
      | none =>
          1 :: (search J pmax f q.c00 ++ search J pmax f q.c10 ++
            search J pmax f q.c01 ++ search J pmax f q.c11)

def main (args : List String) : IO Unit := do
  match args.map String.toNat? with
  | [some F, some pmax, some J, some start, some stride] =>
      for (q, i) in rootsUp.zip (List.range rootsUp.length) do
        if i % stride == start then
          let hs := search J pmax F q
          let r := verifyTree F q hs
          if r.2 ≠ [] then throw (IO.userError s!"unused hints at {q.x} {q.y}")
          IO.println s!"R {q.x} {q.y} {r.1} {String.intercalate " " (hs.map toString)}"
  | _ => IO.eprintln "usage: grid_hints F pmax J start stride"
