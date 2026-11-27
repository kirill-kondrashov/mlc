import Mlc.GridDefs

/-!
# Search for the certificates of the grid

This program is the prover of the grid certificate. For every square of an input
file it subdivides the squares that it cannot certify and writes the stream of
hints that `MLC.Certified.verifyTree` consumes: `0` for an unresolved finest
cell, `1` for a split, and a certificate `h ≥ 2` otherwise (see `Sq.certify`).
The kernel checks every certificate again, so the search needs no proof.

Usage: `grid_hints F pmax J cap own start stride FILE`. Each line `x y k` of
`FILE` is a square `[x, x + 1] × [y, y + 1] / 2^k`; the program handles the lines
whose index is congruent to `start` modulo `stride` (so that several processes
can share the work) and prints `L x y k count hint...` for each of them, where
`count` is the number of unresolved cells `F` levels below the square. The
parameters are the largest period `pmax ≤ periodLen`, the largest number `J` of
steps of an outside certificate, the largest number `cap` of steps before an
inside certificate (a cheap certificate is worth more area per step of the
kernel), and `own ∈ {0, 1, 2}`, which says whether the square itself is certified
first (`0` for a leaf of an earlier grid, which an equal search failed to certify;
`2` accepts only an inside certificate, for coarsening a region of unresolved cells).

The driver `scripts/refine_grid.py` calls the program on the unresolved cells of
the current grid, `scripts/coarsen_grid.py` calls it on coarser squares that hold
only unresolved cells, and `lake build gridhints` compiles it.
-/

open MLC.Certified

/-- Steps at which the search tries an inside certificate. -/
def checkpoint (n : Nat) : Bool :=
  n ≤ 16 || (n ≤ 64 && n % 4 == 0) || (n ≤ 256 && n % 16 == 0) || n % 64 == 0

/-- The periods `i + 1` (as `i`) for which the floating-point orbit of the center
returns close to the point `z₀` after `i + 1` steps. The kernel does not use this
filter, which only saves the search the costly closure tests of hopeless squares. -/
def plausible (z0r z0i cr ci : Float) (pmax : Nat) : List Nat :=
  ((List.range pmax).foldl
    (fun (acc : List Nat × (Float × Float)) i =>
      let zr := acc.2.1 * acc.2.1 - acc.2.2 * acc.2.2 + cr
      let zi := 2 * acc.2.1 * acc.2.2 + ci
      let dr := zr - z0r
      let di := zi - z0i
      ((if dr * dr + di * di < 0.0225 then acc.1 ++ [i] else acc.1), (zr, zi)))
    ([], (z0r, z0i))).1

/-- The first inside certificate at the model `t` after `n` steps, in the order of
increasing period and remainder, among the periods `ps` (given as `period - 1`). A
remainder below the displacement of the model after `p` steps cannot satisfy the
closure test, so it is skipped. -/
def tryIn (q : Sq) (t : TBall) (n : Nat) (ps : List Nat) : Option Nat :=
  ps.findSome? fun i =>
    let t0 := tmIter q.ca q.cb q.rc (i + 1) { t with e := 0 }
    let lb := normUB (t0.mx - t.mx) (t0.my - t.my) +
      (normUB (t0.dx - t.dx) (t0.dy - t.dy) * q.rc + (SN - 1)) / SN
    if 4 * SN < lb then none else
    (List.range ladderLen).findSome? fun j =>
      let e' := t.e + (q.rc / 4 + 1) * 2 ^ j
      if lb ≤ e' && e' ≤ 4 * SN && closes q.ca q.cb q.rc t (i + 1) e'
      then some (2 * ((n * periodLen + i) * ladderLen + j) + 3) else none

/-- One pass over the steps `0, …, J`: the hint of the first certificate. The
floating-point orbit `(zr, zi)` of the center selects the periods that are tried.
With `insideOnly` the pass accepts no outside certificate and stops as soon as the
floating-point orbit of the center leaves the disk of radius 2. -/
def searchPass (q : Sq) (J cap pmax : Nat) (insideOnly : Bool := false) : Option Nat :=
  go J 0 TBall.zero 0 0
where
  cr : Float := Float.ofInt q.ca / 281474976710656.0
  ci : Float := Float.ofInt q.cb / 281474976710656.0
  inside (n : Nat) (t : TBall) (zr zi : Float) : Option Nat :=
    if n ≤ cap && checkpoint n then
      match plausible zr zi cr ci pmax with
      | [] => none
      | ps => tryIn q t n ps
    else none
  go : Nat → Nat → TBall → Float → Float → Option Nat
    | 0, n, t, zr, zi =>
        if escaped (t.toBall q.rc) then (if insideOnly then none else some (2 * n + 2))
        else inside n t zr zi
    | f + 1, n, t, zr, zi =>
        let m := t.toBall q.rc
        if escaped m then (if insideOnly then none else some (2 * n + 2))
        else if 8 * SN < m.R then none
        else if insideOnly && 4.0 < zr * zr + zi * zi then none
        else
          match inside n t zr zi with
          | some h => some h
          | none =>
              go f (n + 1) (tmStep q.ca q.cb q.rc t)
                (zr * zr - zi * zi + cr) (2 * zr * zi + ci)

/-- The hint stream of the subtree below `q`, `f` levels deep. `own` is `0` when
the square itself is not certified, `1` when it is, and `2` when only an inside
certificate is accepted for it. -/
def search (J cap pmax : Nat) (own : Nat) : Nat → Sq → List Nat
  | 0, q =>
      match (if own != 0 then searchPass q J cap pmax (own == 2) else none) with
      | some h => [h]
      | none => [0]
  | f + 1, q =>
      match (if own != 0 then searchPass q J cap pmax (own == 2) else none) with
      | some h => [h]
      | none =>
          1 :: (search J cap pmax 1 f q.c00 ++ search J cap pmax 1 f q.c10 ++
            search J cap pmax 1 f q.c01 ++ search J cap pmax 1 f q.c11)

def parseSquare (s : String) : Option Sq :=
  match (s.splitOn " ").map String.toInt? with
  | [some x, some y, some k] => some ⟨x, y, k.toNat⟩
  | _ => none

def main (args : List String) : IO UInt32 := do
  match args.map String.toNat? with
  | [some F, some pmax, some J, some cap, some own, some start, some stride, _] =>
      let lines ← IO.FS.lines (args.getLast!)
      let mut i := 0
      for line in lines do
        if i % stride == start then
          match parseSquare line with
          | some q =>
              let hs := search J cap pmax own F q
              let r := verifyTree F q hs
              if r.2 ≠ [] then throw (IO.userError s!"unused hints at {q.x} {q.y} {q.k}")
              IO.println s!"L {q.x} {q.y} {q.k} {r.1} {String.intercalate " " (hs.map toString)}"
          | none => pure ()
        i := i + 1
      return 0
  | _ =>
      IO.eprintln "usage: grid_hints F pmax J cap own start stride FILE"
      return 1
