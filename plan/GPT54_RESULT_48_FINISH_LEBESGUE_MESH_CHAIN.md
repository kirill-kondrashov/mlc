# Task 48 Result: Finish Lebesgue Mesh Chain

## Outcome

Partial progress landed and checked, but the full `Fin`-indexed mesh-chain constructor was **not** completed in this pass.

What did land is the remaining hard analytic/arithmetic bridge needed by the mesh argument:

- a closed-form mesh-step identity;
- a pointwise coordinate estimate on each uniform mesh cell;
- the corresponding metric-ball inclusion at the left endpoint of the cell.

This means the proof is now reduced to a pure finite-choice packaging problem.

## Lean changes landed

In `Mlc/BottcherFiniteEscapingLoopCover.lean` I added the checked lemmas:

```lean
lemma mesh_step_eq (k m : ℕ) :
    ((k + 1 : ℝ) / (m + 1 : ℝ)) - ((k : ℝ) / (m + 1 : ℝ)) = (1 : ℝ) / (m + 1 : ℝ)

lemma mesh_interval_coord_lt_fin
    {δ : ℝ} {m : ℕ} (hm : 1 / (m + 1 : ℝ) < δ)
    {k : Fin (m + 1)}
    {y : {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1}}
    (hy : y.1 ∈ Set.Icc ((k.1 : ℝ) / (m + 1 : ℝ)) (((k.1 + 1 : ℕ) : ℝ) / (m + 1 : ℝ))) :
    |y.1 - (k.1 : ℝ) / (m + 1 : ℝ)| < δ

lemma mesh_interval_dist_lt_fin
    {δ : ℝ} {m : ℕ} (hm : 1 / (m + 1 : ℝ) < δ)
    {k : Fin (m + 1)}
    {y : {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1}}
    (hy : y.1 ∈ Set.Icc ((k.1 : ℝ) / (m + 1 : ℝ)) (((k.1 + 1 : ℕ) : ℝ) / (m + 1 : ℝ))) :
    dist y (meshPoint k.1 m (Nat.le_of_lt_succ k.2)) < δ
```

These complement Result 47’s previously landed:

- `BasinLoopFiniteLocalRootBranchCover.exists_lebesgue_number`
- `mesh_left_mem_Icc`
- `mesh_right_mem_Icc`
- `meshPoint`
- `meshPointRight`

## What remains exactly

The unfinished part is now only the `noncomputable` constructor that packages the finite data:

1. choose `m` from `exists_nat_one_div_lt` applied to the Lebesgue number;
2. for each `k : Fin (m+1)`, choose a center `i_k` from
   `hLeb (meshPoint k.1 m ...)`;
3. use `mesh_interval_dist_lt_fin` plus the chosen ball containment to prove each cell lies in `coverSet i_k`;
4. record the overlap witness for adjacent cells via the shared endpoint;
5. package coverage of any `t ∈ Icc (0,1)` by choosing the obvious mesh cell.

## Why the full constructor did not land yet

I probed the intended constructor shape and hit two Lean-engineering issues:

- `Exists`-elimination for the Lebesgue data must be handled in a `noncomputable` definition via `Classical.choose`, not by a direct `rcases` into `Type`-valued output;
- the overlap witness fields need careful off-by-one handling (`Fin m` for adjacency, `Fin (m+1)` for cells/endpoints).

These are bookkeeping problems only. The substantive topological and metric part of Task 48 is now in the file and checked.

## Validation

Checked with:

```bash
lake env lean Mlc/BottcherFiniteEscapingLoopCover.lean
```

which succeeded after the edits.
