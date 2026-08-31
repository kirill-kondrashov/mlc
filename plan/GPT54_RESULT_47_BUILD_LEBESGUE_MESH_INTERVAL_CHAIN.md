# Task 47 Result: Build Lebesgue Mesh Interval Chain

## Outcome

Partial progress landed and checked in Lean.

I confirmed that Mathlib provides the needed compact-metric-space theorem:

```lean
lebesgue_number_lemma_of_metric
```

and used it directly on the subtype `I := {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1}` with the Stage 2C open cover family

```lean
cover.coverSet : I → Set I.
```

This yields a genuine Lebesgue number `δ > 0` for the relative-open cover attached to
`BasinLoopFiniteLocalRootBranchCover`.

I also added concrete mesh-endpoint helpers for the uniform subdivision of `[0,1]`:

- `mesh_left_mem_Icc`
- `mesh_right_mem_Icc`
- `meshPoint`
- `meshPointRight`

These expose actual subdivision endpoints as points of the interval subtype.

## Lean changes landed

In `Mlc/BottcherFiniteEscapingLoopCover.lean` I added:

```lean
lemma BasinLoopFiniteLocalRootBranchCover.exists_lebesgue_number
    (cover : BasinLoopFiniteLocalRootBranchCover c N z₀ γ) :
    ∃ δ > 0,
      ∀ x : {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1},
        ∃ i, Metric.ball x δ ⊆ cover.coverSet i
```

and the mesh endpoint support:

```lean
lemma mesh_left_mem_Icc (k m : ℕ) (hk : k ≤ m) :
    ((k : ℝ) / (m + 1 : ℝ)) ∈ Set.Icc (0 : ℝ) 1

lemma mesh_right_mem_Icc (k m : ℕ) (hk : k < m + 1) :
    ((k + 1 : ℝ) / (m + 1 : ℝ)) ∈ Set.Icc (0 : ℝ) 1

noncomputable def meshPoint (k m : ℕ) (hk : k ≤ m) :
    {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1}

noncomputable def meshPointRight (k m : ℕ) (hk : k < m + 1) :
    {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1}
```

The edited file validates.

## What remains

The still-missing part is the final packaging of the **ordered per-cell assignment**:

- choose `m` with mesh size `< δ`;
- for each cell `k`, choose a center `i_k` whose `coverSet` contains the left-endpoint ball;
- turn the ball containment into interval containment for the whole mesh cell;
- package the shared endpoint between cell `k` and `k+1` as the explicit adjacent overlap witness.

This is now a bookkeeping problem rather than a topological blocker. The main theorem/API gap from Task 46 is repaired at the correct level: the repository now has a checked Lebesgue-number theorem specialized to the actual Stage 2C cover family.

## Why I stopped here

I did **not** add a large `Fin`-indexed chain structure without finishing the actual per-cell selection and containment proofs. The remaining work is mostly subtype and arithmetic plumbing around the uniform mesh, and should be done in the next task/pass rather than by asserting fields prematurely.

## Validation

Checked with:

```bash
lake env lean Mlc/BottcherFiniteEscapingLoopCover.lean
```

which succeeded after the edits.
