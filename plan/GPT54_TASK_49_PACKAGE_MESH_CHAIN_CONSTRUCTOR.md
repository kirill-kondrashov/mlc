# TASK 49 — Package the explicit finite mesh-chain constructor

## Global context

The objective remains removal of:

```lean
MLC.green_sublevel_translate_inter_mandelbrot_connected_straddling
```

Result 47 supplied the Lebesgue-number theorem for the actual Stage 2C cover.
Result 48 supplied the mesh arithmetic and metric estimates. The only missing
piece is a finished `noncomputable` constructor producing the finite ordered
chain.

## Deliverable

In or next to `Mlc/BottcherFiniteEscapingLoopCover.lean`, define a specialized
mesh-chain structure and constructor for
`BasinLoopFiniteLocalRootBranchCover`.

The structure must expose:

```text
m : ℕ
center : Fin (m+1) → cover.centers
cell_subset :
  ∀ k, closed mesh cell k ⊆ coverSet (center k)
covers :
  ∀ t ∈ Icc(0,1), ∃ k, t lies in mesh cell k
adjacent_overlap :
  ∀ j : Fin m,
    meshPointRight j.1 m ∈
      coverSet (center ⟨j.1, ...⟩) ∩
      coverSet (center ⟨j.1+1, ...⟩)
```

The exact types may be adjusted to Lean’s subtype elaboration, but all
membership and coverage statements must be proved.

Construct `m` from the positive Lebesgue number with an explicit
`exists_nat_one_div_lt` argument. For each cell, select a center using the
Lebesgue-ball inclusion at the left mesh endpoint. Derive whole-cell
containment using:

```lean
mesh_interval_dist_lt_fin
```

Use the shared right endpoint of cell `j` as the adjacent overlap witness and
derive its two memberships from the corresponding cell-containment lemmas.

For coverage, prove that every `t ∈ Icc (0,1)` lies in one of the uniform mesh
cells. Use a floor/index argument or an equivalent elementary finite
subdivision proof; do not assert coverage without proof.

## Constraints

- Use `Classical.choose` for `Type`-valued existential selections.
- Keep actual Stage 2C centers and branch data in the output.
- Do not invoke branch rotation or Result 43 yet.
- Do not reuse the vacuous one-cell value-space chart chain.
- No `sorry`, `admit`, or new axiom.
- Do not edit unrelated files or commit.

## Verification

Run:

```bash
lake env lean Mlc/BottcherFiniteEscapingLoopCover.lean
lake build
lake env lean check_axioms.lean
```

The axiom frontier must remain unchanged.

## Result report

Write:

`plan/GPT54_RESULT_49_PACKAGE_MESH_CHAIN_CONSTRUCTOR.md`

Report the exact structure, constructor, mesh coverage proof, center-selection
method, and adjacent-overlap witness theorem.
