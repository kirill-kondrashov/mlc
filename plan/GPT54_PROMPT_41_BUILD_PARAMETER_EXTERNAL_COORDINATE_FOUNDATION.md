Complete the active-frontier task in
`plan/GPT54_TASK_41_BUILD_PARAMETER_EXTERNAL_COORDINATE_FOUNDATION.md`.

The global objective is to remove
`MLC.green_sublevel_translate_inter_mandelbrot_connected_straddling` from the
dependency graph. The most promising credible route is not to prove the
frozen-base set

```lean
{c' | green_function c (c' - c) < (1 / 2 : ℝ) ^ n} ∩ MandelbrotSet
```

directly. Instead, replace the current surrogate `ParaPuzzlePieceAt` by genuine
moving parameter geometry:

```text
parameter external coordinate
→ parameter rays/equipotentials
→ finite parameter graph
→ connected component / genuine parapuzzle piece
→ connected relative parameter piece
→ migrate the local-connectivity consumer
→ delete the frozen straddling axiom
```

The previous audit (`plan/GPT54_RESULT_26_PIN_FINITE_PARAMETER_GRAPH_OR_BLOCKER.md`)
identified the first missing foundation as the parameter-plane external
coordinate, classically `Φ_M(c) = B_c(c)` on `ℂ \ M`. Do not confuse this with
the existing fixed-parameter dynamical Böttcher maps, dynamical external rays,
or `BottcherParamInverse`.

Perform a feasibility probe first. Determine whether the currently checked
repository Böttcher-family declarations are sufficient to define a genuine
parameter-plane map

```lean
parameterExternalCoord : {c : ℂ // c ∉ MandelbrotSet} → ℂ
```

and prove at least its basic target property `1 < ‖parameterExternalCoord c‖`,
without adding an axiom or silently using the false principal-branch candidate.

If the bridge from the existing dynamical family to evaluation `B_c(c)` outside
the Mandelbrot set is available, implement the smallest honest Lean foundation:

1. add a new focused module for the parameter external coordinate;
2. define the map on the complement subtype;
3. prove only the basic well-definedness/domain and norm facts that compile from
   existing theorems;
4. register the module in `Mlc.lean`;
5. leave parameter rays, equipotentials, finite graphs, and parapuzzle
   connectedness for later prompts.

If that bridge is not available, do not invent a placeholder definition that
merely renames an existing dynamical map, do not add an abstract connectedness
field, and do not add `sorry`, `admit`, or a new axiom. Instead, write a precise
blocker report identifying the first missing theorem/signature and the smallest
next task that would supply it.

In either case, write the worker report to:

`plan/GPT54_RESULT_41_BUILD_PARAMETER_EXTERNAL_COORDINATE_FOUNDATION.md`

Do not resume the finite basin branch/monodromy sequence, renormalization
classification, tube-bundle work, exact-image carving, or the frozen Green-set
route. Do not edit unrelated source files or commit.
