Implement the task in
`plan/GPT54_TASK_35_REDUCE_BASIN_PRECONNECTED_TO_SUPERLEVEL.md`.

Context: iteration 34 closed the last mechanical reduction of the genuine
Böttcher-coordinate target. Its two residuals are `holo_on_basin` and
`IsPreconnected (basin_of_infinity c)`. This task attacks the second one by
reducing it to a single concrete per-level fact.

The `FilledJuliaConnected.lean` machinery already proves the *filled* Julia set
`K c` connected via a decreasing intersection of quadratic preimages of a disk.
The basin of infinity is the escaping set — the dual, an **increasing union** of
superlevel sets of the orbit norm:

  `basin_of_infinity c = ⋃ n, {z | R c < ‖orbit c z n‖}`.

Each set in the union is a quadratic preimage of the exterior, they increase with
`n` (once the orbit passes the escape radius `R c` it never returns), and they
share the common far-exterior core, so `isPreconnected_iUnion` reduces basin
preconnectedness to preconnectedness of each superlevel set.

Land ONE theorem, `basin_preconnected_of_forall_superlevel_preconnected`, proving

  `(∀ n, IsPreconnected {z | R c < ‖orbit c z n‖}) → IsPreconnected (basin_of_infinity c)`

for arbitrary `c`. The complete proof script in the task file is planner-verified
to compile (`lake env lean` probe, `PROBE_EXIT_0`) against the current tree.
Paste it verbatim.

Placement: a NEW leaf file `Mlc/BasinConnected.lean` importing
`Mlc.FilledJuliaConnected` and `Mlc.Quadratic.Complex.Bottcher.BottcherCore`
(both needed; this file is a leaf so there is no import cycle), inside
`namespace MLC.Quadratic`. Register it in `Mlc.lean`.

Steps:
(1) Create `Mlc/BasinConnected.lean` with the two imports, `open` line, and the
verbatim theorem inside `namespace MLC.Quadratic`.
(2) Add `import Mlc.BasinConnected` to `Mlc.lean`.
(3) `lake build` clean; no new `sorry`/`axiom`.
(4) Confirm the axiom frontier is still exactly the two project axioms
(`lake env lean check_axioms.lean`, exit 0).
(5) In the result, state that the basin residual is now reduced to the single
crux `∀ n, IsPreconnected {z | R c < ‖orbit c z n‖}` (each orbit-norm superlevel
set is connected), and note this is the genuine remaining content (a
maximum-modulus / no-bounded-complementary-components argument), NOT yet
discharged.

Do NOT introduce `sorry`/`axiom`, do NOT attempt or stub the per-level crux
(leave it as the theorem's hypothesis), do NOT edit `ConstructiveBasinCoordinate.lean`
or `ConstructiveBasinModulus.lean`, and do NOT commit.

Write:

`plan/GPT54_RESULT_35_REDUCE_BASIN_PRECONNECTED_TO_SUPERLEVEL.md`
