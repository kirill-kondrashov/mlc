Run the final source-first gate:

`plan/GPT54_TASK_71_ASSEMBLE_PROVIDER_AND_REROUTE_ROOT.md`

Proceed only if Result 70 constructed a complete genuine
`FiniteMovingWindowProviderData`.

Then:

1. route `MLC.mlc_conjecture` through the moving-window main route;
2. rebuild all affected modules;
3. remove the now-unused frozen straddling axiom;
4. run `lake build` and `lake env lean check_axioms.lean`;
5. confirm that no equivalent provider axiom, `sorryAx`, or hidden frozen wrapper
   remains in the root dependency graph.

If Result 70 stopped at a missing theorem, do not edit the root and report that
the sequence terminates at that source gap. Do not commit.

Write:

`plan/GPT54_RESULT_71_ASSEMBLE_PROVIDER_AND_REROUTE_ROOT.md`
