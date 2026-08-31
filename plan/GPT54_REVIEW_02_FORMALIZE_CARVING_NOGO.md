# Supervisor Review 02: Formalized carving no-go

**Verdict:** Lean change accepted; worker report accepted with reporting defects.

The expected result file and source edit both exist. Independent verification:

- `lake env lean Mlc/ParaPuzzleCarvingReduction.lean`: passed;
- `make build`: passed (7977 jobs);
- `make check`: passed and retained exactly the two existing project axioms;
- no new `axiom`, `sorry`, or `admit` appears in the source diff.

The proof is mathematically sound. It establishes openness of each motion-slice
image locally using `AnalyticAt.eventually_constant_or_nhds_le_map_nhds`, excludes
the locally constant branch by slice injectivity, and proves non-openness of the
straddling intersection using preconnectedness and an open separation.

The result report did not fully satisfy its contract: it omitted the exact final
theorem type, diff/status evidence, focused axiom output, and explicit no-commit
confirmation. These are reporting defects, not proof defects. Future reports
must include every requested verification item.

This theorem is a guardrail only. It does not advance a replacement proof of the
frontier connectivity axiom.
