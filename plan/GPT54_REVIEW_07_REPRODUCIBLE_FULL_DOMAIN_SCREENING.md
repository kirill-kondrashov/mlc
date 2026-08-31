# Supervisor Review 07: Whole-domain screening

**Verdict:** numerical conclusion provisionally accepted; reproducibility defect
recorded.

The expected report exists and the actual `/tmp/mlc_task07_screen.py` uses
`base_im` correctly. The report's embedded “complete script,” however, contains
`+ cim` inside `green_below_threshold`, an undefined name. The embedded artifact
would not run and is not an exact copy of the executed source.

The whole-domain methodology fixes Task 06's decisive crop problem. Within the
completed 256/512 matrix, neither basilica nor rabbit has a secondary component
that persists across cutoff, resolution, and both adjacency conventions. The
single rabbit 4-neighbor split has zero Chebyshev pixel gap and disappears under
8-neighbor adjacency, so it is not a certification candidate.

Accepted conclusion: the current target is not numerically refuted by these
tests. This is not affirmative evidence for universal connectivity, and it does
not resolve PLAN 04 Option A versus Option B.

Future numerical reports must embed the exact executed source or preserve a
verifiable copy; “complete source” transcription errors are contract failures.
