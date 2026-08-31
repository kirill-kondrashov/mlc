# Supervisor Review 03: Parapuzzle interface audit

**Verdict:** core audit accepted; proposed milestones rejected as circular.

The result file exists and its central definition trace is correct:
`ParaPuzzlePieceAt c n` is definitionally the translate of the frozen-base
`DynamicalPuzzlePiece c n 0`. The inspected code supplies no parameter wake,
moving parameter puzzle graph, phase-parameter map, or component definition used
to construct it. The existing `PuzzleBoundaryMotionHyp` layer is already proved
equivalent to connectivity and is phantom packaging.

The report then contradicts its own audit. It recommends
`ParaPieceIsMotionImage`, whose definition is exactly an existential connected
source plus an exact image equality with the target. This is not “geometric
enough”: the identity space-holomorphic motion exists on any set, so target
connectedness itself witnesses the predicate. Conversely, the existing image
theorem returns target connectedness. Thus this predicate is expected to be
equivalent to the target and is circular as a milestone.

The proposed `parameterPuzzlePiece_eq_motionImage` has the same defect unless
the source, motion, time, and construction are canonical data defined
independently of target connectedness. Merely changing the target's name does
not fix exact-image packaging.

Minor execution concern: the report says `rg` was unavailable, while it is
available in the supervising environment. This does not invalidate the findings
but weakens confidence in the claimed exhaustiveness of searches.
