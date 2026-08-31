# Supervisor Review 04: Motion-image equivalence

**Verdict:** accepted.

The expected result and source edit exist. Independent focused compilation and
`make check` passed, retaining exactly the two pre-existing project axioms.

The identity motion is correctly defined on an arbitrary set, and the
equivalence theorem proves that `ParaPieceIsMotionImage` is exactly
target-connectivity packaging. No frontier declaration changed and no new axiom,
sorry, or admit was introduced.

Together with `not_paraPieceCarvedByMotion_of_straddling`, this closes both
motion-image approaches: self-carving is impossible on the live stratum, while
arbitrary connected-source exact-image existence is equivalent to the target.
