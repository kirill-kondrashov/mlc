# Pilgrim: bisets and global curve attractors

Version 1.0, 8 November 2026. A research package within MLC.
It builds separately and does not require the Lean library.
Shared TeX support is in [tex/research](../../tex/research/).

**B3:** construct an explicit finite global attractor of essential
simple curves for the rabbit–Basilica mating

$$
F(z)=\frac{z^2+\lambda}{z^2-1},\qquad \lambda=(1+i\sqrt3)/2.
$$

The main theorem is unproved. Literature screening supports novelty of
the full theorem within the inspected sources. Auxiliary audit lemmas
are proved on paper and partly checked by exact computation.
No implication from B3 to MLC is established.
The main working time is allocated to the [MLC direction](../../study/README.md);
B3's plan is retained for separate continuation.

- [Statement and initial calculations](research/B3_candidate.md), [PDF](b3_candidate.pdf).
- [Detailed audit](research/B3_novelty_audit.md), [PDF](b3_audit.pdf).
- [Novelty screening](research/B3_publication_screening.md), [PDF](b3_publication.pdf).
- [Sources](references.md), [next steps](research_plan.md).
- [Decision register](research/novelty_register.csv), [deferred plan](progress.csv).

From the repository root:

```bash
make -C packages/pilgrim-bisets
make -C packages/pilgrim-bisets check
```

Requires Python 3, Pandoc, XeLaTeX, Noto Serif, Noto Sans, and DejaVu Sans Mono.
Scripts use the Python standard library. `check` verifies algebraic
identities and finite audit data. Global attraction remains unproved.
