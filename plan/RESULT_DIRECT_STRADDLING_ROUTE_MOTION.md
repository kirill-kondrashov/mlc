# Direct straddling route: local Böttcher motion milestone

## Outcome

The next Route-C analytic brick is implemented and checked
`Mlc/Quadratic/Complex/Bottcher/BottcherParamMotion.lean`.

The module adds:

- `exists_param_inverse_singleton_motion`;
- `exists_nontrivial_param_inverse_motion`;
- `exists_nontrivial_param_inverse_disk_motion`.

The strongest theorem extracts the eventual left-inverse identity from
`exists_param_holo_bottcher_inverse`, chooses a small radius around the inverse
base point, and uses the explicit translation

```text
f(t, z) = z + a t
```

on a closed disk source.  Both the parameter coordinate and the dynamical
coordinate stay inside the inverse germ's neighborhood, so the local Böttcher
inverse recovers the translated point.  The source disk is connected by convexity,
and the motion is space-holomorphic because its slices are translations.

## Exact checked content

For every base parameter `c₀`, there are `z₀`, `w₀`, a local inverse `ψ`, positive
real `ε`, `a`, and `b`, and a `SpaceHolomorphicMotion H` of
`closedBall z₀ ε` such that:

```text
w₀ = logSeriesBottcherApprox c₀ z₀

ψ (c₀ + b t,
   logSeriesBottcherApprox (c₀ + b t) (H.f t z))
  = (c₀ + b t, H.f t z)
```

for every `t` in the unit disk and every source point `z`.  The motion is
nontrivial at `t = 1/2`.

The proof uses only the existing checked near-infinity parameter inverse and
elementary metric, convexity, and holomorphy facts.  No axiom, `sorry`, or
connectedness witness for a Mandelbrot slice was added.

## Boundary of the result

This is a local inverse-family and motion infrastructure result, not the
Douady–Hubbard parameter/dynamical correspondence.  The source is an explicit
closed disk, not a puzzle boundary or equipotential, and the theorem does not
identify its image with

```text
{c' | green_function c (c' - c) < (1/2)^n} ∩ MandelbrotSet.
```

Consequently the straddling axiom remains in place.  The next genuine Route-C
brick is still to extend the near-infinity coordinate coherently to the relevant
basin/equipotential boundary and prove the independent parameter-piece
correspondence; the present result supplies only the local motion-side base.

## Validation

- `lake env lean Mlc/Quadratic/Complex/Bottcher/BottcherParamMotion.lean`
- `make build`
- `make check`
- `scripts/verify_output.sh`

All completed successfully.  The axiom frontier remains exactly the two
non-core project axioms: the straddling connectivity axiom and the residual
near-Molecule axiom.  The Prompt 109 comparison changes remain uncommitted
alongside this new module.
