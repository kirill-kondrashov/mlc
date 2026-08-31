# Supervisor Review 27: Parameter external coordinate feasibility

**Verdict:** rejected; the proposed coordinate is not the Böttcher coordinate.

The compiled domain bridge is useful and accepted:

- `c ∉ MandelbrotSet` implies `c ∉ K c` by the critical-orbit shift;
- therefore the critical value `c` lies in the basin of infinity;
- the existing Green function gives a radius strictly larger than one there.

But Result 27's central identification is false. `BottcherCore.lean` defines

```lean
polar_green_map c z =
  (if z = 0 then 1 else z / ‖z‖) * exp (green_function c z)
```

and explicitly documents it as a “computational stand-in, not yet the final
theorem-facing Böttcher coordinate API.” It combines the Green radius with the
ordinary Euclidean argument of `z`. The proved norm identity shows only

```lean
‖polar_green_map c z‖ = exp (G_c z).
```

It does not show the Böttcher functional equation, conformality on the basin, the
correct dynamical external angle, or normalization sufficient to identify it with
`B_c`. In general the Euclidean argument is not the Böttcher argument for
`z²+c`.

Therefore

```lean
proxy_bottcher_map c c
```

cannot honestly be named `parameterExternalCoord`, and its outside-disk norm
theorem does not define classical parameter rays. Implementing Result 27 would
create a second frozen/proxy parameter geometry and repeat the mismatch this route
was intended to fix.

The next audit must exclude `polar_green_map`/`proxy_bottcher_map` as the coordinate
provider and locate an actual constructed map satisfying at minimum the Böttcher
functional equation and near-infinity normalization, then determine whether it has
been extended axiom-cleanly to the entire basin for `c ∉ M`.
