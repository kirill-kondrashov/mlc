# MLC Scripts

Utility scripts and Poetry entry points for graph generation and local serving.

## Factorization figures

Install the optional plotting dependency and regenerate the global
parameter-plane, `X_L`/`F_N` slice, critical-orbit, nested-slice, and
outer-slice figures, along with a map analogy for the component inclusion:

```sh
poetry install --extras figures --no-root
cd ..
make factorization-figure
```

The global parameter-plane figure labels the sampled outer slice `F_N` and
nested slice `X_L` directly. It shows their inclusion inside the radius
windows used to define them.
