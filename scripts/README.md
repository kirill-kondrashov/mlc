# MLC Scripts

Utility scripts and Poetry entry points for graph generation and local serving.

## Literature sources

The reproducible arXiv source fetcher is independent of the Poetry package:

```sh
python scripts/fetch_arxiv_sources.py
```

Use `--key dudko-lyubich-feigenbaum` to fetch one manifest entry, or
`--force` to refresh an already extracted source tree.  It stores the
compressed archive, metadata, extracted TeX, and a small `00README.json`
marker under `refs/`.

## Factorization figures

Install the optional plotting dependency and regenerate the global
parameter-plane, `X_L`/`F_N` slice, critical-orbit, outer-slice, and
component-geometry figures:

```sh
poetry install --extras figures --no-root
cd ..
make factorization-figure
```

The global parameter-plane figure labels the sampled outer slice `F_N` and
nested slice `X_L` directly. It shows their inclusion inside the radius
windows used to define them.
