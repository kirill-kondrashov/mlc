# MLC Scripts

Utility scripts and Poetry entry points for graph generation and local serving.

## Factorization figures

Install the optional plotting dependency and regenerate the numerical
parameter-plane, critical-orbit, source, and target figures with:

```sh
poetry install --extras figures --no-root
cd ..
make factorization-figure
```
