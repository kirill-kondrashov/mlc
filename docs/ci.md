# Continuous integration

The workflows are `.github/workflows/lean_action_ci.yml` (build and check) and
`.github/workflows/graph_pages.yml` (the graph site and the progress page, built after a
successful build of `main` and deployed; a push to a branch `ci/**` builds the site to test a
change of the pipeline and deploys nothing). The progress page reads the ledger
`docs/progress/ledger.json` from the tree, so the shallow checkout of the workflows suffices; the
job `Scripts` runs the tests of the scripts and `python scripts/check_progress.py --ledger`, which
fails when the last update of the ledger lags the Lean sources (the commit hook records it).

## Why the build is not one job

`Mlc/GridTiles` holds 14 420 independent modules whose kernel checks (`decide +kernel`) cost
about 50 CPU hours on a fast desktop and 8 GB of build outputs (5.4 GB of `.olean`, 2.3 GB of
`.c`). One runner has 4 vCPUs and six hours, so a single `lake build` never finishes there,
and the old cache of `.lake` (16 GB) was above the 10 GB limit of the Actions cache, so the work
was lost every time. The tiles change rarely, so the pipeline keeps their build outputs and lets
Lake confirm that they are up to date; the kernel runs on a tile only when its source changed.

## The key

`python3 scripts/ci_grid.py plan` prints the key of the grid: a digest of the tile sources,
`Mlc/GridDefs.lean`, `lean-toolchain` and `lake-manifest.json`. Equal keys mean that the build
outputs of the tiles are interchangeable between machines: Lake's traces depend on the hashes of
the inputs, not on paths or times, and the build of `Mlc.GridDefs` is reproducible byte for byte.

## Where the tiles come from

A job looks, in this order, for

1. the Actions cache entry `tiles-<key>` (one archive, 0.7 GB; saved by the previous build of
   the same key, readable from every branch after a build of `main`);
2. the seed, an archive of the same content in the git ref `refs/ci-cache/tiles-<key>`
   (chunks of 48 MB in a commit without parents; clones and `actions/checkout` never fetch it,
   so the history stays small);
3. the sharded build: `defs` builds `Mlc.GridDefs` once, 20 jobs `tiles` build the modules of
   their shard (`crc32(module) mod 20`, so a changed tile moves no other tile) and upload the
   outputs, and `build` downloads all archives. A finished shard is cached under
   `tiles-shard-<i>-<key>`, so a re-run resumes where the last one stopped. A cold run measured
   on GitHub took about an hour: 1.5 minutes for `defs`, 26 to 37 minutes for the shards (the
   jobs run at once when 20 runners are free) and 16 minutes for the final build.

After unpacking, `python3 scripts/ci_grid.py check` runs `lake build --no-build` on every tile and
fails at once if Lake would rebuild one, instead of spending hours on it. The remaining modules
(`Mlc.GridCertified` alone takes three minutes) are built by `make build`, and
`scripts/verify_output.sh` runs `make check` and compares its summary with the README.

## After regenerating the grid

The first CI run for the new key builds the shards, which is slow. To skip that, build locally and
publish the outputs as a seed before pushing:

```bash
make build
make seed          # archive .lake/build outputs of the tiles and push refs/ci-cache/tiles-<key>
```

Old seeds can be removed with `git ls-remote origin 'refs/ci-cache/*'` and
`git push origin :refs/ci-cache/tiles-<old key>`.

## Running by hand

`Lean Action CI` also runs on pull requests, on pushes to `main` and to branches named `ci/**`
(to test a change of the pipeline before it reaches `main`), and on `workflow_dispatch`. The input
`use_seed` (default true) can be switched off to force the sharded build, for example when the
`check` step reports that the seed does not match.
