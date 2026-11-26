import Lake
open Lake DSL

package mlc where
  @[default_target]
  lean_lib Mlc

/-- The search program of the certified grid (`scripts/grid_hints.lean`), compiled natively. -/
lean_exe gridhints where
  root := `scripts.grid_hints

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.28.0"

require «yoccoz-theorem» from git
  "https://github.com/kirill-kondrashov/yoccoz-theorem" @ "main"
