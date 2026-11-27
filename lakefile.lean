import Lake
open Lake DSL

package mlc

-- The aggregator `Mlc/GridCertified.lean` has thousands of generated commands, and
-- elaborating them overflows the default thread stack of 8 MB. `weakLeanArgs` stay
-- out of the build trace, so changing the stack size rebuilds no module.
@[default_target]
lean_lib Mlc where
  weakLeanArgs := #["--tstack=65536"]

/-- The search program of the certified grid (`scripts/grid_hints.lean`), compiled natively. -/
lean_exe gridhints where
  root := `scripts.grid_hints

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.28.0"

require «yoccoz-theorem» from git
  "https://github.com/kirill-kondrashov/yoccoz-theorem" @ "main"
