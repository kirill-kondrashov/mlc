import Lake
open Lake DSL

package mlc where
  @[default_target]
  lean_lib Mlc

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "master"
