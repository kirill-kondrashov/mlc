import Lake
open Lake DSL

package mlc where
  @[default_target]
  lean_lib Mlc

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "4a98d4f54f7a55a60e0861e24e3387e924d15b04"
