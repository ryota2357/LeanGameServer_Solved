import Lake
open Lake DSL

package "LeanGameServer_Solved" where
  version := v!"0.1.0"

require "leanprover-community" / "mathlib"

@[default_target]
lean_lib Game
