import Lake
open Lake DSL

package «erdos-307» where
  name := "erdos-307"
  version := "0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.14.0"

lean_lib «Erdos307» where
  roots := #[`Erdos307]
