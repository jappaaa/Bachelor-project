import Lake

open Lake DSL

package project
@[default_target]
lean_lib project
  
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "master"

