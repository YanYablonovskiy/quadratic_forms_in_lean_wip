import Lake
open Lake DSL

package leanQuadraticForms

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "master"

@[default_target]
lean_lib QuadraticForms where
  srcDir := "Lean"  -- <--- 🔥 This tells lake where source files live
  globs := #[.submodules `QuadraticForms]
