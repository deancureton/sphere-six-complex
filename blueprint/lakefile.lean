import Lake

open Lake DSL

require SphereSixComplex from ".."
require VersoBlueprint from git
  "https://github.com/leanprover/verso-blueprint.git" @ "v4.33.0"
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.33.1"

package SphereSixComplexBlueprint where
  precompileModules := false
  leanOptions := #[⟨`experimental.module, true⟩, ⟨`autoImplicit, false⟩]

@[default_target]
lean_lib SphereSixComplexBlueprint where
