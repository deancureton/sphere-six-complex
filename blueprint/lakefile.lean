import Lake

open Lake DSL

require SphereSixComplex from ".."
require VersoBlueprint from git
  "https://github.com/leanprover/verso-blueprint.git" @ "v4.33.0"
require mathlib from git
  "https://github.com/Paul-Lez/mathlib4" @ "dba911505e5f973d80c20bb1e3f6952f34081e29"

package SphereSixComplexBlueprint where
  precompileModules := false
  leanOptions := #[⟨`experimental.module, true⟩, ⟨`autoImplicit, false⟩]

@[default_target]
lean_lib SphereSixComplexBlueprint where
