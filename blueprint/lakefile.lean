import Lake

open Lake DSL

require SphereSixComplex from ".."
require VersoBlueprint from git
  "https://github.com/leanprover/verso-blueprint.git" @ "a441323930138cccf42e34396746af67d72078b6"
require mathlib from git
  "https://github.com/Paul-Lez/mathlib4" @ "97d303eb50436be7c4bac4388bdb49459ae9140b"

package SphereSixComplexBlueprint where
  precompileModules := false
  leanOptions := #[⟨`experimental.module, true⟩, ⟨`autoImplicit, false⟩]

@[default_target]
lean_lib SphereSixComplexBlueprint where
