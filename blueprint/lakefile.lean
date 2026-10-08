import Lake

open Lake DSL

require SphereSixComplex from ".."
require VersoBlueprint from git
  "https://github.com/leanprover/verso-blueprint.git" @ "a441323930138cccf42e34396746af67d72078b6"
require verso from git
  "https://github.com/leanprover/verso" @ "v4.35.0-rc3"
require «verso-slides» from git
  "https://github.com/leanprover/verso-slides" @ "e05b619b1c3e3d5ce648b606d1cd0b0fadf7f52a"
require subverso from git
  "https://github.com/leanprover/subverso" @ "d047cb484b2f3598187450935dbcc84d078cb581"
require proofwidgets from git
  "https://github.com/leanprover-community/ProofWidgets4" @ "c643bbb3c24f8a25f9c14e3a6b1ceb13d01f3de1"
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "6b7abb3c7686292736be2955bd3eb9ebf63b456a"

package SphereSixComplexBlueprint where
  precompileModules := false
  leanOptions := #[⟨`experimental.module, true⟩, ⟨`autoImplicit, false⟩]

@[default_target]
lean_lib SphereSixComplexBlueprint where
