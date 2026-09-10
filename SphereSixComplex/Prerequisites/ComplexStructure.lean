module

public import ChallengeDefs

/-!
# Complex Structures on the Six-Sphere

Every definition the final theorem mentions lives in `ChallengeDefs`, which depends only on Mathlib,
so that the Comparator boundary is self-contained and auditable on its own. This module re-exports
those definitions to the rest of the development, so downstream imports are unchanged.

Note that this imports `ChallengeDefs`, not `Challenge`: the latter also declares the sorried
challenge statement, and `Solution` must not see it.
-/
