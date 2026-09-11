module

public import SphereSixComplex.Prerequisites.Topology.MapHomotopyEquivalence

/-!
# Transporting specified homotopy equivalences along homeomorphisms

This file supplies the small amount of bookkeeping needed when a specified map is replaced by
the same map written in homeomorphic source or target coordinates.  Besides proposition-level
closure lemmas, it exposes bundled witnesses whose pointwise behaviour is easy to rewrite.
-/

@[expose] public section

open ContinuousMap

namespace SphereSixComplex

universe u v w

variable {X : Type u} {Y : Type v} {Z : Type w}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

namespace IsHomotopyEquivalence


/-- A chosen bundled witness for a specified homotopy equivalence. -/
public noncomputable def homotopyEquiv {f : X → Y} (hf : IsHomotopyEquivalence f) : X ≃ₕ Y :=
  Classical.choose hf










end IsHomotopyEquivalence

end SphereSixComplex
