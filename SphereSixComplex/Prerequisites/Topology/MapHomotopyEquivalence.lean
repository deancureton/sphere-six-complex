module

public import Mathlib.Topology.Homotopy.Equiv

/-!
# Homotopy equivalences carried by a specified map

Mathlib's `ContinuousMap.HomotopyEquiv` bundles a forward map, an inverse map, and the two
homotopies.  `IsHomotopyEquivalence f` records that a *specified* function `f` is the forward map
of such a bundle; it is deliberately stronger than merely asserting that the source and target
spaces are homotopy equivalent.
-/

@[expose] public section

open ContinuousMap

namespace SphereSixComplex

universe u v w

variable {X : Type u} {Y : Type v} {Z : Type w}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- A specified function is a homotopy equivalence when it is exactly the forward function of a
bundled `ContinuousMap.HomotopyEquiv`.  In particular, the equality remembers the given map rather
than only the homotopy-equivalence type of its source and target. -/
public def IsHomotopyEquivalence (f : X → Y) : Prop :=
  ∃ e : X ≃ₕ Y, (e : X → Y) = f

/-- A map satisfying `IsHomotopyEquivalence` is continuous. -/
public theorem IsHomotopyEquivalence.continuous {f : X → Y}
    (hf : IsHomotopyEquivalence f) : Continuous f := by
  obtain ⟨e, rfl⟩ := hf
  exact e.continuous

/-- The identity function is a homotopy equivalence. -/
public theorem isHomotopyEquivalence_id :
    IsHomotopyEquivalence (id : X → X) :=
  ⟨ContinuousMap.HomotopyEquiv.refl X, rfl⟩

/-- The forward function of every bundled homotopy equivalence satisfies the map-level
predicate. -/
public theorem ContinuousMap.HomotopyEquiv.isHomotopyEquivalence (e : X ≃ₕ Y) :
    IsHomotopyEquivalence (e : X → Y) :=
  ⟨e, rfl⟩

/-- Homotopy equivalences carried by specified maps are closed under function composition. -/
public theorem IsHomotopyEquivalence.comp {f : X → Y} {g : Y → Z}
    (hg : IsHomotopyEquivalence g) (hf : IsHomotopyEquivalence f) :
    IsHomotopyEquivalence (g ∘ f) := by
  obtain ⟨ef, rfl⟩ := hf
  obtain ⟨eg, rfl⟩ := hg
  exact ⟨ef.trans eg, rfl⟩

end SphereSixComplex
