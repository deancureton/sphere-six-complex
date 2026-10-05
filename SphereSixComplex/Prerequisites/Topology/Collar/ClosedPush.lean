module

public import Mathlib.Topology.Homotopy.Contractible
public import Mathlib.Topology.UnitInterval
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Tactic

@[expose] public section
noncomputable section

open Set Topology
open scoped unitInterval

namespace SphereSixComplex


namespace ClosedTopologicalCollar

variable {X : Type*} [TopologicalSpace X] {B : Set X}














public def interiorInclusion (B : Set X) : C(↥(Bᶜ), X) :=
  ⟨Subtype.val, continuous_subtype_val⟩





end ClosedTopologicalCollar
end SphereSixComplex
