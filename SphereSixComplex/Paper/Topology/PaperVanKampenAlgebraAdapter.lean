module

public import SphereSixComplex.Paper.LatticeData

/-! # Lattice monodromies and the toric sublattice -/

@[expose] public section

noncomputable section

open Matrix

namespace SphereSixComplex.Topology

open LatticeData

/-- The order-three lattice monodromy as an additive homomorphism. -/
public def paperMonodromyOne : Lattice →+ Lattice where
  toFun := fun a : Lattice ↦ A₁.mulVec a
  map_zero' := A₁.mulVec_zero
  map_add' := A₁.mulVec_add

/-- The order-four lattice monodromy as an additive homomorphism. -/
public def paperMonodromyTwo : Lattice →+ Lattice where
  toFun := fun a : Lattice ↦ A₂.mulVec a
  map_zero' := A₂.mulVec_zero
  map_add' := A₂.mulVec_add

/-- The toric sublattice killed by the cusp filling. -/
public def paperToricSubgroup : AddSubgroup Lattice where
  carrier := {a | a 0 = 0 ∧ a 1 = 0}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    change a 0 = 0 ∧ a 1 = 0 at ha
    change b 0 = 0 ∧ b 1 = 0 at hb
    change (a + b) 0 = 0 ∧ (a + b) 1 = 0
    simp [ha.1, ha.2, hb.1, hb.2]
  neg_mem' := by
    intro a ha
    change a 0 = 0 ∧ a 1 = 0 at ha
    change (-a) 0 = 0 ∧ (-a) 1 = 0
    simp [ha.1, ha.2]


end SphereSixComplex.Topology

end
