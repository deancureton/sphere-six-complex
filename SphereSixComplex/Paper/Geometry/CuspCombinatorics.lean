module

public import SphereSixComplex.Paper.LatticeData

/-!
# Combinatorics of the cusp fan

This file records the integral `A₂` direction data and the smooth hexagonal fan used by the toric
cusp filling on the second page of the paper.
-/

open Matrix

namespace SphereSixComplex.Geometry.CuspCombinatorics

/-- The rank-two toric lattice at the cusp. -/
public abbrev ToricLattice := Fin 2 → ℤ

@[expose] public def e₁ : ToricLattice := ![1, 0]

@[expose] public def e₂ : ToricLattice := ![0, 1]















@[simp]
public theorem e₁_one : e₁ 1 = 0 :=
  rfl

@[simp]
public theorem e₁_zero : e₁ 0 = 1 :=
  rfl

@[simp]
public theorem e₂_zero : e₂ 0 = 0 :=
  rfl

@[simp]
public theorem e₂_one : e₂ 1 = 1 :=
  rfl

end SphereSixComplex.Geometry.CuspCombinatorics
