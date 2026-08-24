module

public import SphereSixComplex.LatticeData

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
public theorem e₁_zero : e₁ 0 = 1 :=
  rfl

@[simp]
public theorem e₁_one : e₁ 1 = 0 :=
  rfl

@[simp]
public theorem e₂_zero : e₂ 0 = 0 :=
  rfl

@[simp]
public theorem e₂_one : e₂ 1 = 1 :=
  rfl

/-- The three unoriented edge directions of the `A₂` triangulation. -/
public def direction : Fin 3 → ToricLattice
  | 0 => e₁
  | 1 => e₂ - e₁
  | 2 => -e₂

/-- Put two lattice vectors into the columns of a two-by-two matrix. -/
public def pairMatrix (a b : ToricLattice) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![a 0, b 0; a 1, b 1]

public theorem direction_sum_zero : direction 0 + direction 1 + direction 2 = 0 := by
  ext i
  fin_cases i <;> norm_num [direction, e₁, e₂]

/-- Consecutive `A₂` directions form oriented integral bases. -/
public theorem direction_pair_det (i : Fin 3) :
    (pairMatrix (direction i) (direction (i + 1))).det = 1 := by
  decide +revert

/-- The six rays of the smooth complete fan of the degree-six toric del Pezzo surface. -/
public def hexagonRay : Fin 6 → ToricLattice
  | 0 => e₁
  | 1 => e₂
  | 2 => e₂ - e₁
  | 3 => -e₁
  | 4 => -e₂
  | 5 => e₁ - e₂

/-- The ray opposite a given side of the hexagon. -/
public def oppositeRay (i : Fin 6) : Fin 6 := i + 3

@[simp]
public theorem oppositeRay_involutive (i : Fin 6) :
    oppositeRay (oppositeRay i) = i := by
  fin_cases i <;> rfl

@[simp]
public theorem hexagonRay_opposite (i : Fin 6) :
    hexagonRay (oppositeRay i) = -hexagonRay i := by
  decide +revert

/-- Every two-dimensional cone of the hexagonal fan is unimodular. -/
public theorem hexagonCone_det (i : Fin 6) :
    (pairMatrix (hexagonRay i) (hexagonRay (i + 1))).det = 1 := by
  decide +revert

/-- The cusp shear `B₀` is an orientation-preserving integral equivalence. -/
public theorem cuspShear_det : SphereSixComplex.LatticeData.B₀.det = 1 :=
  SphereSixComplex.LatticeData.B₀_det

end SphereSixComplex.Geometry.CuspCombinatorics
