module

public import SphereSixComplex.Topology.StandardThreeTorusDegreeOneCoordinates
public import SphereSixComplex.Topology.StandardThreeTorusDegreeTwoCoordinates
public import SphereSixComplex.Topology.StandardThreeTorusProductDegreeTwoCoordinates

/-!
# Standard three-torus coordinates for cyclic Wang calculations

This file contains only the explicit source-coordinate projections and cyclic norm data used by
the order-three and order-four specializations.  The general naturality boundary is kept in the
neutral `FiniteCyclicMappingTorusWangNaturality` module.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology

namespace SphereSixComplex.Topology.FiniteCyclicThreeTorusWangNaturality

open StandardTorusHomology
open PaperAffineCyclicReducedFiberMappingTorus

public abbrev ThreeLattice := Fin 3 → ℤ
public abbrev SixLattice := Fin 6 → ℤ

/-- Canonical coordinates on the second homology of circle times the standard three-torus. -/
public noncomputable def productHomologyTwo :
    IntegralSingularHomology 2 (UnitAddCircle × StdTorus 3) ≃+ SixLattice :=
  standardCircleProdThreeTorusHomologyTwo

/-- The three base-circle cross fibre-circle coordinates `(01,02,03)`. -/
public def baseCrossDegreeOne : SixLattice →ₗ[ℤ] ThreeLattice where
  toFun x := ![x 0, x 1, x 2]
  map_add' x y := by funext i; fin_cases i <;> simp
  map_smul' n x := by funext i; fin_cases i <;> simp

/-- The three fibre degree-two coordinates `(12,13,23)`. -/
public def fibreDegreeTwo : SixLattice →ₗ[ℤ] ThreeLattice where
  toFun x := ![x 3, x 4, x 5]
  map_add' x y := by funext i; fin_cases i <;> simp
  map_smul' n x := by funext i; fin_cases i <;> simp

/-- Coordinate data for the homological norm, with its codomain restricted to invariants. -/
public structure CyclicNormData (m : ℕ) (M : ThreeLattice →ₗ[ℤ] ThreeLattice) where
  toInvariants : ThreeLattice →ₗ[ℤ] LinearMap.ker (M - LinearMap.id)
  value : ∀ x, (toInvariants x).1 = ∑ i ∈ Finset.range m, (M ^ i) x

end SphereSixComplex.Topology.FiniteCyclicThreeTorusWangNaturality

end

end
