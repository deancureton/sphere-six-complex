module

public import SphereSixComplex.Prerequisites.Topology.StandardThreeTorusDegreeOneCoordinates
public import SphereSixComplex.Prerequisites.Topology.StandardThreeTorusDegreeTwoCoordinates
public import SphereSixComplex.Prerequisites.Topology.StandardThreeTorusProductDegreeTwoCoordinates

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
open CyclicMappingTorus

public abbrev ThreeLattice := Fin 3 → ℤ
public abbrev SixLattice := Fin 6 → ℤ

/-- Canonical coordinates on the second homology of circle times the standard three-torus. -/
public noncomputable def productHomologyTwo :
    IntegralSingularHomology 2 (UnitAddCircle × StdTorus 3) ≃+ SixLattice :=
  standardCircleProdThreeTorusHomologyTwo




end SphereSixComplex.Topology.FiniteCyclicThreeTorusWangNaturality

end

end
