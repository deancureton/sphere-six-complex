module

public import SphereSixComplex.Prerequisites.Topology.FiniteCyclicMappingTorusWangNaturality
public import SphereSixComplex.Prerequisites.Topology.FiniteCyclicThreeTorusWangNaturality

/-!
# The oriented product Wang boundary for the standard three-torus

The canonical coordinates on `H₂(S¹ × T³; ℤ)` split into the three base-circle cross
fibre-circle classes and the three fibre two-torus classes.  This file constructs the resulting
oriented product Wang presentation directly from those coordinates.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology
open scoped ContinuousMap

namespace SphereSixComplex.Topology.StandardThreeTorusProductWangBoundary

open FiniteCyclicMappingTorusWangNaturality
open FiniteCyclicThreeTorusWangNaturality
open CyclicMappingTorus
open StandardTorusHomology

/-- Assemble the base-cross and fibre coordinates in the standard pair ordering. -/
public def joinCoordinates (a b : ThreeLattice) : SixLattice :=
  ![a 0, a 1, a 2, b 0, b 1, b 2]




private theorem gammaSplit_symm_comp_fiberInclusion :
    (StandardTorusHomology.fourTorusSplit.symm : C(UnitAddCircle × StdTorus 3, StdTorus 4)).comp
        (circleProductFiberInclusion (X := StdTorus 3)) =
      standardThreeTorusTailInclusion := by
  ext x i
  fin_cases i <;> rfl

/-- In product coordinates, fibre inclusion occupies exactly the last three coordinates. -/
public theorem productHomologyTwo_fiberInclusion
    (x : IntegralSingularHomology 2 (StdTorus 3)) :
    productHomologyTwo
        (integralSingularHomologyMap 2
          (circleProductFiberInclusion (X := StdTorus 3)) x) =
      joinCoordinates 0 (standardThreeTorusHomologyTwo x) := by
  rw [productHomologyTwo, standardCircleProdThreeTorusHomologyTwo_apply]
  rw [integralSingularHomologyMap_comp_wang, gammaSplit_symm_comp_fiberInclusion]
  rw [standardThreeTorusTailInclusion_homologyTwo_coordinates]
  rfl







end SphereSixComplex.Topology.StandardThreeTorusProductWangBoundary

end

end
