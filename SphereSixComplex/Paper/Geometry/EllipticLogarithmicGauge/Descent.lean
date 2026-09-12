module

public import SphereSixComplex.Paper.Geometry.EllipticLogarithmicGauge.Basic
public import SphereSixComplex.Prerequisites.Geometry.EquivariantQuotientHomeomorph
import all SphereSixComplex.Paper.Geometry.EllipticWholeFiberTrivialization
import all SphereSixComplex.Paper.Geometry.EllipticVaryingFamilyQuotient

/-!
# Quotient descent for the elliptic logarithmic gauges

Compatible local logarithm branches give a single torus-valued gauge after branch changes are
identified by lattice periods.  This file isolates the exact remaining gluing data for that
gauge and proves that it descends from the affine cyclic collar quotient to the linear cyclic
collar quotient.  It does not posit a global logarithm on a punctured disc or identify either
local quotient with a paper-specific space.
-/

namespace SphereSixComplex.Geometry.EllipticLogarithmicGauge

open Set
open SphereSixComplex.Geometry SphereSixComplex.TriangleGroup
open SphereSixComplex.Periods
open SphereSixComplex.Geometry.TorusFamily
open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.Geometry.EllipticWholeFiberTrivialization
open SphereSixComplex.Geometry.EllipticVaryingFamilyQuotient
open SphereSixComplex.Geometry.EllipticLocalCoordinates
open SphereSixComplex.Geometry.EquivariantQuotientHomeomorph

noncomputable section

variable {U : TriangleUniformization} (F : PeriodFunctions U)

/-- The order-three linear cyclic action obtained by restricting the global deck action. -/
@[expose, instance_reducible] public noncomputable def orderThreeLinearFamilyAction :
    MulAction (FiniteCyclic 3) (TotalSpace (parameterMap F)) where
  smul g q := orderThreeFamilyRepresentation F g q
  one_smul q := by
    change orderThreeFamilyRepresentation F 1 q = q
    rw [map_one]
    rfl
  mul_smul g h q := by
    change orderThreeFamilyRepresentation F (g * h) q =
      orderThreeFamilyRepresentation F g (orderThreeFamilyRepresentation F h q)
    rw [map_mul]
    rfl

/-- The order-four linear cyclic action obtained by restricting the global deck action. -/
@[expose, instance_reducible] public noncomputable def orderFourLinearFamilyAction :
    MulAction (FiniteCyclic 4) (TotalSpace (parameterMap F)) where
  smul g q := orderFourFamilyRepresentation F g q
  one_smul q := by
    change orderFourFamilyRepresentation F 1 q = q
    rw [map_one]
    rfl
  mul_smul g h q := by
    change orderFourFamilyRepresentation F (g * h) q =
      orderFourFamilyRepresentation F g (orderFourFamilyRepresentation F h q)
    rw [map_mul]
    rfl

public theorem orderThreeAffine_actionMap_generator
    (q : TotalSpace (parameterMap F)) :
    actionMap (orderThreeAffineFamilyAction F) (cyclicGenerator 3) q =
      orderThreeAffineFamilyGenerator F q := by
  rw [actionMap.eq_def]
  change orderThreeAffineFamilyRepresentation F (cyclicGenerator 3) q = _
  rw [orderThreeAffineFamilyRepresentation.eq_def, cyclicGenerator.eq_def,
    cyclicRepresentation_generator]

public theorem orderFourAffine_actionMap_generator
    (q : TotalSpace (parameterMap F)) :
    actionMap (orderFourAffineFamilyAction F) (cyclicGenerator 4) q =
      orderFourAffineFamilyGenerator F q := by
  rw [actionMap.eq_def]
  change orderFourAffineFamilyRepresentation F (cyclicGenerator 4) q = _
  rw [orderFourAffineFamilyRepresentation.eq_def, cyclicGenerator.eq_def,
    cyclicRepresentation_generator]

public theorem orderThreeLinear_actionMap_generator
    (q : TotalSpace (parameterMap F)) :
    actionMap (orderThreeLinearFamilyAction F) (cyclicGenerator 3) q =
      familyDeckMap F g₁ q := by
  rw [actionMap.eq_def]
  change orderThreeFamilyRepresentation F (cyclicGenerator 3) q = _
  rw [orderThreeFamilyRepresentation, SphereSixComplex.TriangleGroup.g₁.eq_def]
  rfl

public theorem orderFourLinear_actionMap_generator
    (q : TotalSpace (parameterMap F)) :
    actionMap (orderFourLinearFamilyAction F) (cyclicGenerator 4) q =
      familyDeckMap F g₂ q := by
  rw [actionMap.eq_def]
  change orderFourFamilyRepresentation F (cyclicGenerator 4) q = _
  rw [orderFourFamilyRepresentation, SphereSixComplex.TriangleGroup.g₂.eq_def]
  rfl



end

end SphereSixComplex.Geometry.EllipticLogarithmicGauge
