module

public import SphereSixComplex.Paper.Topology.PaperActualEllipticOrderThreeBaseFreeHomotopyProof
public import SphereSixComplex.Paper.Topology.PaperActualEllipticCentralCoverProductLiftComparison

@[expose] public section

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex.Topology
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.EllipticFamilySpecialization

variable (A : PaperAnalyticData)

/-- The fixed order-three fibre coordinate of the complete filling loop before removing the
constant collar offset. -/
public noncomputable def orderThreePrincipalGaugeWithOffsetMap :
    letI := A.ellipticThreeBoundaryAction
    C(unitInterval,
      AdditiveTorus
        (parameterMap A.periods
          A.modular.modularParameter.toTriangleUniformization.zOne).1) := by
  let _ := A.ellipticThreeBoundaryAction
  exact
    { toFun := fun t ↦ A.orderThreeFillingRelationPrincipalGaugeLoop t +
        Quotient.mk _ A.ellipticThreeBoundaryBase.2.2
      continuous_toFun := by fun_prop }




end SphereSixComplex.Geometry.PaperAnalyticData

end

end
