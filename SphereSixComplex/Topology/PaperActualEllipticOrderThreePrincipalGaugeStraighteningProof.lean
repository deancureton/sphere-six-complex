module

public import SphereSixComplex.Topology.PaperActualEllipticOrderThreeZeroSectionHomotopyProof

@[expose] public section

noncomputable section

open Set Topology

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex.Topology
open SphereSixComplex.Geometry
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.AnalyticTorusFamily

variable (A : PaperAnalyticData)

/-- The straight vector-cover segment with the same period endpoint as the order-three
principal gauge. -/
public noncomputable def orderThreePrincipalGaugeStraightLiftPath :
    letI := A.orderThreeActualEllipticBoundaryAction
    Path (A.orderThreeFillingRelationPrincipalGaugeCoverLift 0)
      (A.orderThreeFillingRelationPrincipalGaugeDeck •
        A.orderThreeFillingRelationPrincipalGaugeCoverLift 0) := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  exact Path.segment _ _

/-- The fixed-fibre loop obtained by projecting the straight `epsilon`-period segment. -/
public noncomputable def orderThreePrincipalGaugeStraightLoop :
    letI := A.orderThreeActualEllipticBoundaryAction
    Path
      (torusProjection
        (parameterMap A.periods
          A.modular.modularParameter.toTriangleUniformization.zOne).1
        (A.orderThreeFillingRelationPrincipalGaugeCoverLift 0))
      (torusProjection
        (parameterMap A.periods
          A.modular.modularParameter.toTriangleUniformization.zOne).1
        (A.orderThreeFillingRelationPrincipalGaugeCoverLift 0)) := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  let _ : ProperlyDiscontinuousSMul
      (PeriodGroup
        (parameterMap A.periods
          A.modular.modularParameter.toTriangleUniformization.zOne).1)
      ComplexTwoSpace :=
    periodLattice_properlyDiscontinuousSMul
      (FullRank.ofSetupInequalities _
        (parameterMap A.periods
          A.modular.modularParameter.toTriangleUniformization.zOne).2)
  let hp : IsQuotientCoveringMap
      (torusProjection
        (parameterMap A.periods
          A.modular.modularParameter.toTriangleUniformization.zOne).1)
      (PeriodGroup
        (parameterMap A.periods
          A.modular.modularParameter.toTriangleUniformization.zOne).1) :=
    isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul
  exact projectedQuotientDeckPath hp
    (A.orderThreeFillingRelationPrincipalGaugeCoverLift 0)
    A.orderThreeFillingRelationPrincipalGaugeDeck
    A.orderThreePrincipalGaugeStraightLiftPath

/-- The analytic principal gauge and the literal straight `epsilon`-period loop have the same
fixed-torus path class. -/
public theorem orderThreeFillingRelationPrincipalGaugeLoop_class_eq_straight :
    letI := A.orderThreeActualEllipticBoundaryAction
    pathLoopClass A.orderThreeFillingRelationPrincipalGaugeLoop =
      pathLoopClass A.orderThreePrincipalGaugeStraightLoop := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  let _ : ProperlyDiscontinuousSMul
      (PeriodGroup
        (parameterMap A.periods
          A.modular.modularParameter.toTriangleUniformization.zOne).1)
      ComplexTwoSpace :=
    periodLattice_properlyDiscontinuousSMul
      (FullRank.ofSetupInequalities _
        (parameterMap A.periods
          A.modular.modularParameter.toTriangleUniformization.zOne).2)
  let hp : IsQuotientCoveringMap
      (torusProjection
        (parameterMap A.periods
          A.modular.modularParameter.toTriangleUniformization.zOne).1)
      (PeriodGroup
        (parameterMap A.periods
          A.modular.modularParameter.toTriangleUniformization.zOne).1) :=
    isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul
  let e : (torusProjection
      (parameterMap A.periods
        A.modular.modularParameter.toTriangleUniformization.zOne).1) ⁻¹'
        {torusProjection
          (parameterMap A.periods
            A.modular.modularParameter.toTriangleUniformization.zOne).1
          (A.orderThreeFillingRelationPrincipalGaugeCoverLift 0)} :=
    ⟨A.orderThreeFillingRelationPrincipalGaugeCoverLift 0, rfl⟩
  apply (hp.fundamentalGroupEquiv e).injective
  change hp.fundamentalGroupToMulOpposite e
      (pathLoopClass A.orderThreeFillingRelationPrincipalGaugeLoop) =
    hp.fundamentalGroupToMulOpposite e
      (pathLoopClass A.orderThreePrincipalGaugeStraightLoop)
  rw [A.orderThreeFillingRelationPrincipalGaugeLoop_classification]
  exact (fundamentalGroupToMulOpposite_projectedQuotientDeckPath hp
    (A.orderThreeFillingRelationPrincipalGaugeCoverLift 0)
    A.orderThreeFillingRelationPrincipalGaugeDeck
    A.orderThreePrincipalGaugeStraightLiftPath).symm

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
