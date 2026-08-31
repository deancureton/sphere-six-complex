module

public import SphereSixComplex.Topology.PaperEllipticPrincipalGaugeWindingProof
public import SphereSixComplex.Topology.PaperActualEllipticRelatorNormalClosure

/-!
# Classification of the principal-gauge winding in the elliptic filling relations
-/

@[expose] public section

noncomputable section

open Set Topology

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex
open SphereSixComplex.LatticeData
open SphereSixComplex.Periods
open SphereSixComplex.Geometry
open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open SphereSixComplex.Geometry.EllipticWholeFiberCompactCover
open SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.Geometry.TorusFamily

variable (A : PaperAnalyticData)

/-- The fixed order-three period-lattice element detected by the principal gauge. -/
public def orderThreeFillingRelationPrincipalGaugeDeck :
    PeriodGroup
      (parameterMap A.periods
        A.modular.modularParameter.toTriangleUniformization.zOne).1 :=
  Multiplicative.ofAdd
    ⟨periodVector
        (parameterMap A.periods
          A.modular.modularParameter.toTriangleUniformization.zOne).1 epsilon,
      ⟨epsilon, rfl⟩⟩

/-- The fixed order-four period-lattice element detected by the principal gauge. -/
public def orderFourFillingRelationPrincipalGaugeDeck :
    PeriodGroup
      (parameterMap A.periods
        A.modular.modularParameter.toTriangleUniformization.zTwo).1 :=
  Multiplicative.ofAdd
    ⟨periodVector
        (parameterMap A.periods
          A.modular.modularParameter.toTriangleUniformization.zTwo).1 (-epsilon'),
      ⟨-epsilon', rfl⟩⟩

@[simp]
public theorem orderThreeFillingRelationPrincipalGaugeDeck_smul (z : ComplexTwoSpace) :
    A.orderThreeFillingRelationPrincipalGaugeDeck • z =
      periodVector
          (parameterMap A.periods
            A.modular.modularParameter.toTriangleUniformization.zOne).1 epsilon + z :=
  rfl

@[simp]
public theorem orderFourFillingRelationPrincipalGaugeDeck_smul (z : ComplexTwoSpace) :
    A.orderFourFillingRelationPrincipalGaugeDeck • z =
      periodVector
          (parameterMap A.periods
            A.modular.modularParameter.toTriangleUniformization.zTwo).1 (-epsilon') + z :=
  rfl

/-- The explicit order-three gauge lift, regarded as a path to its lattice translate. -/
public noncomputable def orderThreeFillingRelationPrincipalGaugeLiftPath :
    letI := A.orderThreeActualEllipticBoundaryAction
    Path (A.orderThreeFillingRelationPrincipalGaugeCoverLift 0)
      (A.orderThreeFillingRelationPrincipalGaugeDeck •
        A.orderThreeFillingRelationPrincipalGaugeCoverLift 0) := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  exact
    { toFun := A.orderThreeFillingRelationPrincipalGaugeCoverLiftMap
      continuous_toFun := A.orderThreeFillingRelationPrincipalGaugeCoverLiftMap.continuous
      source' := rfl
      target' := by
        change A.orderThreeFillingRelationPrincipalGaugeCoverLift 1 = _
        rw [A.orderThreeFillingRelationPrincipalGaugeCoverLift_endpoint]
        rfl }

/-- The explicit order-four gauge lift, regarded as a path to its lattice translate. -/
public noncomputable def orderFourFillingRelationPrincipalGaugeLiftPath :
    letI := A.orderFourActualEllipticBoundaryAction
    Path (A.orderFourFillingRelationPrincipalGaugeCoverLift 0)
      (A.orderFourFillingRelationPrincipalGaugeDeck •
        A.orderFourFillingRelationPrincipalGaugeCoverLift 0) := by
  let _ := A.orderFourActualEllipticBoundaryAction
  exact
    { toFun := A.orderFourFillingRelationPrincipalGaugeCoverLiftMap
      continuous_toFun := A.orderFourFillingRelationPrincipalGaugeCoverLiftMap.continuous
      source' := rfl
      target' := by
        change A.orderFourFillingRelationPrincipalGaugeCoverLift 1 = _
        rw [A.orderFourFillingRelationPrincipalGaugeCoverLift_endpoint]
        rfl }

/-- The order-three gauge winding as a based loop in the fixed torus fibre. -/
public noncomputable def orderThreeFillingRelationPrincipalGaugeLoop :
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
    A.orderThreeFillingRelationPrincipalGaugeLiftPath

/-- The order-four gauge winding as a based loop in the fixed torus fibre. -/
public noncomputable def orderFourFillingRelationPrincipalGaugeLoop :
    letI := A.orderFourActualEllipticBoundaryAction
    Path
      (torusProjection
        (parameterMap A.periods
          A.modular.modularParameter.toTriangleUniformization.zTwo).1
        (A.orderFourFillingRelationPrincipalGaugeCoverLift 0))
      (torusProjection
        (parameterMap A.periods
          A.modular.modularParameter.toTriangleUniformization.zTwo).1
        (A.orderFourFillingRelationPrincipalGaugeCoverLift 0)) := by
  let _ := A.orderFourActualEllipticBoundaryAction
  let _ : ProperlyDiscontinuousSMul
      (PeriodGroup
        (parameterMap A.periods
          A.modular.modularParameter.toTriangleUniformization.zTwo).1)
      ComplexTwoSpace :=
    periodLattice_properlyDiscontinuousSMul
      (FullRank.ofSetupInequalities _
        (parameterMap A.periods
          A.modular.modularParameter.toTriangleUniformization.zTwo).2)
  let hp : IsQuotientCoveringMap
      (torusProjection
        (parameterMap A.periods
          A.modular.modularParameter.toTriangleUniformization.zTwo).1)
      (PeriodGroup
        (parameterMap A.periods
          A.modular.modularParameter.toTriangleUniformization.zTwo).1) :=
    isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul
  exact projectedQuotientDeckPath hp
    (A.orderFourFillingRelationPrincipalGaugeCoverLift 0)
    A.orderFourFillingRelationPrincipalGaugeDeck
    A.orderFourFillingRelationPrincipalGaugeLiftPath

public theorem orderThreeFillingRelationPrincipalGaugeLoop_apply (t : unitInterval) :
    letI := A.orderThreeActualEllipticBoundaryAction
    A.orderThreeFillingRelationPrincipalGaugeLoop t =
      A.orderThreePrincipalRealPeriodGauge
        (familyTotalSpaceBase A.periods
          (A.orderThreeCollarInverseRepresentative
            (A.orderThreeActualEllipticBoundaryDeckStraightLift
              A.orderThreeActualEllipticBoundaryDeckData.fillingRelation t)).1) := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  change torusProjection
      (parameterMap A.periods
        A.modular.modularParameter.toTriangleUniformization.zOne).1
      (A.orderThreeFillingRelationPrincipalGaugeCoverLift t) = _
  exact A.orderThreeFillingRelationPrincipalGaugeCoverLift_projects t

public theorem orderFourFillingRelationPrincipalGaugeLoop_apply (t : unitInterval) :
    letI := A.orderFourActualEllipticBoundaryAction
    A.orderFourFillingRelationPrincipalGaugeLoop t =
      A.orderFourPrincipalRealPeriodGauge
        (familyTotalSpaceBase A.periods
          (A.orderFourCollarInverseRepresentative
            (A.orderFourActualEllipticBoundaryDeckStraightLift
              A.orderFourActualEllipticBoundaryDeckData.fillingRelation t)).1) := by
  let _ := A.orderFourActualEllipticBoundaryAction
  change torusProjection
      (parameterMap A.periods
        A.modular.modularParameter.toTriangleUniformization.zTwo).1
      (A.orderFourFillingRelationPrincipalGaugeCoverLift t) = _
  exact A.orderFourFillingRelationPrincipalGaugeCoverLift_projects t

/-- The order-three principal gauge has exactly the lattice label `epsilon`. -/
public theorem orderThreeFillingRelationPrincipalGaugeLoop_classification :
    letI := A.orderThreeActualEllipticBoundaryAction
    letI : ProperlyDiscontinuousSMul
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
    hp.fundamentalGroupToMulOpposite
        ⟨A.orderThreeFillingRelationPrincipalGaugeCoverLift 0, rfl⟩
        (pathLoopClass A.orderThreeFillingRelationPrincipalGaugeLoop) =
      MulOpposite.op A.orderThreeFillingRelationPrincipalGaugeDeck := by
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
  exact fundamentalGroupToMulOpposite_projectedQuotientDeckPath hp
    (A.orderThreeFillingRelationPrincipalGaugeCoverLift 0)
    A.orderThreeFillingRelationPrincipalGaugeDeck
    A.orderThreeFillingRelationPrincipalGaugeLiftPath

/-- The order-four principal gauge has exactly the lattice label `-epsilon'`. -/
public theorem orderFourFillingRelationPrincipalGaugeLoop_classification :
    letI := A.orderFourActualEllipticBoundaryAction
    letI : ProperlyDiscontinuousSMul
        (PeriodGroup
          (parameterMap A.periods
            A.modular.modularParameter.toTriangleUniformization.zTwo).1)
        ComplexTwoSpace :=
      periodLattice_properlyDiscontinuousSMul
        (FullRank.ofSetupInequalities _
          (parameterMap A.periods
            A.modular.modularParameter.toTriangleUniformization.zTwo).2)
    let hp : IsQuotientCoveringMap
        (torusProjection
          (parameterMap A.periods
            A.modular.modularParameter.toTriangleUniformization.zTwo).1)
        (PeriodGroup
          (parameterMap A.periods
            A.modular.modularParameter.toTriangleUniformization.zTwo).1) :=
      isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul
    hp.fundamentalGroupToMulOpposite
        ⟨A.orderFourFillingRelationPrincipalGaugeCoverLift 0, rfl⟩
        (pathLoopClass A.orderFourFillingRelationPrincipalGaugeLoop) =
      MulOpposite.op A.orderFourFillingRelationPrincipalGaugeDeck := by
  let _ := A.orderFourActualEllipticBoundaryAction
  let _ : ProperlyDiscontinuousSMul
      (PeriodGroup
        (parameterMap A.periods
          A.modular.modularParameter.toTriangleUniformization.zTwo).1)
      ComplexTwoSpace :=
    periodLattice_properlyDiscontinuousSMul
      (FullRank.ofSetupInequalities _
        (parameterMap A.periods
          A.modular.modularParameter.toTriangleUniformization.zTwo).2)
  let hp : IsQuotientCoveringMap
      (torusProjection
        (parameterMap A.periods
          A.modular.modularParameter.toTriangleUniformization.zTwo).1)
      (PeriodGroup
        (parameterMap A.periods
          A.modular.modularParameter.toTriangleUniformization.zTwo).1) :=
    isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul
  exact fundamentalGroupToMulOpposite_projectedQuotientDeckPath hp
    (A.orderFourFillingRelationPrincipalGaugeCoverLift 0)
    A.orderFourFillingRelationPrincipalGaugeDeck
    A.orderFourFillingRelationPrincipalGaugeLiftPath

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
