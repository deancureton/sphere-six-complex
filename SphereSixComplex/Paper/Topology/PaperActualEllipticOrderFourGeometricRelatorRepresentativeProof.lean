module

public import SphereSixComplex.Paper.Topology.PaperActualEllipticOrderFourBaseFreeHomotopyProof
public import SphereSixComplex.Paper.Topology.PaperActualEllipticCentralCoverProductLiftComparison

@[expose] public section

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex
open SphereSixComplex.LatticeData
open SphereSixComplex.Topology
open SphereSixComplex.Geometry
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open SphereSixComplex.Geometry.GlobalTorusFamily

variable (A : PaperAnalyticData)

/-- The fixed order-four fibre coordinate of the complete filling loop before removing the
constant collar offset. -/
public noncomputable def orderFourPrincipalGaugeWithOffsetMap :
    letI := A.ellipticFourBoundaryAction
    C(unitInterval,
      AdditiveTorus
        (parameterMap A.periods
          A.modular.modularParameter.toTriangleUniformization.zTwo).1) := by
  let _ := A.ellipticFourBoundaryAction
  exact
    { toFun := fun t ↦ A.orderFourFillingRelationPrincipalGaugeLoop t +
        Quotient.mk _ A.ellipticFourBoundaryBase.2.2
      continuous_toFun := by fun_prop }




/-- The zero-section lift of the actual order-four base-coordinate loop. -/
public noncomputable def orderFourZeroSectionBaseMap :
    C(unitInterval, A.CentralFamily) :=
  A.markedBaseToCentralZeroSection.comp A.orderFourFillingRelationBaseCoordinateMap

/-- The zero-section lift of the standard positive four-turn one meridian. -/
public noncomputable def orderFourZeroSectionQuadruplePath :
    Path (A.centralZeroSection A.markedPuncturedBasepoint)
      (A.centralZeroSection A.markedPuncturedBasepoint) :=
  twicePuncturedCounterclockwiseOneQuadruple.map
    A.markedBaseToCentralZeroSection.continuous


/-- The lifted positive four-turn circle is the fourth power of the inverse marked central
one-meridian. -/
public theorem orderFourZeroSectionQuadruplePath_class :
    Path.Homotopic.Quotient.mk A.orderFourZeroSectionQuadruplePath =
      A.markedOneCentralMeridianClass⁻¹ ^ 4 := by
  have h := congrArg
    (FundamentalGroup.map A.markedBaseToCentralZeroSection
      twicePuncturedComplexBasepoint)
    twicePuncturedCounterclockwiseOneQuadruple_class
  rw [map_pow, map_inv, A.markedBaseToCentralZeroSection_map_one] at h
  change (Path.Homotopic.Quotient.mk
      twicePuncturedCounterclockwiseOneQuadruple).map
        A.markedBaseToCentralZeroSection = _ at h
  rw [← Path.Homotopic.Quotient.mk_map] at h
  exact h

/-- Rebase the lifted four-turn zero-section circle at the selected actual cusp point. -/
public noncomputable def ellipticFourCuspZeroSectionQuadruplePath :
    Path A.cuspCentralBase A.cuspCentralBase :=
  A.cuspMarkedCentralWhisker.symm.trans
    (A.orderFourZeroSectionQuadruplePath.trans A.cuspMarkedCentralWhisker)

/-- At the actual cusp basepoint, the zero-section part is the fourth power of the geometric
second central meridian. -/
public theorem ellipticFourCuspZeroSectionQuadruplePath_class :
    Path.Homotopic.Quotient.mk A.ellipticFourCuspZeroSectionQuadruplePath =
      A.geometricCentralRhoTwo ^ 4 := by
  have h := congrArg A.markedCentralToActualCuspEquiv
    A.orderFourZeroSectionQuadruplePath_class
  rw [map_pow] at h
  exact h

/-- The straight vector-cover segment with the same period endpoint as the order-four
principal gauge. -/
public noncomputable def orderFourPrincipalGaugeStraightLiftPath :
    letI := A.ellipticFourBoundaryAction
    Path (A.orderFourFillingRelationPrincipalGaugeCoverLift 0)
      (A.orderFourFillingRelationPrincipalGaugeDeck •
        A.orderFourFillingRelationPrincipalGaugeCoverLift 0) := by
  let _ := A.ellipticFourBoundaryAction
  exact Path.segment _ _

/-- The fixed-fibre loop obtained by projecting the straight negative-epsilon-prime period
segment. -/
public noncomputable def orderFourPrincipalGaugeStraightLoop :
    letI := A.ellipticFourBoundaryAction
    Path
      (torusProjection
        (parameterMap A.periods
          A.modular.modularParameter.toTriangleUniformization.zTwo).1
        (A.orderFourFillingRelationPrincipalGaugeCoverLift 0))
      (torusProjection
        (parameterMap A.periods
          A.modular.modularParameter.toTriangleUniformization.zTwo).1
        (A.orderFourFillingRelationPrincipalGaugeCoverLift 0)) := by
  let _ := A.ellipticFourBoundaryAction
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
    A.orderFourPrincipalGaugeStraightLiftPath

/-- The analytic principal gauge and the literal straight negative-epsilon-prime period loop
have the same fixed-torus path class. -/
public theorem orderFourFillingRelationPrincipalGaugeLoop_class_eq_straight :
    letI := A.ellipticFourBoundaryAction
    pathLoopClass A.orderFourFillingRelationPrincipalGaugeLoop =
      pathLoopClass A.orderFourPrincipalGaugeStraightLoop := by
  let _ := A.ellipticFourBoundaryAction
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
  let e : (torusProjection
      (parameterMap A.periods
        A.modular.modularParameter.toTriangleUniformization.zTwo).1) ⁻¹'
        {torusProjection
          (parameterMap A.periods
            A.modular.modularParameter.toTriangleUniformization.zTwo).1
          (A.orderFourFillingRelationPrincipalGaugeCoverLift 0)} :=
    ⟨A.orderFourFillingRelationPrincipalGaugeCoverLift 0, rfl⟩
  apply (hp.fundamentalGroupEquiv e).injective
  change hp.fundamentalGroupToMulOpposite e
      (pathLoopClass A.orderFourFillingRelationPrincipalGaugeLoop) =
    hp.fundamentalGroupToMulOpposite e
      (pathLoopClass A.orderFourPrincipalGaugeStraightLoop)
  rw [A.orderFourFillingRelationPrincipalGaugeLoop_classification]
  exact (fundamentalGroupToMulOpposite_projectedQuotientDeckPath hp
    (A.orderFourFillingRelationPrincipalGaugeCoverLift 0)
    A.orderFourFillingRelationPrincipalGaugeDeck
    A.orderFourPrincipalGaugeStraightLiftPath).symm







end SphereSixComplex.Geometry.PaperAnalyticData

end

end
