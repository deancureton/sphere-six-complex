module

public import SphereSixComplex.Topology.PaperActualEllipticOrderFourGeometricRelatorRepresentativeProof
public import SphereSixComplex.Topology.PaperActualEllipticOrderThreeProductLoopSplittingProof
public import SphereSixComplex.Topology.PaperActualEllipticRelatorFreeHomotopyReduction
public import SphereSixComplex.Topology.PaperSectionSevenAffinePrincipalGaugeRadialBaseSquare

@[expose] public section

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex
open SphereSixComplex.LatticeData
open SphereSixComplex.Periods
open SphereSixComplex.Topology
open SphereSixComplex.TriangleGroup
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.EllipticCayleyHomeomorph
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open SphereSixComplex.Geometry.EllipticLocalCoordinates
open SphereSixComplex.Geometry.EllipticLinearCollarGlobalDescent
open SphereSixComplex.Geometry.EllipticRealPeriodProductTrivialization
open SphereSixComplex.Geometry.EllipticPuncturedCollarGaugeHomeomorph
open SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.Geometry.TorusFamily
open SphereSixComplex.Geometry.EllipticWholeFiberCompactCover
open SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination

variable (A : PaperAnalyticData)

/-- The actual one-turn Cayley circle, retaining its radius bound as a point of the unit disc. -/
public noncomputable def orderFourFillingRelationCayleyDiscLoop :
    Path
      (⟨A.orderFourFillingRelationCayleyBaseValue, by
        rw [A.orderFourFillingRelationCayleyBaseValue_norm]
        exact A.orderFourActualEllipticBoundaryBase.1.2.2.trans
          A.starSeparation.orderFour.radius_lt_one⟩ : ComplexUnitDisc)
      (⟨A.orderFourFillingRelationCayleyBaseValue, by
        rw [A.orderFourFillingRelationCayleyBaseValue_norm]
        exact A.orderFourActualEllipticBoundaryBase.1.2.2.trans
          A.starSeparation.orderFour.radius_lt_one⟩ : ComplexUnitDisc) where
  toFun t := ⟨(A.orderFourFillingRelationCayleyLoop t).1, by
    have hpoint : (A.orderFourFillingRelationCayleyLoop t).1 =
        localDegreeCirclePoint A.orderFourFillingRelationCayleyBaseValue t := by
      simp [orderFourFillingRelationCayleyLoop, puncturedComplexIntegerCircle,
        puncturedComplexIntegerCirclePoint, localDegreeCirclePoint]
    rw [hpoint]
    rw [localDegreeCirclePoint_norm, A.orderFourFillingRelationCayleyBaseValue_norm]
    exact A.orderFourActualEllipticBoundaryBase.1.2.2.trans
      A.starSeparation.orderFour.radius_lt_one⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact A.orderFourFillingRelationCayleyLoop.continuous.subtype_val
  source' := by
    apply Subtype.ext
    change (A.orderFourFillingRelationCayleyLoop 0).1 =
      A.orderFourFillingRelationCayleyBaseValue
    exact congrArg Subtype.val A.orderFourFillingRelationCayleyLoop.source
  target' := by
    apply Subtype.ext
    change (A.orderFourFillingRelationCayleyLoop 1).1 =
      A.orderFourFillingRelationCayleyBaseValue
    exact congrArg Subtype.val A.orderFourFillingRelationCayleyLoop.target

/-- Add the fixed collar offset to the based principal-gauge loop. -/
public noncomputable def orderFourPrincipalGaugeWithOffsetPath :
    letI := A.orderFourActualEllipticBoundaryAction
    Path
      (A.orderFourFillingRelationPrincipalGaugeLoop 0 +
        Quotient.mk _ A.orderFourActualEllipticBoundaryBase.2.2)
      (A.orderFourFillingRelationPrincipalGaugeLoop 0 +
        Quotient.mk _ A.orderFourActualEllipticBoundaryBase.2.2) := by
  let _ := A.orderFourActualEllipticBoundaryAction
  exact
    { toFun := A.orderFourPrincipalGaugeWithOffsetMap
      continuous_toFun := A.orderFourPrincipalGaugeWithOffsetMap.continuous
      source' := rfl
      target' := by
        rw [orderFourPrincipalGaugeWithOffsetMap]
        exact congrArg
          (fun q ↦ q + Quotient.mk _ A.orderFourActualEllipticBoundaryBase.2.2)
          A.orderFourFillingRelationPrincipalGaugeLoop.target }

/-- The full regular filling loop has exactly the Cayley-disc and offset principal-gauge
coordinates, including their subtype data. -/
public theorem orderFourRegularLoop_cayleyGaugeProductCoordinate
    (t : unitInterval) :
    letI := A.orderFourActualEllipticBoundaryAction
    orderFourRealPeriodProductHomeomorph A.periods
        (regularFamilyInclusion A.periods
          (A.orderFourFillingRelationRegularLoop t)) =
      (A.orderFourFillingRelationCayleyDiscLoop t,
        A.orderFourPrincipalGaugeWithOffsetPath t) := by
  let _ := A.orderFourActualEllipticBoundaryAction
  have hcoord := A.orderFourFillingRelationRegularLoop_localProductCoordinate t
  apply Prod.ext
  · apply Subtype.ext
    rw [orderFourRealPeriodProductHomeomorph_fst]
    rw [familyTotalSpaceBase_regularFamilyInclusion]
    let hproper : SourceActionProperlyDiscontinuous
        (U := A.modular.modularParameter.toTriangleUniformization) :=
      sourceActionProperlyDiscontinuous_of_eq
        A.modular.modularParameter.toTriangleUniformization_sourceAction
    let lift := A.orderFourActualEllipticBoundaryDeckStraightLift
      A.orderFourActualEllipticBoundaryDeckData.fillingRelation t
    have hb : (regularTotalSpaceBase A.periods
        (A.orderFourCollarRegularRepresentativeMap lift)).1 =
        familyTotalSpaceBase A.periods
          (A.orderFourCollarInverseRepresentative lift).1 := by
      convert orderFourCollarToRegular_principalGauge_base A.periods hproper
        A.modular.modularParameter.toTriangleUniformization_sourceAction
        A.starSeparation.orderFour.sourceData
        (A.orderFourCollarInverseRepresentative lift) using 1
      all_goals congr 1
    change ((orderFourCayleyHomeomorph
      (regularTotalSpaceBase A.periods
        (A.orderFourFillingRelationRegularLoop t)).1 :
        ComplexUnitDisc) : ℂ) = _
    rw [show A.orderFourFillingRelationRegularLoop t =
      A.orderFourCollarRegularRepresentativeMap lift by rfl]
    rw [hb]
    exact A.orderFourFillingRelationCayleyLoop_apply t
  · change ((orderFourRealPeriodProductHomeomorph A.periods
        (regularFamilyInclusion A.periods
          (A.orderFourFillingRelationRegularLoop t))).2) =
      A.orderFourFillingRelationPrincipalGaugeLoop t +
        Quotient.mk _ A.orderFourActualEllipticBoundaryBase.2.2
    exact congrArg Prod.snd hcoord

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
