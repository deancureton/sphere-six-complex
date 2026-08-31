module

public import SphereSixComplex.Topology.PaperActualAffineFillingCoverModelsProof
public import SphereSixComplex.Topology.PaperActualEllipticStraightLoopGeometricConnectorReduction

/-!
# Explicit representatives for the inverse elliptic collar charts
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex
open SphereSixComplex.CyclicAngularFundamentalDomain
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.EquivariantQuotientHomeomorph
open SphereSixComplex.Geometry.EllipticPuncturedCollarGaugeHomeomorph
open SphereSixComplex.Geometry.EllipticLinearCollarGlobalDescent
open SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.TriangleGroup
open SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination

variable (A : PaperAnalyticData)

public noncomputable def orderThreeCollarInverseRepresentative
    (q : OpenRadialInterval A.starSeparation.orderThree.radius ×
      (ℝ × ComplexTwoSpace)) :
    (orderThreeAffinePuncturedCarrier A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction
      A.starSeparation.orderThree.radius).carrier := by
  let D := orderThreeCyclicPuncturedProductData A.periods
    A.starSeparation.orderThree.radius A.starSeparation.orderThree.radius_pos
    A.starSeparation.orderThree.radius_lt_one
  let e := orderThreePuncturedProductEquivariantHomeomorph A.periods
    A.modular.modularParameter.toTriangleUniformization_sourceAction
    A.starSeparation.orderThree.radius A.starSeparation.orderThree.radius_pos
    A.starSeparation.orderThree.radius_lt_one
  let w : OpenRadialInterval A.starSeparation.orderThree.radius ×
      (ℝ × A.orderThreeTorus) := (q.1, q.2.1, Quotient.mk _ q.2.2)
  let y : D.carrier.carrier :=
    (Homeomorph.setCongr (show D.carrier.carrier =
      puncturedProduct A.orderThreeTorus A.starSeparation.orderThree.radius from rfl)).symm
      (angularCover (T := A.orderThreeTorus) 3 D.radius_lt_one.le w)
  exact e.toHomeomorph.symm y

public noncomputable def orderFourCollarInverseRepresentative
    (q : OpenRadialInterval A.starSeparation.orderFour.radius ×
      (ℝ × ComplexTwoSpace)) :
    (orderFourAffinePuncturedCarrier A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction
      A.starSeparation.orderFour.radius).carrier := by
  let D := orderFourCyclicPuncturedProductData A.periods
    A.starSeparation.orderFour.radius A.starSeparation.orderFour.radius_pos
    A.starSeparation.orderFour.radius_lt_one
  let e := orderFourPuncturedProductEquivariantHomeomorph A.periods
    A.modular.modularParameter.toTriangleUniformization_sourceAction
    A.starSeparation.orderFour.radius A.starSeparation.orderFour.radius_pos
    A.starSeparation.orderFour.radius_lt_one
  let w : OpenRadialInterval A.starSeparation.orderFour.radius ×
      (ℝ × A.orderFourTorus) := (q.1, q.2.1, Quotient.mk _ q.2.2)
  let y : D.carrier.carrier :=
    (Homeomorph.setCongr (show D.carrier.carrier =
      puncturedProduct A.orderFourTorus A.starSeparation.orderFour.radius from rfl)).symm
      (angularCover (T := A.orderFourTorus) 4 D.radius_lt_one.le w)
  exact e.toHomeomorph.symm y

public theorem orderThreePuncturedProductHomeomorph_inverseRepresentative
    (q : OpenRadialInterval A.starSeparation.orderThree.radius ×
      (ℝ × ComplexTwoSpace)) :
    let D := orderThreeCyclicPuncturedProductData A.periods
      A.starSeparation.orderThree.radius A.starSeparation.orderThree.radius_pos
      A.starSeparation.orderThree.radius_lt_one
    let e := orderThreePuncturedProductEquivariantHomeomorph A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction
      A.starSeparation.orderThree.radius A.starSeparation.orderThree.radius_pos
      A.starSeparation.orderThree.radius_lt_one
    let w : OpenRadialInterval A.starSeparation.orderThree.radius ×
        (ℝ × A.orderThreeTorus) := (q.1, q.2.1, Quotient.mk _ q.2.2)
    e.toHomeomorph (A.orderThreeCollarInverseRepresentative q) =
      (Homeomorph.setCongr (show D.carrier.carrier =
        puncturedProduct A.orderThreeTorus A.starSeparation.orderThree.radius from rfl)).symm
        (angularCover (T := A.orderThreeTorus) 3 D.radius_lt_one.le w) := by
  dsimp only
  unfold orderThreeCollarInverseRepresentative
  exact (orderThreePuncturedProductEquivariantHomeomorph A.periods
    A.modular.modularParameter.toTriangleUniformization_sourceAction
    A.starSeparation.orderThree.radius A.starSeparation.orderThree.radius_pos
    A.starSeparation.orderThree.radius_lt_one).toHomeomorph.apply_symm_apply _

public theorem orderFourPuncturedProductHomeomorph_inverseRepresentative
    (q : OpenRadialInterval A.starSeparation.orderFour.radius ×
      (ℝ × ComplexTwoSpace)) :
    let D := orderFourCyclicPuncturedProductData A.periods
      A.starSeparation.orderFour.radius A.starSeparation.orderFour.radius_pos
      A.starSeparation.orderFour.radius_lt_one
    let e := orderFourPuncturedProductEquivariantHomeomorph A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction
      A.starSeparation.orderFour.radius A.starSeparation.orderFour.radius_pos
      A.starSeparation.orderFour.radius_lt_one
    let w : OpenRadialInterval A.starSeparation.orderFour.radius ×
        (ℝ × A.orderFourTorus) := (q.1, q.2.1, Quotient.mk _ q.2.2)
    e.toHomeomorph (A.orderFourCollarInverseRepresentative q) =
      (Homeomorph.setCongr (show D.carrier.carrier =
        puncturedProduct A.orderFourTorus A.starSeparation.orderFour.radius from rfl)).symm
        (angularCover (T := A.orderFourTorus) 4 D.radius_lt_one.le w) := by
  dsimp only
  unfold orderFourCollarInverseRepresentative
  exact (orderFourPuncturedProductEquivariantHomeomorph A.periods
    A.modular.modularParameter.toTriangleUniformization_sourceAction
    A.starSeparation.orderFour.radius A.starSeparation.orderFour.radius_pos
    A.starSeparation.orderFour.radius_lt_one).toHomeomorph.apply_symm_apply _

public theorem orderThreeCollarInverseRepresentative_fullTurn
    (q : OpenRadialInterval A.starSeparation.orderThree.radius ×
      (ℝ × ComplexTwoSpace)) :
    A.orderThreeCollarInverseRepresentative (q.1, q.2.1 + 3, q.2.2) =
      A.orderThreeCollarInverseRepresentative q := by
  unfold orderThreeCollarInverseRepresentative
  apply congrArg (orderThreePuncturedProductEquivariantHomeomorph A.periods
    A.modular.modularParameter.toTriangleUniformization_sourceAction
    A.starSeparation.orderThree.radius A.starSeparation.orderThree.radius_pos
    A.starSeparation.orderThree.radius_lt_one).toHomeomorph.symm
  apply Subtype.ext
  exact congrArg Subtype.val (angularCover_fullTurn 3
    A.starSeparation.orderThree.radius_lt_one.le
    (q.1, q.2.1, Quotient.mk _ q.2.2))

public theorem orderFourCollarInverseRepresentative_fullTurn
    (q : OpenRadialInterval A.starSeparation.orderFour.radius ×
      (ℝ × ComplexTwoSpace)) :
    A.orderFourCollarInverseRepresentative (q.1, q.2.1 + 4, q.2.2) =
      A.orderFourCollarInverseRepresentative q := by
  unfold orderFourCollarInverseRepresentative
  apply congrArg (orderFourPuncturedProductEquivariantHomeomorph A.periods
    A.modular.modularParameter.toTriangleUniformization_sourceAction
    A.starSeparation.orderFour.radius A.starSeparation.orderFour.radius_pos
    A.starSeparation.orderFour.radius_lt_one).toHomeomorph.symm
  apply Subtype.ext
  exact congrArg Subtype.val (angularCover_fullTurn 4
    A.starSeparation.orderFour.radius_lt_one.le
    (q.1, q.2.1, Quotient.mk _ q.2.2))

public theorem regularFamilyInclusion_orderThreeCollarInverseRepresentative
    (q : OpenRadialInterval A.starSeparation.orderThree.radius ×
      (ℝ × ComplexTwoSpace)) :
    regularFamilyInclusion A.periods
        (orderThreeCollarToRegular A.periods
          (sourceActionProperlyDiscontinuous_of_eq
            A.modular.modularParameter.toTriangleUniformization_sourceAction)
          A.starSeparation.orderThree.sourceData
          (orderThreePuncturedCollarGaugeEquiv A.periods
            A.starSeparation.orderThree.radius
            (A.orderThreeCollarInverseRepresentative q))) =
      orderThreePrincipalGaugeEquiv A.periods
        (A.orderThreeCollarInverseRepresentative q).1 := by
  rw [regularFamilyInclusion_orderThreeCollarToRegular]
  rfl

public theorem regularFamilyInclusion_orderFourCollarInverseRepresentative
    (q : OpenRadialInterval A.starSeparation.orderFour.radius ×
      (ℝ × ComplexTwoSpace)) :
    regularFamilyInclusion A.periods
        (orderFourCollarToRegular A.periods
          (sourceActionProperlyDiscontinuous_of_eq
            A.modular.modularParameter.toTriangleUniformization_sourceAction)
          A.starSeparation.orderFour.sourceData
          (orderFourPuncturedCollarGaugeEquiv A.periods
            A.starSeparation.orderFour.radius
            (A.orderFourCollarInverseRepresentative q))) =
      orderFourPrincipalGaugeEquiv A.periods
        (A.orderFourCollarInverseRepresentative q).1 := by
  rw [regularFamilyInclusion_orderFourCollarToRegular]
  rfl

public theorem orderThreeCollarRadialMappingTorusHomeomorph_symm_apply_liftProjection
    (q : OpenRadialInterval A.starSeparation.orderThree.radius ×
      (ℝ × ComplexTwoSpace)) :
    A.orderThreeCollarRadialMappingTorusHomeomorph.symm
        (q.1, orderThreeAffineMappingTorusLiftProjection A.periods q.2) =
      Quotient.mk _ (A.orderThreeCollarInverseRepresentative q) := by
  let D := orderThreeCyclicPuncturedProductData A.periods
    A.starSeparation.orderThree.radius A.starSeparation.orderThree.radius_pos
    A.starSeparation.orderThree.radius_lt_one
  let e := orderThreePuncturedProductEquivariantHomeomorph A.periods
    A.modular.modularParameter.toTriangleUniformization_sourceAction
    A.starSeparation.orderThree.radius A.starSeparation.orderThree.radius_pos
    A.starSeparation.orderThree.radius_lt_one
  let hprod := restrictedOrbitQuotientHomeomorph e
  let hang := EstablishedCyclicAngularFundamentalDomain.quotientHomeomorphRadialMappingTorus D
    orderThreeMultiplier_eq_standardMultiplier
  let w : OpenRadialInterval A.starSeparation.orderThree.radius ×
      (ℝ × A.orderThreeTorus) := (q.1, q.2.1, Quotient.mk _ q.2.2)
  let y : D.carrier.carrier :=
    (Homeomorph.setCongr (show D.carrier.carrier =
      puncturedProduct A.orderThreeTorus A.starSeparation.orderThree.radius from rfl)).symm
      (angularCover (T := A.orderThreeTorus) 3 D.radius_lt_one.le w)
  change (hprod.trans hang).symm
      (q.1, orderThreeAffineMappingTorusLiftProjection A.periods q.2) = _
  rw [Homeomorph.symm_apply_eq]
  change (q.1, orderThreeAffineMappingTorusLiftProjection A.periods q.2) =
    hang (hprod (Quotient.mk _ (A.orderThreeCollarInverseRepresentative q)))
  rw [restrictedOrbitQuotientHomeomorph_mk]
  change (q.1, orderThreeAffineMappingTorusLiftProjection A.periods q.2) =
    hang (Quotient.mk _ (e.toHomeomorph (A.orderThreeCollarInverseRepresentative q)))
  rw [show e.toHomeomorph (A.orderThreeCollarInverseRepresentative q) = y by
    unfold orderThreeCollarInverseRepresentative
    exact e.toHomeomorph.apply_symm_apply y]
  exact (A.orderThreeAngularQuotientHomeomorph_apply q).symm

public theorem orderFourCollarRadialMappingTorusHomeomorph_symm_apply_liftProjection
    (q : OpenRadialInterval A.starSeparation.orderFour.radius ×
      (ℝ × ComplexTwoSpace)) :
    A.orderFourCollarRadialMappingTorusHomeomorph.symm
        (q.1, orderFourAffineMappingTorusLiftProjection A.periods q.2) =
      Quotient.mk _ (A.orderFourCollarInverseRepresentative q) := by
  let D := orderFourCyclicPuncturedProductData A.periods
    A.starSeparation.orderFour.radius A.starSeparation.orderFour.radius_pos
    A.starSeparation.orderFour.radius_lt_one
  let e := orderFourPuncturedProductEquivariantHomeomorph A.periods
    A.modular.modularParameter.toTriangleUniformization_sourceAction
    A.starSeparation.orderFour.radius A.starSeparation.orderFour.radius_pos
    A.starSeparation.orderFour.radius_lt_one
  let hprod := restrictedOrbitQuotientHomeomorph e
  let hang := EstablishedCyclicAngularFundamentalDomain.quotientHomeomorphRadialMappingTorus D
    orderFourMultiplier_eq_standardMultiplier
  let w : OpenRadialInterval A.starSeparation.orderFour.radius ×
      (ℝ × A.orderFourTorus) := (q.1, q.2.1, Quotient.mk _ q.2.2)
  let y : D.carrier.carrier :=
    (Homeomorph.setCongr (show D.carrier.carrier =
      puncturedProduct A.orderFourTorus A.starSeparation.orderFour.radius from rfl)).symm
      (angularCover (T := A.orderFourTorus) 4 D.radius_lt_one.le w)
  change (hprod.trans hang).symm
      (q.1, orderFourAffineMappingTorusLiftProjection A.periods q.2) = _
  rw [Homeomorph.symm_apply_eq]
  change (q.1, orderFourAffineMappingTorusLiftProjection A.periods q.2) =
    hang (hprod (Quotient.mk _ (A.orderFourCollarInverseRepresentative q)))
  rw [restrictedOrbitQuotientHomeomorph_mk]
  change (q.1, orderFourAffineMappingTorusLiftProjection A.periods q.2) =
    hang (Quotient.mk _ (e.toHomeomorph (A.orderFourCollarInverseRepresentative q)))
  rw [show e.toHomeomorph (A.orderFourCollarInverseRepresentative q) = y by
    unfold orderFourCollarInverseRepresentative
    exact e.toHomeomorph.apply_symm_apply y]
  exact (A.orderFourAngularQuotientHomeomorph_apply q).symm

public theorem orderThreeActualEllipticBoundaryDeckStraightCentralLoop_apply_explicit
    (g : OrderThreeAffineMappingTorusDeck A.periods) (t : unitInterval) :
    letI := orderThreeAffineMappingTorusDeckAction A.periods
    letI := A.orderThreeActualEllipticBoundaryAction
    let q : OpenRadialInterval A.starSeparation.orderThree.radius ×
        (ℝ × ComplexTwoSpace) :=
      (A.orderThreeActualEllipticBoundaryBase.1,
        Path.segment A.orderThreeActualEllipticBoundaryBase.2
          (g • A.orderThreeActualEllipticBoundaryBase.2) t)
    A.orderThreeActualEllipticBoundaryDeckStraightCentralLoop g t =
      A.centralQuotientProjection
        (orderThreeCollarToRegular A.periods
          (sourceActionProperlyDiscontinuous_of_eq
            A.modular.modularParameter.toTriangleUniformization_sourceAction)
          A.starSeparation.orderThree.sourceData
          (orderThreePuncturedCollarGaugeEquiv A.periods
            A.starSeparation.orderThree.radius
            (A.orderThreeCollarInverseRepresentative q))) := by
  let _ := orderThreeAffineMappingTorusDeckAction A.periods
  let _ := A.orderThreeActualEllipticBoundaryAction
  let q : OpenRadialInterval A.starSeparation.orderThree.radius ×
      (ℝ × ComplexTwoSpace) :=
    (A.orderThreeActualEllipticBoundaryBase.1,
      Path.segment A.orderThreeActualEllipticBoundaryBase.2
        (g • A.orderThreeActualEllipticBoundaryBase.2) t)
  change A.orderThreeActualEllipticBoundaryDeckStraightCentralLoop g t =
    A.centralQuotientProjection
      (orderThreeCollarToRegular A.periods
        (sourceActionProperlyDiscontinuous_of_eq
          A.modular.modularParameter.toTriangleUniformization_sourceAction)
        A.starSeparation.orderThree.sourceData
        (orderThreePuncturedCollarGaugeEquiv A.periods
          A.starSeparation.orderThree.radius
          (A.orderThreeCollarInverseRepresentative q)))
  calc
    _ = A.starToCentral 1
        (A.orderThreeCollarRadialMappingTorusHomeomorph.symm
          (q.1, orderThreeAffineMappingTorusLiftProjection A.periods q.2)) :=
      A.orderThreeActualEllipticBoundaryDeckStraightCentralLoop_apply_segment g t
    _ = A.starToCentral 1
        (Quotient.mk _ (A.orderThreeCollarInverseRepresentative q)) :=
      congrArg (A.starToCentral 1)
        (A.orderThreeCollarRadialMappingTorusHomeomorph_symm_apply_liftProjection q)
    _ = _ := A.orderThreeStarToCentral_mk (A.orderThreeCollarInverseRepresentative q)

public theorem orderFourActualEllipticBoundaryDeckStraightCentralLoop_apply_explicit
    (g : OrderFourAffineMappingTorusDeck A.periods) (t : unitInterval) :
    letI := orderFourAffineMappingTorusDeckAction A.periods
    letI := A.orderFourActualEllipticBoundaryAction
    let q : OpenRadialInterval A.starSeparation.orderFour.radius ×
        (ℝ × ComplexTwoSpace) :=
      (A.orderFourActualEllipticBoundaryBase.1,
        Path.segment A.orderFourActualEllipticBoundaryBase.2
          (g • A.orderFourActualEllipticBoundaryBase.2) t)
    A.orderFourActualEllipticBoundaryDeckStraightCentralLoop g t =
      A.centralQuotientProjection
        (orderFourCollarToRegular A.periods
          (sourceActionProperlyDiscontinuous_of_eq
            A.modular.modularParameter.toTriangleUniformization_sourceAction)
          A.starSeparation.orderFour.sourceData
          (orderFourPuncturedCollarGaugeEquiv A.periods
            A.starSeparation.orderFour.radius
            (A.orderFourCollarInverseRepresentative q))) := by
  let _ := orderFourAffineMappingTorusDeckAction A.periods
  let _ := A.orderFourActualEllipticBoundaryAction
  let q : OpenRadialInterval A.starSeparation.orderFour.radius ×
      (ℝ × ComplexTwoSpace) :=
    (A.orderFourActualEllipticBoundaryBase.1,
      Path.segment A.orderFourActualEllipticBoundaryBase.2
        (g • A.orderFourActualEllipticBoundaryBase.2) t)
  change A.orderFourActualEllipticBoundaryDeckStraightCentralLoop g t =
    A.centralQuotientProjection
      (orderFourCollarToRegular A.periods
        (sourceActionProperlyDiscontinuous_of_eq
          A.modular.modularParameter.toTriangleUniformization_sourceAction)
        A.starSeparation.orderFour.sourceData
        (orderFourPuncturedCollarGaugeEquiv A.periods
          A.starSeparation.orderFour.radius
          (A.orderFourCollarInverseRepresentative q)))
  calc
    _ = A.starToCentral 2
        (A.orderFourCollarRadialMappingTorusHomeomorph.symm
          (q.1, orderFourAffineMappingTorusLiftProjection A.periods q.2)) :=
      A.orderFourActualEllipticBoundaryDeckStraightCentralLoop_apply_segment g t
    _ = A.starToCentral 2
        (Quotient.mk _ (A.orderFourCollarInverseRepresentative q)) :=
      congrArg (A.starToCentral 2)
        (A.orderFourCollarRadialMappingTorusHomeomorph_symm_apply_liftProjection q)
    _ = _ := A.orderFourStarToCentral_mk (A.orderFourCollarInverseRepresentative q)

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
