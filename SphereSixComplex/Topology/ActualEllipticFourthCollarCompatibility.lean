module
public import SphereSixComplex.Topology.GlobalInvariantPeriodTranslation
public import SphereSixComplex.Topology.ActualEllipticVaryingFourthTranslation
public import SphereSixComplex.Geometry.PaperEllipticCentralEscape

@[expose] public section
noncomputable section
open scoped ContinuousMap
namespace SphereSixComplex.Geometry.PaperAnalyticData
open SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open ComplexTorus TorusFamily AnalyticTorusFamily GlobalTorusFamily
open EllipticVaryingFamilyQuotient EllipticLinearCollarGlobalDescent
open EllipticPuncturedCollarGaugeHomeomorph

public def centralFourthTranslation (A : PaperAnalyticData) :
    C(UnitAddCircle × A.CentralFamily, A.CentralFamily) :=
  invariantPeriodCircleTranslation A.periods ![0,0,0,1] rhoLambda_fourthBasis

public theorem regularFamilyInclusion_fourthTranslation (A : PaperAnalyticData) (t : ℝ)
    (q : RegularTotalSpace A.periods) :
    regularFamilyInclusion A.periods (regularPeriodTranslation A.periods ![0,0,0,1] (t,q)) =
      fourthPeriodFamilyTranslation A.periods t (regularFamilyInclusion A.periods q) := by
  induction q using Quotient.inductionOn with
  | _ p => rfl

public def orderThreeFourthCollarSource (A : PaperAnalyticData) (t : ℝ)
    (q : (orderThreeAffinePuncturedCarrier A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction A.starSeparation.orderThree.radius).carrier) :
    (orderThreeAffinePuncturedCarrier A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction A.starSeparation.orderThree.radius).carrier :=
  ⟨fourthPeriodFamilyTranslation A.periods t q.1, by
    change 0 < orderThreeFamilyRadius A.periods _ ∧ orderThreeFamilyRadius A.periods _ < _
    rw [orderThreeFamilyRadius, fourthPeriodFamilyTranslation,
      familyTotalSpaceBase_familyTranslationMap]
    exact q.property⟩

public def orderFourFourthCollarSource (A : PaperAnalyticData) (t : ℝ)
    (q : (orderFourAffinePuncturedCarrier A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction A.starSeparation.orderFour.radius).carrier) :
    (orderFourAffinePuncturedCarrier A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction A.starSeparation.orderFour.radius).carrier :=
  ⟨fourthPeriodFamilyTranslation A.periods t q.1, by
    change 0 < orderFourFamilyRadius A.periods _ ∧ orderFourFamilyRadius A.periods _ < _
    rw [orderFourFamilyRadius, fourthPeriodFamilyTranslation,
      familyTotalSpaceBase_familyTranslationMap]
    exact q.property⟩

public theorem orderThreeFourthCollarSource_central (A : PaperAnalyticData) (t : ℝ)
    (q : (orderThreeAffinePuncturedCarrier A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction A.starSeparation.orderThree.radius).carrier) :
    A.centralFourthTranslation ((t : UnitAddCircle), A.starToCentral 1 (Quotient.mk _ q)) =
      A.starToCentral 1 (Quotient.mk _ (A.orderThreeFourthCollarSource t q)) := by
  rw [A.orderThreeStarToCentral_mk, A.orderThreeStarToCentral_mk]
  change invariantPeriodCircleTranslation A.periods _ _
    ((t : UnitAddCircle),Quotient.mk _ _) = Quotient.mk _ _
  rw [invariantPeriodCircleTranslation_real, invariantPeriodRealTranslation_mk]
  apply congrArg A.centralQuotientProjection
  apply regularFamilyInclusion_injective A.periods
  rw [A.regularFamilyInclusion_fourthTranslation,
    regularFamilyInclusion_orderThreeCollarToRegular,
    regularFamilyInclusion_orderThreeCollarToRegular]
  exact (orderThreePrincipalGauge_fourthTranslation A.periods t q.1).symm

public theorem orderFourFourthCollarSource_central (A : PaperAnalyticData) (t : ℝ)
    (q : (orderFourAffinePuncturedCarrier A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction A.starSeparation.orderFour.radius).carrier) :
    A.centralFourthTranslation ((t : UnitAddCircle), A.starToCentral 2 (Quotient.mk _ q)) =
      A.starToCentral 2 (Quotient.mk _ (A.orderFourFourthCollarSource t q)) := by
  rw [A.orderFourStarToCentral_mk, A.orderFourStarToCentral_mk]
  change invariantPeriodCircleTranslation A.periods _ _
    ((t : UnitAddCircle),Quotient.mk _ _) = Quotient.mk _ _
  rw [invariantPeriodCircleTranslation_real, invariantPeriodRealTranslation_mk]
  apply congrArg A.centralQuotientProjection
  apply regularFamilyInclusion_injective A.periods
  rw [A.regularFamilyInclusion_fourthTranslation,
    regularFamilyInclusion_orderFourCollarToRegular,
    regularFamilyInclusion_orderFourCollarToRegular]
  exact (orderFourPrincipalGauge_fourthTranslation A.periods t q.1).symm

public theorem orderThreeFourthCollarSource_filling (A : PaperAnalyticData) (t : ℝ)
    (q : (orderThreeAffinePuncturedCarrier A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction A.starSeparation.orderThree.radius).carrier) :
    A.actualOrderThreeFourthTranslation ((t : UnitAddCircle), A.starToFilling 1 (Quotient.mk _ q)) =
      A.starToFilling 1 (Quotient.mk _ (A.orderThreeFourthCollarSource t q)) := by
  change A.actualOrderThreeFourthTranslation ((t : UnitAddCircle),Quotient.mk _ _) = _
  rw [A.actualOrderThreeFourthTranslation_mk]
  rfl

public theorem orderFourFourthCollarSource_filling (A : PaperAnalyticData) (t : ℝ)
    (q : (orderFourAffinePuncturedCarrier A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction A.starSeparation.orderFour.radius).carrier) :
    A.actualOrderFourFourthTranslation ((t : UnitAddCircle), A.starToFilling 2 (Quotient.mk _ q)) =
      A.starToFilling 2 (Quotient.mk _ (A.orderFourFourthCollarSource t q)) := by
  change A.actualOrderFourFourthTranslation ((t : UnitAddCircle),Quotient.mk _ _) = _
  rw [A.actualOrderFourFourthTranslation_mk]
  rfl

end SphereSixComplex.Geometry.PaperAnalyticData
