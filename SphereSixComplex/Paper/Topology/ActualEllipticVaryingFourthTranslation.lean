module
public import SphereSixComplex.Paper.Topology.ActualEllipticFourthGaugeCompatibility
public import SphereSixComplex.Paper.Topology.PaperEllipticFillingRealPeriodRadial

@[expose] public section
noncomputable section
open scoped ContinuousMap
namespace SphereSixComplex.Geometry.AnalyticData
open SphereSixComplex.EllipticFilling
open EllipticVaryingFamilyQuotient RealPeriodTrivialization

public def orderThreeFourthFillingHomeomorph (A : AnalyticData) :
    A.OrderThreeVaryingFilling A.starSeparation.orderThree.radius ≃ₜ
      (orderThreeRadialActionData A.periods).FillingQuotient :=
  (orderThreeSelectedAffineRadialCompatibility A).toVaryingFillingProductIdentification.quotientHomeomorph

public def orderFourFourthFillingHomeomorph (A : AnalyticData) :
    A.OrderFourVaryingFilling A.starSeparation.orderFour.radius ≃ₜ
      (orderFourRadialActionData A.periods).FillingQuotient :=
  (orderFourSelectedAffineRadialCompatibility A).toVaryingFillingProductIdentification.quotientHomeomorph

public def actualOrderThreeFourthTranslation (A : AnalyticData) :
    C(UnitAddCircle × A.OrderThreeVaryingFilling A.starSeparation.orderThree.radius,
      A.OrderThreeVaryingFilling A.starSeparation.orderThree.radius) :=
  (A.orderThreeFourthFillingHomeomorph.symm : C(_, _)).comp
    ((orderThreeFourthCircleTranslation A.periods).comp
      ⟨fun z ↦ (z.1,A.orderThreeFourthFillingHomeomorph z.2),
        continuous_fst.prodMk (A.orderThreeFourthFillingHomeomorph.continuous.comp continuous_snd)⟩)

public def actualOrderFourFourthTranslation (A : AnalyticData) :
    C(UnitAddCircle × A.OrderFourVaryingFilling A.starSeparation.orderFour.radius,
      A.OrderFourVaryingFilling A.starSeparation.orderFour.radius) :=
  (A.orderFourFourthFillingHomeomorph.symm : C(_, _)).comp
    ((orderFourFourthCircleTranslation A.periods).comp
      ⟨fun z ↦ (z.1,A.orderFourFourthFillingHomeomorph z.2),
        continuous_fst.prodMk (A.orderFourFourthFillingHomeomorph.continuous.comp continuous_snd)⟩)

public def orderThreeFourthTranslationSource (A : AnalyticData) (t : ℝ)
    (q : A.orderThreeFillingOpen A.starSeparation.orderThree.radius) :
    A.orderThreeFillingOpen A.starSeparation.orderThree.radius :=
  ⟨fourthPeriodFamilyTranslation A.periods t q.1, by
    change orderThreeFamilyRadius A.periods (fourthPeriodFamilyTranslation A.periods t q.1) < _
    rw [orderThreeFamilyRadius, fourthPeriodFamilyTranslation,
      familyTotalSpaceBase_familyTranslationMap]
    exact q.property⟩

public def orderFourFourthTranslationSource (A : AnalyticData) (t : ℝ)
    (q : A.orderFourFillingOpen A.starSeparation.orderFour.radius) :
    A.orderFourFillingOpen A.starSeparation.orderFour.radius :=
  ⟨fourthPeriodFamilyTranslation A.periods t q.1, by
    change orderFourFamilyRadius A.periods (fourthPeriodFamilyTranslation A.periods t q.1) < _
    rw [orderFourFamilyRadius, fourthPeriodFamilyTranslation,
      familyTotalSpaceBase_familyTranslationMap]
    exact q.property⟩

public theorem orderThreeFourthTranslationSource_chart (A : AnalyticData) (t : ℝ)
    (q : A.orderThreeFillingOpen A.starSeparation.orderThree.radius) :
    (orderThreeSelectedAffineRadialCompatibility A).toVaryingFillingProductIdentification.toHomeomorph
      (A.orderThreeFourthTranslationSource t q) =
      (((orderThreeSelectedAffineRadialCompatibility A).toVaryingFillingProductIdentification.toHomeomorph q).1,
        fourthPeriodCircle (AnalyticTorusFamily.parameterMap A.periods
          A.modular.modularParameter.toTriangleUniformization.zOne) (t : UnitAddCircle) +
        ((orderThreeSelectedAffineRadialCompatibility A).toVaryingFillingProductIdentification.toHomeomorph q).2) := by
  apply Prod.ext
  · apply Subtype.ext
    change (orderThreeFillingProductMap A _ (A.orderThreeFourthTranslationSource t q)).1.1 / _ =
      (orderThreeFillingProductMap A _ q).1.1 / _
    congr 1
    change ((orderThreeRealPeriodProductHomeomorph A.periods
      (fourthPeriodFamilyTranslation A.periods t q.1)).1 : ℂ) =
      ((orderThreeRealPeriodProductHomeomorph A.periods q.1).1 : ℂ)
    rw [orderThreeRealPeriodProductHomeomorph_fst, orderThreeRealPeriodProductHomeomorph_fst,
      fourthPeriodFamilyTranslation, familyTotalSpaceBase_familyTranslationMap]
  · exact orderThreeRealPeriodProductHomeomorph_fourthTranslation A.periods t q.1

public theorem orderFourFourthTranslationSource_chart (A : AnalyticData) (t : ℝ)
    (q : A.orderFourFillingOpen A.starSeparation.orderFour.radius) :
    (orderFourSelectedAffineRadialCompatibility A).toVaryingFillingProductIdentification.toHomeomorph
      (A.orderFourFourthTranslationSource t q) =
      (((orderFourSelectedAffineRadialCompatibility A).toVaryingFillingProductIdentification.toHomeomorph q).1,
        fourthPeriodCircle (AnalyticTorusFamily.parameterMap A.periods
          A.modular.modularParameter.toTriangleUniformization.zTwo) (t : UnitAddCircle) +
        ((orderFourSelectedAffineRadialCompatibility A).toVaryingFillingProductIdentification.toHomeomorph q).2) := by
  apply Prod.ext
  · apply Subtype.ext
    change (orderFourFillingProductMap A _ (A.orderFourFourthTranslationSource t q)).1.1 / _ =
      (orderFourFillingProductMap A _ q).1.1 / _
    congr 1
    change ((orderFourRealPeriodProductHomeomorph A.periods
      (fourthPeriodFamilyTranslation A.periods t q.1)).1 : ℂ) =
      ((orderFourRealPeriodProductHomeomorph A.periods q.1).1 : ℂ)
    rw [orderFourRealPeriodProductHomeomorph_fst, orderFourRealPeriodProductHomeomorph_fst,
      fourthPeriodFamilyTranslation, familyTotalSpaceBase_familyTranslationMap]
  · exact orderFourRealPeriodProductHomeomorph_fourthTranslation A.periods t q.1

public theorem actualOrderThreeFourthTranslation_mk (A : AnalyticData) (t : ℝ)
    (q : A.orderThreeFillingOpen A.starSeparation.orderThree.radius) :
    A.actualOrderThreeFourthTranslation ((t : UnitAddCircle), Quotient.mk _ q) =
      Quotient.mk _ (A.orderThreeFourthTranslationSource t q) := by
  apply A.orderThreeFourthFillingHomeomorph.injective
  change A.orderThreeFourthFillingHomeomorph (A.orderThreeFourthFillingHomeomorph.symm _) = _
  rw [Homeomorph.apply_symm_apply]
  change orderThreeFourthCircleTranslation A.periods
    ((t : UnitAddCircle),
      (orderThreeSelectedAffineRadialCompatibility A).toVaryingFillingProductIdentification.quotientHomeomorph
        (Quotient.mk _ q)) =
    (orderThreeSelectedAffineRadialCompatibility A).toVaryingFillingProductIdentification.quotientHomeomorph
      (Quotient.mk _ (A.orderThreeFourthTranslationSource t q))
  rw [EquivariantRadialProductIdentification.quotientHomeomorph_mk,
    EquivariantRadialProductIdentification.quotientHomeomorph_mk,
    A.orderThreeFourthTranslationSource_chart]
  rfl

public theorem actualOrderFourFourthTranslation_mk (A : AnalyticData) (t : ℝ)
    (q : A.orderFourFillingOpen A.starSeparation.orderFour.radius) :
    A.actualOrderFourFourthTranslation ((t : UnitAddCircle), Quotient.mk _ q) =
      Quotient.mk _ (A.orderFourFourthTranslationSource t q) := by
  apply A.orderFourFourthFillingHomeomorph.injective
  change A.orderFourFourthFillingHomeomorph (A.orderFourFourthFillingHomeomorph.symm _) = _
  rw [Homeomorph.apply_symm_apply]
  change orderFourFourthCircleTranslation A.periods
    ((t : UnitAddCircle),
      (orderFourSelectedAffineRadialCompatibility A).toVaryingFillingProductIdentification.quotientHomeomorph
        (Quotient.mk _ q)) =
    (orderFourSelectedAffineRadialCompatibility A).toVaryingFillingProductIdentification.quotientHomeomorph
      (Quotient.mk _ (A.orderFourFourthTranslationSource t q))
  rw [EquivariantRadialProductIdentification.quotientHomeomorph_mk,
    EquivariantRadialProductIdentification.quotientHomeomorph_mk,
    A.orderFourFourthTranslationSource_chart]
  rfl

end SphereSixComplex.Geometry.AnalyticData
