module
public import SphereSixComplex.Paper.Topology.ActualEllipticFourthCircleTranslation

@[expose] public section
noncomputable section
namespace SphereSixComplex.Geometry.EllipticVaryingFamilyQuotient
open SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open ComplexTorus TorusFamily AnalyticTorusFamily EllipticFamilySpecialization
open SphereSixComplex.StandardTorusHomology
open GlobalTorusFamily EllipticPuncturedCollarGaugeHomeomorph
open EllipticRealPeriodProductTrivialization
open SphereSixComplex.Topology.PaperEllipticFillingRadialRetraction
variable {U : TriangleUniformization} (F : PeriodFunctions U)

public def fourthPeriodFamilyTranslation (t : ℝ) :
    TotalSpace (parameterMap F) → TotalSpace (parameterMap F) :=
  familyTranslationMap F (fun z ↦ t • periodVector (parameterMap F z).1 ![0,0,0,1])

public theorem familyTranslationMap_commute
    (s v : UpperHalfPlane → ComplexTwoSpace) (q : TotalSpace (parameterMap F)) :
    familyTranslationMap F s (familyTranslationMap F v q) =
      familyTranslationMap F v (familyTranslationMap F s q) := by
  induction q using Quotient.inductionOn with
  | _ p =>
    simp only [familyTranslationMap_mk, familyTranslationCover.eq_def]
    rw [add_left_comm]

public theorem orderThreePrincipalGauge_fourthTranslation (t : ℝ)
    (q : TotalSpace (parameterMap F)) :
    orderThreePrincipalGaugeEquiv F (fourthPeriodFamilyTranslation F t q) =
      fourthPeriodFamilyTranslation F t (orderThreePrincipalGaugeEquiv F q) :=
  familyTranslationMap_commute F _ _ q

public theorem orderFourPrincipalGauge_fourthTranslation (t : ℝ)
    (q : TotalSpace (parameterMap F)) :
    orderFourPrincipalGaugeEquiv F (fourthPeriodFamilyTranslation F t q) =
      fourthPeriodFamilyTranslation F t (orderFourPrincipalGaugeEquiv F q) :=
  familyTranslationMap_commute F _ _ q

public theorem orderThreePrincipalGauge_symm_fourthTranslation (t : ℝ)
    (q : TotalSpace (parameterMap F)) :
    (orderThreePrincipalGaugeEquiv F).symm (fourthPeriodFamilyTranslation F t q) =
      fourthPeriodFamilyTranslation F t ((orderThreePrincipalGaugeEquiv F).symm q) :=
  familyTranslationMap_commute F _ _ q

public theorem orderFourPrincipalGauge_symm_fourthTranslation (t : ℝ)
    (q : TotalSpace (parameterMap F)) :
    (orderFourPrincipalGaugeEquiv F).symm (fourthPeriodFamilyTranslation F t q) =
      fourthPeriodFamilyTranslation F t ((orderFourPrincipalGaugeEquiv F).symm q) :=
  familyTranslationMap_commute F _ _ q

public theorem movingToFixedCover_fourthTranslation
    (b : UpperHalfPlane) (t : ℝ) (p : UpperHalfPlane × ComplexTwoSpace) :
    (movingToFixedCover F b
      (familyTranslationCover (fun z ↦ t • periodVector (parameterMap F z).1 ![0,0,0,1]) p)).2 =
      t • periodVector (parameterMap F b).1 ![0,0,0,1] +
        (movingToFixedCover F b p).2 := by
  change (fullRankDomain (parameterMap F b)).realEquiv
    ((fullRankDomain (parameterMap F p.1)).realEquiv.symm
      (t • periodVector (parameterMap F p.1).1 ![0,0,0,1] + p.2)) = _
  rw [map_add, map_smul, realEquiv_symm_periodVector, map_add, map_smul,
    (fullRankDomain _).map_integer]
  rfl

public theorem orderThreeRealPeriodProductHomeomorph_fourthTranslation (t : ℝ)
    (q : TotalSpace (parameterMap F)) :
    (orderThreeRealPeriodProductHomeomorph F (fourthPeriodFamilyTranslation F t q)).2 =
      fourthPeriodCircle (parameterMap F U.zOne) (t : UnitAddCircle) +
        (orderThreeRealPeriodProductHomeomorph F q).2 := by
  induction q using Quotient.inductionOn with
  | _ p =>
    change (orderThreeRealPeriodProductHomeomorph F (familyTranslationMap F _ (Quotient.mk _ p))).2 = _
    rw [familyTranslationMap_mk, orderThreeRealPeriodProductHomeomorph_mk,
      orderThreeRealPeriodProductHomeomorph_mk, movingToFixedCover_fourthTranslation,
      fourthPeriodCircle_real]
    exact additiveTorus_mk_add _ _ _

public theorem orderFourRealPeriodProductHomeomorph_fourthTranslation (t : ℝ)
    (q : TotalSpace (parameterMap F)) :
    (orderFourRealPeriodProductHomeomorph F (fourthPeriodFamilyTranslation F t q)).2 =
      fourthPeriodCircle (parameterMap F U.zTwo) (t : UnitAddCircle) +
        (orderFourRealPeriodProductHomeomorph F q).2 := by
  induction q using Quotient.inductionOn with
  | _ p =>
    change (orderFourRealPeriodProductHomeomorph F (familyTranslationMap F _ (Quotient.mk _ p))).2 = _
    rw [familyTranslationMap_mk, orderFourRealPeriodProductHomeomorph_mk,
      orderFourRealPeriodProductHomeomorph_mk, movingToFixedCover_fourthTranslation,
      fourthPeriodCircle_real]
    exact additiveTorus_mk_add _ _ _

end SphereSixComplex.Geometry.EllipticVaryingFamilyQuotient

