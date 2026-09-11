module
public import SphereSixComplex.Paper.Topology.CuspFourthCircle
public import SphereSixComplex.Paper.Topology.EllipticInvariantCircleTranslation
import all SphereSixComplex.Paper.Periods.Matrix


@[expose] public section
noncomputable section
open scoped ContinuousMap
namespace SphereSixComplex.Topology.PaperEllipticFillingRadialRetraction
open SphereSixComplex.Geometry SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open ComplexTorus AnalyticTorusFamily EllipticFamilySpecialization EllipticFixedPointCriterion
open CuspRadialClutchingConstruction GlobalTorusFamily FamilyEquivariance

public def fourthPeriodCircle (x : PeriodDomain) : C(UnitAddCircle, AdditiveTorus x.1) :=
  (cuspFourthCircle x).comp ⟨fun z _ ↦ z, continuous_pi fun _ ↦ continuous_id⟩

public theorem fourthPeriodCircle_real (x : PeriodDomain) (t : ℝ) :
    fourthPeriodCircle x (t : UnitAddCircle) =
      additiveTorusProjection x.1 (t • periodVector x.1 ![0,0,0,1]) :=
  cuspFourthCircle_real x t

variable {U : TriangleUniformization} (F : PeriodFunctions U)

public theorem orderThreeFourthPeriodCircle_fixed (z : UnitAddCircle) :
    (orderThreeActionData F).automorphism (fourthPeriodCircle (parameterMap F U.zOne) z) =
      fourthPeriodCircle (parameterMap F U.zOne) z := by
  obtain ⟨t,rfl⟩ := QuotientAddGroup.mk_surjective z
  rw [fourthPeriodCircle_real]
  change orderThreeFiberAutomorphism F (Quotient.mk _ _) = Quotient.mk _ _
  rw [orderThreeFiberAutomorphism_mk]
  apply congrArg (Quotient.mk _)
  rw [periodTransport_gOne]
  change rightOneLinearEquiv _ (parameterMap F U.zOne).tau_ne_zero _ = _
  rw [rightOneLinearEquiv_apply]
  ext i
  fin_cases i <;> simp [periodVector, periodMatrix, rightOne, Matrix.vecHead, Matrix.vecTail]

public theorem orderFourFourthPeriodCircle_fixed (z : UnitAddCircle) :
    (orderFourActionData F).automorphism (fourthPeriodCircle (parameterMap F U.zTwo) z) =
      fourthPeriodCircle (parameterMap F U.zTwo) z := by
  obtain ⟨t,rfl⟩ := QuotientAddGroup.mk_surjective z
  rw [fourthPeriodCircle_real]
  change orderFourFiberAutomorphism F (Quotient.mk _ _) = Quotient.mk _ _
  rw [orderFourFiberAutomorphism_mk]
  apply congrArg (Quotient.mk _)
  rw [periodTransport_gTwo]
  change rightTwoLinearEquiv _ (parameterMap F U.zTwo).tau_ne_zero _ = _
  rw [rightTwoLinearEquiv_apply]
  ext i
  fin_cases i <;> simp [periodVector, periodMatrix, rightTwo, Matrix.vecHead, Matrix.vecTail]

public def orderThreeFourthCircleTranslation :
    C(UnitAddCircle × (orderThreeRadialActionData F).FillingQuotient,
      (orderThreeRadialActionData F).FillingQuotient) :=
  (orderThreeRadialActionData F).circleTranslate (fourthPeriodCircle (parameterMap F U.zOne))
    (orderThreeFourthPeriodCircle_fixed F)

public def orderFourFourthCircleTranslation :
    C(UnitAddCircle × (orderFourRadialActionData F).FillingQuotient,
      (orderFourRadialActionData F).FillingQuotient) :=
  (orderFourRadialActionData F).circleTranslate (fourthPeriodCircle (parameterMap F U.zTwo))
    (orderFourFourthPeriodCircle_fixed F)



end SphereSixComplex.Topology.PaperEllipticFillingRadialRetraction
